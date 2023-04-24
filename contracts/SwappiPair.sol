// SPDX-License-Identifier: MIT
pragma solidity =0.5.16;
pragma experimental ABIEncoderV2;
import "./interfaces/ISwappiPair.sol";
import "./SwappiERC20.sol";
import "./libraries/Math.sol";
import "./libraries/UQ112x112.sol";
import "./interfaces/IERC20.sol";
import "./interfaces/ISwappiFactory.sol";
import "./interfaces/ISwappiCallee.sol";
import "./WeightedMath.sol";
import "./external-fees/InvariantGrowthProtocolSwapFees.sol";
contract SwappiPairWeighted is ISwappiPair, SwappiERC20 {
    using SafeMath for uint256;
    using UQ112x112 for uint224;

    uint256 public constant MINIMUM_LIQUIDITY = 10**3;
    bytes4 private constant SELECTOR =
        bytes4(keccak256(bytes("transfer(address,uint256)")));

    address public factory;
    address public token0;
    address public token1;

    uint112 private reserve0; // uses single storage slot, accessible via getReserves
    uint112 private reserve1; // uses single storage slot, accessible via getReserves
    uint32 private blockTimestampLast; // uses single storage slot, accessible via getReserves

    uint256 public price0CumulativeLast;
    uint256 public price1CumulativeLast;
    uint256 public kLast; // reserve0 * reserve1, as of immediately after the most recent liquidity event

    uint256 private unlocked = 1;

    // #############Weighted###########
    // 1e18 corresponds to 1.0, or a 100% fee
    uint256 public swapFeePercentage = 3e10; // 0.03%
    uint256 public protocolSwapFeePercentage = 1e10; //0.01%
    // All token balances are normalized to behave as if the token had 18 decimals. We assume a token's decimals will
    // not change throughout its lifetime, and store the corresponding scaling factor for each at construction time.
    // These factors are always greater than or equal to one: tokens with more than 18 decimals are not supported.

    uint256 public _scalingFactor0;
    uint256 public _scalingFactor1;

    uint256 public _normalizedWeight0;
    uint256 public _normalizedWeight1;

    uint256 public postJoinExitInvariant; // use this instead of kLast
    struct SwapRequest {
        bool isGivenIn;
        IERC20 tokenIn;
        IERC20 tokenOut;
        uint256 amount;
        bytes userData;
    }
    // #############Weighted###########
    modifier lock() {
        require(unlocked == 1, "Swappi: LOCKED");
        unlocked = 0;
        _;
        unlocked = 1;
    }

    function getReserves()
        public
        view
        returns (
            uint112 _reserve0,
            uint112 _reserve1,
            uint32 _blockTimestampLast
        )
    {
        _reserve0 = reserve0;
        _reserve1 = reserve1;
        _blockTimestampLast = blockTimestampLast;
    }

    function _safeTransfer(
        address token,
        address to,
        uint256 value
    ) private {
        (bool success, bytes memory data) =
            token.call(abi.encodeWithSelector(SELECTOR, to, value));
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "Swappi: TRANSFER_FAILED"
        );
    }

    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
    event Burn(
        address indexed sender,
        uint256 amount0,
        uint256 amount1,
        address indexed to
    );
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    constructor() public {
        factory = msg.sender;
    }

    // called once by the factory at time of deployment
    function initialize(address _token0, address _token1, uint256[2] calldata normalizedWeights) external {
        require(msg.sender == factory, "Swappi: FORBIDDEN"); // sufficient check
        // Ensure each normalized weight is above the minimum
        uint256 normalizedSum = 0;
        for (uint8 i = 0; i < 2; i++) {
            uint256 normalizedWeight = normalizedWeights[i];

            require(normalizedWeight >= 0.01e18, "Errors.MIN_WEIGHT");
            normalizedSum = normalizedSum.add(normalizedWeight);
        }
        // Ensure that the normalized weights sum to ONE
        require(normalizedSum == FixedPoint.getONE(), "Errors.NORMALIZED_WEIGHT_INVARIANT");

        token0 = _token0;
        token1 = _token1;
        _scalingFactor0 = _computeScalingFactor(IERC20(_token0));
        _scalingFactor1 = _computeScalingFactor(IERC20(_token1));
        _normalizedWeight0 = normalizedWeights[0];
        _normalizedWeight1 = normalizedWeights[1];
    }
    
    // Scaling

    /**
     * @dev Returns a scaling factor that, when multiplied to a token amount for `token`, normalizes its balance as if
     * it had 18 decimals.
     */
    function _computeScalingFactor(IERC20 token) internal view returns (uint256) {
        if (address(token) == address(this)) {
            return FixedPoint.getONE();
        }

        // Tokens that don't implement the `decimals` method are not supported.
        uint256 tokenDecimals = IERC20(address(token)).decimals();

        // Tokens with more than 18 decimals are not supported.
        uint256 decimalsDifference = Math.sub(18, tokenDecimals);
        return FixedPoint.getONE() * 10**decimalsDifference;
    }
    // Array

    /**
    * @dev Same as `_upscale`, but for an entire array. This function does not return anything, but instead *mutates*
    * the `amounts` array.
    */
    function _upscaleArray(uint256[] memory amounts, uint256[] memory scalingFactors) internal pure {
        uint256 length = amounts.length;
        // InputHelpers.ensureInputLengthMatch(length, scalingFactors.length);

        for (uint256 i = 0; i < length; ++i) {
            amounts[i] = FixedPoint.mulDown(amounts[i], scalingFactors[i]);
        }
    }
    /**
    * @dev Same as `_downscaleDown`, but for an entire array. This function does not return anything, but instead
    * *mutates* the `amounts` array.
    */
    function _downscaleDownArray(uint256[] memory amounts, uint256[] memory scalingFactors) internal pure {
        uint256 length = amounts.length;
        // InputHelpers.ensureInputLengthMatch(length, scalingFactors.length);

        for (uint256 i = 0; i < length; ++i) {
            amounts[i] = FixedPoint.divDown(amounts[i], scalingFactors[i]);
        }
    }
    /**
    * @dev Same as `_downscaleUp`, but for an entire array. This function does not return anything, but instead
    * *mutates* the `amounts` array.
    */
    function _downscaleUpArray(uint256[] memory amounts, uint256[] memory scalingFactors) internal pure {
        uint256 length = amounts.length;
        // InputHelpers.ensureInputLengthMatch(length, scalingFactors.length);

        for (uint256 i = 0; i < length; ++i) {
            amounts[i] = FixedPoint.divUp(amounts[i], scalingFactors[i]);
        }
    }
    function _getNormalizedWeights() internal view returns (uint256[] memory) {
        // uint256 totalTokens = _getTotalTokens();
        uint256[] memory normalizedWeights = new uint256[](2);

        // prettier-ignore
        {
            normalizedWeights[0] = _normalizedWeight0;
            normalizedWeights[1] = _normalizedWeight1;
        }

        return normalizedWeights;
    }
    function _scalingFactors() internal view returns (uint256[] memory) {
        // uint256 totalTokens = _getTotalTokens();
        uint256[] memory scalingFactors = new uint256[](2);

        // prettier-ignore
        {
            scalingFactors[0] = _scalingFactor0;
            scalingFactors[1] = _scalingFactor1;
        }

        return scalingFactors;
    }
    /**
     * @dev Called when the Pool is joined for the first time; that is, when the BPT total supply is zero.
     *
     * Returns the amount of BPT to mint, and the token amounts the Pool will receive in return.
     *
     * Minted BPT will be sent to `recipient`, except for _getMinimumBpt(), which will be deducted from this amount and
     * sent to the zero address instead. This will cause that BPT to remain forever locked there, preventing total BTP
     * from ever dropping below that value, and ensuring `_onInitializePool` can only be called once in the entire
     * Pool's lifetime.
     *
     * The tokens granted to the Pool will be transferred from `sender`. These amounts are considered upscaled and will
     * be downscaled (rounding up) before being returned to the Vault.
     */
    function _onInitializePool(
        uint256[] memory scalingFactors,
        uint256[] memory amountsIn
    ) internal returns (uint256, uint256[] memory) {
        // WeightedPoolUserData.JoinKind kind = userData.joinKind();
        // _require(kind == WeightedPoolUserData.JoinKind.INIT, Errors.UNINITIALIZED);

        // uint256[] memory amountsIn = userData.initialAmountsIn();
        // InputHelpers.ensureInputLengthMatch(amountsIn.length, scalingFactors.length);
        _upscaleArray(amountsIn, scalingFactors);

        uint256[] memory normalizedWeights = _getNormalizedWeights();
        uint256 invariantAfterJoin = WeightedMath._calculateInvariant(normalizedWeights, amountsIn);

        // Set the initial BPT to the value of the invariant times the number of tokens. This makes BPT supply more
        // consistent in Pools with similar compositions but different number of tokens.
        uint256 bptAmountOut = Math.mul(invariantAfterJoin, amountsIn.length);

        // Initialization is still a join, so we need to do post-join work. Since we are not paying protocol fees,
        // and all we need to do is update the invariant, call `_updatePostJoinExit` here instead of `_afterJoinExit`.
        // _updatePostJoinExit(invariantAfterJoin);
        postJoinExitInvariant = invariantAfterJoin;

        return (bptAmountOut, amountsIn);
    }
    /**
     * @dev Called before any join or exit operation. Returns the Pool's total supply by default, but derived contracts
     * may choose to add custom behavior at these steps. This often has to do with protocol fee processing.
     */
    function _beforeJoinExit(uint256[] memory preBalances, uint256[] memory normalizedWeights)
        internal view
        returns (uint256, uint256)
    {
        return (totalSupply, WeightedMath._calculateInvariant(normalizedWeights, preBalances));
    }
    function _joinExactTokensInForBPTOut(
        uint256[] memory balances,
        uint256[] memory normalizedWeights,
        uint256[] memory scalingFactors,
        uint256 iTotalSupply,
        uint256[] memory amountsIn, uint256 minBPTAmountOut
    ) private view returns (uint256, uint256[] memory) {
        // (uint256[] memory amountsIn, uint256 minBPTAmountOut) = userData.exactTokensInForBptOut();
        // InputHelpers.ensureInputLengthMatch(balances.length, amountsIn.length);

        _upscaleArray(amountsIn, scalingFactors);

        uint256 bptAmountOut = WeightedMath._calcBptOutGivenExactTokensIn(
            balances,
            normalizedWeights,
            amountsIn,
            iTotalSupply,
            swapFeePercentage
        );

        require(bptAmountOut >= minBPTAmountOut, "Errors.BPT_OUT_MIN_AMOUNT");

        return (bptAmountOut, amountsIn);
    }

    function _joinTokenInForExactBPTOut(
        uint256[] memory balances,
        uint256[] memory normalizedWeights,
        uint256 iTotalSupply,
        uint256 bptAmountOut, uint256 tokenIndex
    ) private view returns (uint256, uint256[] memory) {
        // (uint256 bptAmountOut, uint256 tokenIndex) = userData.tokenInForExactBptOut();
        // Note that there is no maximum amountIn parameter: this is handled by `IVault.joinPool`.

        require(tokenIndex < balances.length, "Errors.OUT_OF_BOUNDS");

        uint256 amountIn = WeightedMath._calcTokenInGivenExactBptOut(
            balances[tokenIndex],
            normalizedWeights[tokenIndex],
            bptAmountOut,
            iTotalSupply,
            swapFeePercentage
        );

        // We join in a single token, so we initialize amountsIn with zeros
        uint256[] memory amountsIn = new uint256[](balances.length);
        // And then assign the result to the selected token
        amountsIn[tokenIndex] = amountIn;

        return (bptAmountOut, amountsIn);
    }

    function _joinAllTokensInForExactBPTOut(
        uint256[] memory balances,
        uint256 iTotalSupply,
        uint256 bptAmountOut
    ) private pure returns (uint256, uint256[] memory) {
        // uint256 bptAmountOut = userData.allTokensInForExactBptOut();
        // Note that there is no maximum amountsIn parameter: this is handled by `IVault.joinPool`.

        uint256[] memory amountsIn = WeightedMath.computeProportionalAmountsIn(balances, iTotalSupply, bptAmountOut);

        return (bptAmountOut, amountsIn);
    }
    /**
     * @dev Returns the amount of BPT to be minted to pay protocol fees on swap fees accrued during a join/exit.
     * Note that this isn't a view function. This function automatically updates `_lastPostJoinExitInvariant` to
     * ensure that proper accounting is performed to prevent charging duplicate protocol fees.
     * @param preJoinExitInvariant - The Pool's invariant prior to the join/exit.
     * @param preBalances - The Pool's balances prior to the join/exit.
     * @param balanceDeltas - The changes to the Pool's balances due to the join/exit.
     * @param normalizedWeights - The Pool's normalized token weights.
     * @param preJoinExitSupply - The Pool's total supply prior to the join/exit *after* minting protocol fees.
     * @param postJoinExitSupply - The Pool's total supply after the join/exit.
     */
    function _getPostJoinExitProtocolFees(
        uint256 preJoinExitInvariant,
        uint256[] memory preBalances,
        uint256[] memory balanceDeltas,
        uint256[] memory normalizedWeights,
        uint256 preJoinExitSupply,
        uint256 postJoinExitSupply
    ) internal returns (uint256) {
        bool isJoin = postJoinExitSupply >= preJoinExitSupply;

        // Compute the post balances by adding or removing the deltas.
        for (uint256 i = 0; i < preBalances.length; ++i) {
            preBalances[i] = isJoin
                ? SafeMath.add(preBalances[i], balanceDeltas[i])
                : SafeMath.sub(preBalances[i], balanceDeltas[i]);
        }

        // preBalances have now been mutated to reflect the postJoinExit balances.
        uint256 prePostJoinExitInvariant = WeightedMath._calculateInvariant(normalizedWeights, preBalances);
        // uint256 protocolSwapFeePercentage = getProtocolFeePercentageCache(ProtocolFeeType.SWAP);

        // _updatePostJoinExit(prepostJoinExitInvariant);
        postJoinExitInvariant = prePostJoinExitInvariant;
        // We return immediately if the fee percentage is zero to avoid unnecessary computation.
        if (protocolSwapFeePercentage == 0) return 0;

        uint256 protocolFeeAmount = InvariantGrowthProtocolSwapFees.calcDueProtocolFees(
            FixedPoint.divDown(prePostJoinExitInvariant, preJoinExitInvariant),
            preJoinExitSupply,
            postJoinExitSupply,
            protocolSwapFeePercentage
        );

        return protocolFeeAmount;
    }
    // if fee is on, mint liquidity equivalent to 8/25 of the growth in sqrt(k)
    function _payProtocolFees(uint256 liquidity)
        private
        returns (bool feeOn)
    {
        address feeTo = ISwappiFactory(factory).feeTo();
        feeOn = feeTo != address(0);
        if (feeOn) {
            if (liquidity > 0) _mint(feeTo, liquidity);
        }
    }
    function _afterJoinExit(
        uint256 preJoinExitInvariant,
        uint256[] memory preBalances,
        uint256[] memory balanceDeltas,
        uint256[] memory normalizedWeights,
        uint256 preJoinExitSupply,
        uint256 postJoinExitSupply
    ) internal {
        uint256 protocolFeesToBeMinted = _getPostJoinExitProtocolFees(
            preJoinExitInvariant,
            preBalances,
            balanceDeltas,
            normalizedWeights,
            preJoinExitSupply,
            postJoinExitSupply
        );

        _payProtocolFees(protocolFeesToBeMinted);
    }
    /**
     * @dev Dispatch code which decodes the provided userdata to perform the specified join type.
     * Inheriting contracts may override this function to add additional join types or extra conditions to allow
     * or disallow joins under certain circumstances.
     */
    function _doJoin(
        uint256[] memory balances,
        uint256[] memory normalizedWeights,
        uint256[] memory scalingFactors,
        uint256 iTotalSupply,
        uint256[] memory userAmountsInOrIndex,
        uint256 bptMinOrExact
    ) internal view returns (uint256, uint256[] memory) {
        if (bptMinOrExact == 0) {
            return _joinExactTokensInForBPTOut(balances, normalizedWeights, scalingFactors, iTotalSupply, userAmountsInOrIndex, bptMinOrExact);
        }else{
            return _joinTokenInForExactBPTOut(balances, normalizedWeights, iTotalSupply, bptMinOrExact, userAmountsInOrIndex[0]);
        }
        // WeightedPoolUserData.JoinKind kind = userData.joinKind();

        // if (kind == WeightedPoolUserData.JoinKind.EXACT_TOKENS_IN_FOR_BPT_OUT) {
        //     return _joinExactTokensInForBPTOut(balances, normalizedWeights, scalingFactors, totalSupply, userData);
        // } else if (kind == WeightedPoolUserData.JoinKind.TOKEN_IN_FOR_EXACT_BPT_OUT) {
        //     return _joinTokenInForExactBPTOut(balances, normalizedWeights, totalSupply, userData);
        // } else if (kind == WeightedPoolUserData.JoinKind.ALL_TOKENS_IN_FOR_EXACT_BPT_OUT) {
        //     return _joinAllTokensInForExactBPTOut(balances, totalSupply, userData);
        // } else {
        //     _revert(Errors.UNHANDLED_JOIN_KIND);
        // }
    }
    function _onJoinPool(
        uint256[] memory balances,
        uint256[] memory scalingFactors,
        uint256[] memory userAmountsIn,
        uint256 bptAmountMinOrExact
    ) internal returns (uint256, uint256[] memory) {
        uint256[] memory normalizedWeights = _getNormalizedWeights();

        (uint256 preJoinExitSupply, uint256 preJoinExitInvariant) = _beforeJoinExit(balances, normalizedWeights);

        (uint256 bptAmountOut, uint256[] memory amountsIn) = _doJoin(
            balances,
            normalizedWeights,
            scalingFactors,
            preJoinExitSupply,
            userAmountsIn,
            bptAmountMinOrExact
        );

        _afterJoinExit(
            preJoinExitInvariant,
            balances,
            amountsIn,
            normalizedWeights,
            preJoinExitSupply,
            preJoinExitSupply.add(bptAmountOut)
        );

        return (bptAmountOut, amountsIn);
    }
    /**
     * @notice Vault hook for adding liquidity to a pool (including the first time, "initializing" the pool).
     * @dev This function can only be called from the Vault, from `joinPool`.
     */
    function onJoinPool(
        address recipient,
        uint256[] calldata balances,
        uint256[] calldata userAmountsIn,
        uint256 bptMinOrExact
    ) external lock returns (uint256[] memory, uint256[] memory) {
        // _beforeSwapJoinExit();

        uint256[] memory scalingFactors = _scalingFactors();
        uint256 _totalSupply = totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
        if (_totalSupply == 0) {
            (uint256 bptAmountOut, uint256[] memory amountsIn) = _onInitializePool(
                scalingFactors,
                userAmountsIn
            );

            // On initialization, we lock _getMinimumBpt() by minting it for the zero address. This BPT acts as a
            // minimum as it will never be burned, which reduces potential issues with rounding, and also prevents the
            // Pool from ever being fully drained.
            require(bptAmountOut >= MINIMUM_LIQUIDITY, "Errors.MINIMUM_BPT");
            _mint(address(0), MINIMUM_LIQUIDITY);
            _mint(recipient, bptAmountOut - MINIMUM_LIQUIDITY);

            // amountsIn are amounts entering the Pool, so we round up.
            _downscaleUpArray(amountsIn, scalingFactors);

            return (amountsIn, new uint256[](balances.length));
        } else {
            _upscaleArray(balances, scalingFactors);
            (uint256 bptAmountOut, uint256[] memory amountsIn) = _onJoinPool(
                balances,
                scalingFactors,
                userAmountsIn,
                bptMinOrExact
            );

            // Note we no longer use `balances` after calling `_onJoinPool`, which may mutate it.

            _mint(recipient, bptAmountOut);

            // amountsIn are amounts entering the Pool, so we round up.
            _downscaleUpArray(amountsIn, scalingFactors);

            // This Pool ignores the `dueProtocolFees` return value, so we simply return a zeroed-out array.
            return (amountsIn, new uint256[](balances.length));
        }
    }
    // update reserves and, on the first call per block, price accumulators
    function _update(
        uint256 balance0,
        uint256 balance1,
        uint112 _reserve0,
        uint112 _reserve1
    ) private {
        require(
            balance0 <= uint112(-1) && balance1 <= uint112(-1),
            "Swappi: OVERFLOW"
        );
        uint32 blockTimestamp = uint32(block.timestamp % 2**32);
        uint32 timeElapsed = blockTimestamp - blockTimestampLast; // overflow is desired
        if (timeElapsed > 0 && _reserve0 != 0 && _reserve1 != 0) {
            // * never overflows, and + overflow is desired
            price0CumulativeLast +=
                uint256(UQ112x112.encode(_reserve1).uqdiv(_reserve0)) *
                timeElapsed;
            price1CumulativeLast +=
                uint256(UQ112x112.encode(_reserve0).uqdiv(_reserve1)) *
                timeElapsed;
        }
        reserve0 = uint112(balance0);
        reserve1 = uint112(balance1);
        blockTimestampLast = blockTimestamp;
        emit Sync(reserve0, reserve1);
    }
    // formula of k
    function _k(uint256 x, uint256 y) internal pure returns (uint) {
        uint _a = x.mul(y).div(1e18);
        uint _b = x.mul(x).div(1e18).add(y.mul(y).div(1e18));
        return _a.mul(_b).div(1e18);  // x3y+y3x >= k
    }

    // // if fee is on, mint liquidity equivalent to 8/25 of the growth in sqrt(k)
    // function _mintFee(uint112 _reserve0, uint112 _reserve1)
    //     private
    //     returns (bool feeOn)
    // {
    //     address feeTo = ISwappiFactory(factory).feeTo();
    //     feeOn = feeTo != address(0);
    //     uint256 _kLast = kLast; // gas savings
    //     if (feeOn) {
    //         if (_kLast != 0) {
    //             uint256 rootK = Math.sqrt(uint256(_reserve0).mul(_reserve1));
    //             uint256 rootKLast = Math.sqrt(_kLast);
    //             if (rootK > rootKLast) {
    //                 uint256 numerator =
    //                     totalSupply.mul(rootK.sub(rootKLast)).mul(8);
    //                 uint256 denominator = rootK.mul(17).add(rootKLast.mul(8));
    //                 uint256 liquidity = numerator / denominator;
    //                 if (liquidity > 0) _mint(feeTo, liquidity);
    //             }
    //         }
    //     } else if (_kLast != 0) {
    //         kLast = 0;
    //     }
    // }

    // ###################V2 mint is deleted####################
    // // this low-level function should be called from a contract which performs important safety checks
    // function mint(address to) external lock returns (uint256 liquidity) {
    //     (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
    //     uint256 balance0 = IERC20(token0).balanceOf(address(this));
    //     uint256 balance1 = IERC20(token1).balanceOf(address(this));
    //     uint256 amount0 = balance0.sub(_reserve0);
    //     uint256 amount1 = balance1.sub(_reserve1);

    //     bool feeOn = _mintFee(_reserve0, _reserve1);
    //     uint256 _totalSupply = totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
    //     if (_totalSupply == 0) {
    //         liquidity = Math.sqrt(amount0.mul(amount1)).sub(MINIMUM_LIQUIDITY);
    //         _mint(address(0), MINIMUM_LIQUIDITY); // permanently lock the first MINIMUM_LIQUIDITY tokens
    //     } else {
    //         liquidity = Math.min(
    //             amount0.mul(_totalSupply) / _reserve0,
    //             amount1.mul(_totalSupply) / _reserve1
    //         );
    //     }
    //     require(liquidity > 0, "Swappi: INSUFFICIENT_LIQUIDITY_MINTED");
    //     _mint(to, liquidity);

    //     _update(balance0, balance1, _reserve0, _reserve1);
    //     if (feeOn) kLast = _k(uint256(reserve0), uint256(reserve1)); // reserve0 and reserve1 are up-to-date
    //     emit Mint(msg.sender, amount0, amount1);
    // }
    /**
     * @dev Dispatch code which decodes the provided userdata to perform the specified exit type.
     * Inheriting contracts may override this function to add additional exit types or extra conditions to allow
     * or disallow exit under certain circumstances.
     */
    function _doExit(
        uint256[] memory balances,
        uint256[] memory normalizedWeights,
        uint256 iTotalSupply,
        uint256 bptAmountIn,
        uint256 tokenIndex
    ) internal view returns (uint256, uint256[] memory) {
        if (tokenIndex == 2) {
             return _exitExactBPTInForTokensOut(balances, iTotalSupply, bptAmountIn);
        }else{
            return _exitExactBPTInForTokenOut(balances, normalizedWeights, iTotalSupply, bptAmountIn, tokenIndex);
        }
        // WeightedPoolUserData.ExitKind kind = userData.exitKind();

        // if (kind == WeightedPoolUserData.ExitKind.EXACT_BPT_IN_FOR_ONE_TOKEN_OUT) {
        //     return _exitExactBPTInForTokenOut(balances, normalizedWeights, totalSupply, userData);
        // } else if (kind == WeightedPoolUserData.ExitKind.EXACT_BPT_IN_FOR_TOKENS_OUT) {
        //     return _exitExactBPTInForTokensOut(balances, totalSupply, userData);
        // } else if (kind == WeightedPoolUserData.ExitKind.BPT_IN_FOR_EXACT_TOKENS_OUT) {
        //     return _exitBPTInForExactTokensOut(balances, normalizedWeights, scalingFactors, totalSupply, userData);
        // } else {
        //     _revert(Errors.UNHANDLED_EXIT_KIND);
        // }
    }

    function _exitExactBPTInForTokenOut(
        uint256[] memory balances,
        uint256[] memory normalizedWeights,
        uint256 iTotalSupply,
        uint256 bptAmountIn, uint256 tokenIndex
    ) private view returns (uint256, uint256[] memory) {
        // (uint256 bptAmountIn, uint256 tokenIndex) = userData.exactBptInForTokenOut();
        // Note that there is no minimum amountOut parameter: this is handled by `IVault.exitPool`.

        require(tokenIndex < balances.length, "Errors.OUT_OF_BOUNDS");

        uint256 amountOut = WeightedMath._calcTokenOutGivenExactBptIn(
            balances[tokenIndex],
            normalizedWeights[tokenIndex],
            bptAmountIn,
            iTotalSupply,
            protocolSwapFeePercentage
        );

        // This is an exceptional situation in which the fee is charged on a token out instead of a token in.
        // We exit in a single token, so we initialize amountsOut with zeros
        uint256[] memory amountsOut = new uint256[](balances.length);
        // And then assign the result to the selected token
        amountsOut[tokenIndex] = amountOut;

        return (bptAmountIn, amountsOut);
    }

    function _exitExactBPTInForTokensOut(
        uint256[] memory balances,
        uint256 iTotalSupply,
        uint256 bptAmountIn
    ) private pure returns (uint256, uint256[] memory) {
        // uint256 bptAmountIn = userData.exactBptInForTokensOut();
        // Note that there is no minimum amountOut parameter: this is handled by `IVault.exitPool`.

        uint256[] memory amountsOut = WeightedMath.computeProportionalAmountsOut(balances, iTotalSupply, bptAmountIn);
        return (bptAmountIn, amountsOut);
    }

    function _exitBPTInForExactTokensOut(
        uint256[] memory balances,
        uint256[] memory normalizedWeights,
        uint256[] memory scalingFactors,
        uint256 iTotalSupply,
        uint256[] memory amountsOut, uint256 maxBPTAmountIn
    ) private view returns (uint256, uint256[] memory) {
        // (uint256[] memory amountsOut, uint256 maxBPTAmountIn) = userData.bptInForExactTokensOut();
        // InputHelpers.ensureInputLengthMatch(amountsOut.length, balances.length);
        _upscaleArray(amountsOut, scalingFactors);

        // This is an exceptional situation in which the fee is charged on a token out instead of a token in.
        uint256 bptAmountIn = WeightedMath._calcBptInGivenExactTokensOut(
            balances,
            normalizedWeights,
            amountsOut,
            iTotalSupply,
            protocolSwapFeePercentage
        );
        require(bptAmountIn <= maxBPTAmountIn, "Errors.BPT_IN_MAX_AMOUNT");

        return (bptAmountIn, amountsOut);
    }
    function _onExitPool(
        uint256[] memory balances,
        uint256[] memory scalingFactors,
        uint256 bptAmountIn,
        uint256 tokenIndex
    ) internal returns (uint256, uint256[] memory) {
        uint256[] memory normalizedWeights = _getNormalizedWeights();

        (uint256 preJoinExitSupply, uint256 preJoinExitInvariant) = _beforeJoinExit(balances, normalizedWeights);

        (uint256 bptAmountIn, uint256[] memory amountsOut) = _doExit(
            balances,
            normalizedWeights,
            preJoinExitSupply,
            bptAmountIn,
            tokenIndex
        );

        _afterJoinExit(
            preJoinExitInvariant,
            balances,
            amountsOut,
            normalizedWeights,
            preJoinExitSupply,
            preJoinExitSupply.sub(bptAmountIn)
        );

        return (bptAmountIn, amountsOut);
    }
    /**
     * @notice Vault hook for removing liquidity from a pool.
     * @dev This function can only be called from the Vault, from `exitPool`.
     */
    function onExitPool(
        address sender,
        uint256[] calldata balances,
        uint256 bptAmountInExact,
        uint256 tokenIndex
    ) external lock returns (uint256[] memory, uint256[] memory) {
        uint256[] memory amountsOut;
        uint256 bptAmountIn;

        uint256[] memory scalingFactors = _scalingFactors();
        _upscaleArray(balances, scalingFactors);

        (bptAmountIn, amountsOut) = _onExitPool(
            balances,
            scalingFactors,
            bptAmountInExact,
            tokenIndex
        );

        // amountsOut are amounts exiting the Pool, so we round down.
        _downscaleDownArray(amountsOut, scalingFactors);
        // Note we no longer use `balances` after calling `_onExitPool`, which may mutate it.

        _burn(sender, bptAmountIn);

        // This Pool ignores the `dueProtocolFees` return value, so we simply return a zeroed-out array.
        return (amountsOut, new uint256[](balances.length));
    }
    // // this low-level function should be called from a contract which performs important safety checks
    // function burn(address to)
    //     external
    //     lock
    //     returns (uint256 amount0, uint256 amount1)
    // {
    //     (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
    //     address _token0 = token0; // gas savings
    //     address _token1 = token1; // gas savings
    //     uint256 balance0 = IERC20(_token0).balanceOf(address(this));
    //     uint256 balance1 = IERC20(_token1).balanceOf(address(this));
    //     uint256 liquidity = balanceOf[address(this)];

    //     bool feeOn = _mintFee(_reserve0, _reserve1);
    //     uint256 _totalSupply = totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
    //     amount0 = liquidity.mul(balance0) / _totalSupply; // using balances ensures pro-rata distribution
    //     amount1 = liquidity.mul(balance1) / _totalSupply; // using balances ensures pro-rata distribution
    //     require(
    //         amount0 > 0 && amount1 > 0,
    //         "Swappi: INSUFFICIENT_LIQUIDITY_BURNED"
    //     );
    //     _burn(address(this), liquidity);
    //     _safeTransfer(_token0, to, amount0);
    //     _safeTransfer(_token1, to, amount1);
    //     balance0 = IERC20(_token0).balanceOf(address(this));
    //     balance1 = IERC20(_token1).balanceOf(address(this));

    //     _update(balance0, balance1, _reserve0, _reserve1);
    //     if (feeOn) kLast = uint256(reserve0).mul(reserve1); // reserve0 and reserve1 are up-to-date
    //     emit Burn(msg.sender, amount0, amount1, to);
    // }

    /**
     * @dev Adds swap fee amount to `amount`, returning a higher value.
     */
    function _addSwapFeeAmount(uint256 amount) internal view returns (uint256) {
        // This returns amount + fee amount, so we round up (favoring a higher fee amount).
        return FixedPoint.divUp(amount, FixedPoint.complement(swapFeePercentage));
    }
    /**
     * @dev Subtracts swap fee amount from `amount`, returning a lower value.
     */
    function _subtractSwapFeeAmount(uint256 amount) internal view returns (uint256) {
        // This returns amount - fee amount, so we round up (favoring a higher fee amount).
        uint256 feeAmount = FixedPoint.mulUp(amount, swapFeePercentage);
        return amount.sub(feeAmount);
    }
    // Single Value

    /**
    * @dev Applies `scalingFactor` to `amount`, resulting in a larger or equal value depending on whether it needed
    * scaling or not.
    */
    function _upscale(uint256 amount, uint256 scalingFactor) internal pure returns (uint256) {
        // Upscale rounding wouldn't necessarily always go in the same direction: in a swap for example the balance of
        // token in should be rounded up, and that of token out rounded down. This is the only place where we round in
        // the same direction for all amounts, as the impact of this rounding is expected to be minimal.
        return FixedPoint.mulDown(amount, scalingFactor);
    }

    /**
    * @dev Reverses the `scalingFactor` applied to `amount`, resulting in a smaller or equal value depending on
    * whether it needed scaling or not. The result is rounded down.
    */
    function _downscaleDown(uint256 amount, uint256 scalingFactor) internal pure returns (uint256) {
        return FixedPoint.divDown(amount, scalingFactor);
    }

    /**
    * @dev Reverses the `scalingFactor` applied to `amount`, resulting in a smaller or equal value depending on
    * whether it needed scaling or not. The result is rounded up.
    */
    function _downscaleUp(uint256 amount, uint256 scalingFactor) internal pure returns (uint256) {
        return FixedPoint.divUp(amount, scalingFactor);
    }
    function _getNormalizedWeight(IERC20 token) internal view returns (uint256) {
        // prettier-ignore
        if (address(token) == token0) { return _normalizedWeight0; }
        else { return _normalizedWeight1; }
    }
    /**
     * @dev Returns the scaling factor for one of the Pool's tokens. Reverts if `token` is not a token registered by the
     * Pool.
     */
    function _scalingFactor(IERC20 token) internal view returns (uint256) {
        // prettier-ignore
        if (address(token) == token0) { return _scalingFactor0; }
        else { return _scalingFactor1; }
    }
    // Base Pool handlers

    // Swap

    function _onSwapGivenIn(
        SwapRequest memory swapRequest,
        uint256 currentBalanceTokenIn,
        uint256 currentBalanceTokenOut
    ) internal view returns (uint256) {
        return
            WeightedMath._calcOutGivenIn(
                currentBalanceTokenIn,
                _getNormalizedWeight(swapRequest.tokenIn),
                currentBalanceTokenOut,
                _getNormalizedWeight(swapRequest.tokenOut),
                swapRequest.amount
            );
    }

    function _onSwapGivenOut(
        SwapRequest memory swapRequest,
        uint256 currentBalanceTokenIn,
        uint256 currentBalanceTokenOut
    ) internal view returns (uint256) {
        return
            WeightedMath._calcInGivenOut(
                currentBalanceTokenIn,
                _getNormalizedWeight(swapRequest.tokenIn),
                currentBalanceTokenOut,
                _getNormalizedWeight(swapRequest.tokenOut),
                swapRequest.amount
            );
    }    
    // Swap Hooks

    function onSwap(
        SwapRequest memory request,
        uint256 balanceTokenIn,
        uint256 balanceTokenOut
    ) public returns (uint256) {
        // _beforeSwapJoinExit();

        uint256 scalingFactorTokenIn = _scalingFactor(request.tokenIn);
        uint256 scalingFactorTokenOut = _scalingFactor(request.tokenOut);

        balanceTokenIn = _upscale(balanceTokenIn, scalingFactorTokenIn);
        balanceTokenOut = _upscale(balanceTokenOut, scalingFactorTokenOut);

        if (request.isGivenIn) {
            // Fees are subtracted before scaling, to reduce the complexity of the rounding direction analysis.
            request.amount = _subtractSwapFeeAmount(request.amount);

            // All token amounts are upscaled.
            request.amount = _upscale(request.amount, scalingFactorTokenIn);

            uint256 amountOut = _onSwapGivenIn(request, balanceTokenIn, balanceTokenOut);

            // amountOut tokens are exiting the Pool, so we round down.
            return _downscaleDown(amountOut, scalingFactorTokenOut);
        } else {
            // All token amounts are upscaled.
            request.amount = _upscale(request.amount, scalingFactorTokenOut);

            uint256 amountIn = _onSwapGivenOut(request, balanceTokenIn, balanceTokenOut);

            // amountIn tokens are entering the Pool, so we round up.
            amountIn = _downscaleUp(amountIn, scalingFactorTokenIn);

            // Fees are added after scaling happens, to reduce the complexity of the rounding direction analysis.
            return _addSwapFeeAmount(amountIn);
        }
    }
    // this low-level function should be called from a contract which performs important safety checks
    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external lock {
        require(
            amount0Out > 0 || amount1Out > 0,
            "Swappi: INSUFFICIENT_OUTPUT_AMOUNT"
        );
        (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
        require(
            amount0Out < _reserve0 && amount1Out < _reserve1,
            "Swappi: INSUFFICIENT_LIQUIDITY"
        );

        uint256 balance0;
        uint256 balance1;
        {
            // scope for _token{0,1}, avoids stack too deep errors
            address _token0 = token0;
            address _token1 = token1;
            require(to != _token0 && to != _token1, "Swappi: INVALID_TO");
            if (amount0Out > 0) _safeTransfer(_token0, to, amount0Out); // optimistically transfer tokens
            if (amount1Out > 0) _safeTransfer(_token1, to, amount1Out); // optimistically transfer tokens
            if (data.length > 0)
                ISwappiCallee(to).swappiCall(
                    msg.sender,
                    amount0Out,
                    amount1Out,
                    data
                );
            balance0 = IERC20(_token0).balanceOf(address(this));
            balance1 = IERC20(_token1).balanceOf(address(this));
        }
        uint256 amount0In =
            balance0 > _reserve0 - amount0Out
                ? balance0 - (_reserve0 - amount0Out)
                : 0;
        uint256 amount1In =
            balance1 > _reserve1 - amount1Out
                ? balance1 - (_reserve1 - amount1Out)
                : 0;
        require(
            amount0In > 0 || amount1In > 0,
            "Swappi: INSUFFICIENT_INPUT_AMOUNT"
        );
        {
            // scope for reserve{0,1}Adjusted, avoids stack too deep errors
            uint256 balance0Adjusted =
                (balance0.mul(10000).sub(amount0In.mul(3)));
            uint256 balance1Adjusted =
                (balance1.mul(10000).sub(amount1In.mul(3)));
            // require(
            //     balance0Adjusted.mul(balance1Adjusted) >=
            //         uint256(_reserve0).mul(_reserve1).mul(10000**2),
            //     "Swappi: K"
            // );
            require(
                _k(balance0Adjusted, balance1Adjusted) >=
                    _k(uint256(_reserve0).mul(10000),uint256(_reserve1).mul(10000)),
                "Swappi: K"
            );
        }

        _update(balance0, balance1, _reserve0, _reserve1);
        emit Swap(msg.sender, amount0In, amount1In, amount0Out, amount1Out, to);
    }

    // force balances to match reserves
    function skim(address to) external lock {
        address _token0 = token0; // gas savings
        address _token1 = token1; // gas savings
        _safeTransfer(
            _token0,
            to,
            IERC20(_token0).balanceOf(address(this)).sub(reserve0)
        );
        _safeTransfer(
            _token1,
            to,
            IERC20(_token1).balanceOf(address(this)).sub(reserve1)
        );
    }

    // force reserves to match balances
    function sync() external lock {
        _update(
            IERC20(token0).balanceOf(address(this)),
            IERC20(token1).balanceOf(address(this)),
            reserve0,
            reserve1
        );
    }
}