pragma solidity =0.5.16;

import './interfaces/ISwappiFactory.sol';
import './SwappiPair.sol';

contract SwappiFactoryStable is ISwappiFactory {
    bytes32 public constant INIT_CODE_PAIR_HASH = keccak256(abi.encodePacked(type(SwappiPairWeighted).creationCode));

    address public feeTo;
    address public feeToSetter;

    mapping(address => mapping(address => address)) public getPair;
    address[] public allPairs;

    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    constructor(address _feeToSetter) public {
        feeToSetter = _feeToSetter;
    }

    function allPairsLength() external view returns (uint) {
        return allPairs.length;
    }

    function createPair(address tokenA, address tokenB, uint256[2] calldata normalizedWeights) external returns (address pair) {
        require(tokenA != tokenB, 'Swappi: IDENTICAL_ADDRESSES');
        (address token0, address token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        require(token0 != address(0), 'Swappi: ZERO_ADDRESS');
        require(getPair[token0][token1] == address(0), 'Swappi: PAIR_EXISTS'); // single check is sufficient
        bytes memory bytecode = type(SwappiPairWeighted).creationCode;
        bytes32 salt = keccak256(abi.encodePacked(token0, token1));
        assembly {
            pair := create2(0, add(bytecode, 32), mload(bytecode), salt)
        }
        ISwappiPair(pair).initialize(token0, token1, normalizedWeights);
        getPair[token0][token1] = pair;
        getPair[token1][token0] = pair; // populate mapping in the reverse direction
        allPairs.push(pair);
        emit PairCreated(token0, token1, pair, allPairs.length);
    }

    function setFeeTo(address _feeTo) external {
        require(msg.sender == feeToSetter, 'Swappi: FORBIDDEN');
        feeTo = _feeTo;
        emit feeToChanged(_feeTo);
    }

    function setFeeToSetter(address _feeToSetter) external {
        require(msg.sender == feeToSetter, 'Swappi: FORBIDDEN');
        feeToSetter = _feeToSetter;
        emit feeToSetterChanged(_feeToSetter);
    }
}
