// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// The Safe 1.4.1 surface both builds expose.
interface ISafe {
    function setup(address[] calldata owners, uint256 threshold, address to, bytes calldata data,
        address fallbackHandler, address paymentToken, uint256 payment, address payable paymentReceiver) external;
    function execTransaction(address to, uint256 value, bytes calldata data, uint8 operation, uint256 safeTxGas,
        uint256 baseGas, uint256 gasPrice, address gasToken, address payable refundReceiver, bytes memory signatures)
        external payable returns (bool);
    function approveHash(bytes32 hashToApprove) external;
    function nonce() external view returns (uint256);
    function getThreshold() external view returns (uint256);
    function getOwners() external view returns (address[] memory);
    function isOwner(address owner) external view returns (bool);
    function domainSeparator() external view returns (bytes32);
    function getChainId() external view returns (uint256);
    function approvedHashes(address owner, bytes32 hash) external view returns (uint256);
}

/// Call target: records the last call, or reverts with preset data.
contract Target {
    uint256 public calls;
    uint256 public lastValue;
    bytes public lastData;
    address public lastSender;
    bytes public revertData;
    bool public shouldRevert;

    function setRevert(bool on, bytes calldata data) external {
        shouldRevert = on;
        revertData = data;
    }

    fallback() external payable {
        if (shouldRevert) {
            bytes memory d = revertData;
            assembly { revert(add(d, 32), mload(d)) }
        }
        calls += 1;
        lastValue = msg.value;
        lastData = msg.data;
        lastSender = msg.sender;
    }
}

/// Delegatecall target: writes into the caller's storage.
contract StorageWriter {
    function write(uint256 slot, uint256 value) external {
        assembly { sstore(slot, value) }
    }
    function fail() external pure {
        revert("writer failed");
    }
}

/// Legacy EIP-1271 validator (`isValidSignature(bytes,bytes)`), the interface Safe 1.4.1 calls.
contract Validator1271 {
    enum Mode { Magic, Wrong, Revert, Short, Dirty }
    Mode public mode;
    bytes32 public expectedSigHash;
    bytes public lastData;

    function setMode(Mode m) external { mode = m; }
    function expect(bytes calldata sig) external { expectedSigHash = keccak256(sig); }

    function isValidSignature(bytes memory data, bytes memory sig) external view returns (bytes4) {
        if (mode == Mode.Revert) revert("1271 says no");
        if (mode == Mode.Wrong) return 0xdeadbeef;
        if (mode == Mode.Short) assembly { mstore(0, 0x20c13b0b00000000000000000000000000000000000000000000000000000000) return(0, 4) }
        if (mode == Mode.Dirty) assembly { mstore(0, 0x20c13b0b000000000000000000000000000000000000000000000000000000ff) return(0, 32) }
        // Magic only for the expected signature bytes and a 66-byte EIP-712 pre-image.
        if (keccak256(sig) != expectedSigHash || data.length != 66 || data[0] != 0x19 || data[1] != 0x01) return 0;
        return 0x20c13b0b;
    }
}

/// ERC-20 used for gas refunds; the return shape is configurable.
contract Token {
    enum Mode { ReturnsTrue, ReturnsFalse, NoReturn, Reverts, ReturnsLong }
    Mode public mode;
    mapping(address => uint256) public balanceOf;

    function setMode(Mode m) external { mode = m; }
    function mint(address to, uint256 amount) external { balanceOf[to] += amount; }

    function transfer(address to, uint256 amount) external returns (bool) {
        if (mode == Mode.Reverts) revert("token reverts");
        if (mode == Mode.ReturnsFalse) return false;
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        if (mode == Mode.NoReturn) assembly { return(0, 0) }
        if (mode == Mode.ReturnsLong) assembly { mstore(0, 1) mstore(32, 1) return(0, 64) }
        return true;
    }
}

/// ETH receiver that rejects payments.
contract Rejecter {
    receive() external payable { revert("no eth"); }
}
