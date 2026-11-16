// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test, Vm} from "forge-std/Test.sol";
import {ISafe, Target, StorageWriter, Validator1271, Token, Rejecter} from "./helpers/Helpers.sol";

/// Deploys either build of the Safe: the solc 0.7.6 reference (behind its proxy) or the Verity bytecode.
abstract contract SafeDeployer is Test {
    function _deployVerity() internal returns (ISafe s) {
        bytes memory code = vm.parseBytes(vm.readFile("out/Safe.bin"));
        assembly { s := create(0, add(code, 32), mload(code)) }
        require(address(s) != address(0), "verity deploy failed");
    }

    function _deploySolc() internal returns (ISafe) {
        address singleton = deployCode("Safe.sol:Safe");
        return ISafe(deployCode("SafeProxy.sol:SafeProxy", abi.encode(singleton)));
    }
}

/// Safe 1.4.1 behaviour, run unchanged against both builds (see the two concrete contracts at the end).
abstract contract SafeBehaviour is SafeDeployer {
    event SafeSetup(address indexed initiator, address[] owners, uint256 threshold, address initializer, address fallbackHandler);
    event ApproveHash(bytes32 indexed approvedHash, address indexed owner);
    event ExecutionFailure(bytes32 indexed txHash, uint256 payment);
    event ExecutionSuccess(bytes32 indexed txHash, uint256 payment);
    event SafeReceived(address indexed sender, uint256 value);

    bytes32 constant DOMAIN_SEPARATOR_TYPEHASH = 0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218;
    bytes32 constant SAFE_TX_TYPEHASH = 0xbb8310d486368db6bd6f849402fdd73ad53d316b5a4b2644ad6efe0f941286d8;
    address constant SENTINEL = address(1);

    ISafe safe;
    Target target;
    uint256[] keys; // sorted by address
    address[] owners;

    struct SafeTx {
        address to;
        uint256 value;
        bytes data;
        uint8 operation;
        uint256 safeTxGas;
        uint256 baseGas;
        uint256 gasPrice;
        address gasToken;
        address refundReceiver;
    }

    function deploySafe() internal virtual returns (ISafe);

    function setUp() public {
        target = new Target();
        for (uint256 k = 101; k <= 103; k++) keys.push(k);
        _sortKeys(keys);
        for (uint256 i = 0; i < keys.length; i++) owners.push(vm.addr(keys[i]));
        safe = deploySafe();
        safe.setup(owners, 2, address(0), "", address(0), address(0), 0, payable(address(0)));
        vm.deal(address(safe), 10 ether);
    }

    // ---------------------------------------------------------------- helpers

    function _sortKeys(uint256[] storage ks) internal {
        for (uint256 i = 0; i < ks.length; i++)
            for (uint256 j = i + 1; j < ks.length; j++)
                if (vm.addr(ks[j]) < vm.addr(ks[i])) (ks[i], ks[j]) = (ks[j], ks[i]);
    }

    function _call(address to, uint256 value, bytes memory data) internal pure returns (SafeTx memory t) {
        t.to = to;
        t.value = value;
        t.data = data;
    }

    function _domainSeparator(ISafe s) internal view returns (bytes32) {
        return keccak256(abi.encode(DOMAIN_SEPARATOR_TYPEHASH, block.chainid, address(s)));
    }

    function _txHash(ISafe s, SafeTx memory t, uint256 n) internal view returns (bytes32) {
        bytes32 h = keccak256(abi.encode(SAFE_TX_TYPEHASH, t.to, t.value, keccak256(t.data), t.operation,
            t.safeTxGas, t.baseGas, t.gasPrice, t.gasToken, t.refundReceiver, n));
        return keccak256(abi.encodePacked(bytes1(0x19), bytes1(0x01), _domainSeparator(s), h));
    }

    function _sign(uint256 key, bytes32 h) internal pure returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, h);
        return abi.encodePacked(r, s, v);
    }

    function _ethSign(uint256 key, bytes32 h) internal pure returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) =
            vm.sign(key, keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n32", h)));
        return abi.encodePacked(r, s, v + 4);
    }

    function _approved(address who) internal pure returns (bytes memory) {
        return abi.encodePacked(bytes32(uint256(uint160(who))), bytes32(0), uint8(1));
    }

    /// Signatures of the first `count` (sorted) owners over the current nonce.
    function _sigs(SafeTx memory t, uint256 count) internal view returns (bytes memory sigs) {
        bytes32 h = _txHash(safe, t, safe.nonce());
        for (uint256 i = 0; i < count; i++) sigs = abi.encodePacked(sigs, _sign(keys[i], h));
    }

    function _exec(SafeTx memory t, bytes memory sigs) internal returns (bool) {
        return safe.execTransaction(t.to, t.value, t.data, t.operation, t.safeTxGas, t.baseGas, t.gasPrice,
            t.gasToken, payable(t.refundReceiver), sigs);
    }

    function _expectRevertGS(string memory code) internal {
        vm.expectRevert(bytes(code));
    }

    /// Payment field of the last ExecutionSuccess/ExecutionFailure log.
    function _paymentFromLogs() internal returns (uint256 payment, bool found) {
        Vm.Log[] memory logs = vm.getRecordedLogs();
        for (uint256 i = 0; i < logs.length; i++) {
            if (logs[i].emitter == address(safe)
                && (logs[i].topics[0] == ExecutionSuccess.selector || logs[i].topics[0] == ExecutionFailure.selector)) {
                payment = abi.decode(logs[i].data, (uint256));
                found = true;
            }
        }
    }

    // ---------------------------------------------------------------- setup

    function test_setup_state() public view {
        assertEq(safe.getThreshold(), 2);
        assertEq(safe.nonce(), 0);
        address[] memory got = safe.getOwners();
        assertEq(got.length, 3);
        for (uint256 i = 0; i < 3; i++) {
            assertEq(got[i], owners[i]);
            assertTrue(safe.isOwner(owners[i]));
        }
        assertFalse(safe.isOwner(SENTINEL));
        assertFalse(safe.isOwner(address(0)));
        assertFalse(safe.isOwner(address(this)));
    }

    function test_setup_storageLayout() public view {
        assertEq(uint256(vm.load(address(safe), bytes32(uint256(3)))), 3, "ownerCount slot 3");
        assertEq(uint256(vm.load(address(safe), bytes32(uint256(4)))), 2, "threshold slot 4");
        assertEq(uint256(vm.load(address(safe), bytes32(uint256(5)))), 0, "nonce slot 5");
        bytes32 sentinelSlot = keccak256(abi.encode(SENTINEL, uint256(2)));
        assertEq(address(uint160(uint256(vm.load(address(safe), sentinelSlot)))), owners[0], "owners[SENTINEL]");
        bytes32 lastSlot = keccak256(abi.encode(owners[2], uint256(2)));
        assertEq(address(uint160(uint256(vm.load(address(safe), lastSlot)))), SENTINEL, "owners[last]");
        bytes32 moduleSlot = keccak256(abi.encode(SENTINEL, uint256(1)));
        assertEq(uint256(vm.load(address(safe), moduleSlot)), 1, "modules[SENTINEL]");
    }

    function test_setup_event() public {
        ISafe s = deploySafe();
        vm.expectEmit(true, true, true, true, address(s));
        emit SafeSetup(address(this), owners, 1, address(0), address(0));
        s.setup(owners, 1, address(0), "", address(0), address(0), 0, payable(address(0)));
    }

    function test_setup_twice_GS200() public {
        _expectRevertGS("GS200");
        safe.setup(owners, 1, address(0), "", address(0), address(0), 0, payable(address(0)));
    }

    function test_setup_thresholdTooHigh_GS201() public {
        ISafe s = deploySafe();
        _expectRevertGS("GS201");
        s.setup(owners, 4, address(0), "", address(0), address(0), 0, payable(address(0)));
    }

    function test_setup_thresholdZero_GS202() public {
        ISafe s = deploySafe();
        _expectRevertGS("GS202");
        s.setup(owners, 0, address(0), "", address(0), address(0), 0, payable(address(0)));
    }

    function test_setup_badOwners_GS203() public {
        address[4] memory bad = [address(0), SENTINEL, address(0), owners[0]];
        for (uint256 b = 0; b < 3; b++) {
            ISafe s = deploySafe();
            address[] memory os = new address[](2);
            os[0] = owners[0];
            os[1] = b == 2 ? address(s) : bad[b];
            _expectRevertGS("GS203");
            s.setup(os, 1, address(0), "", address(0), address(0), 0, payable(address(0)));
        }
        ISafe s2 = deploySafe();
        address[] memory adjacent = new address[](2);
        adjacent[0] = owners[0];
        adjacent[1] = owners[0];
        _expectRevertGS("GS203");
        s2.setup(adjacent, 1, address(0), "", address(0), address(0), 0, payable(address(0)));
    }

    function test_setup_duplicateOwner_GS204() public {
        ISafe s = deploySafe();
        address[] memory os = new address[](3);
        os[0] = owners[0];
        os[1] = owners[1];
        os[2] = owners[0];
        _expectRevertGS("GS204");
        s.setup(os, 1, address(0), "", address(0), address(0), 0, payable(address(0)));
    }

    function test_noSetup_GS001() public {
        ISafe s = deploySafe();
        _expectRevertGS("GS001");
        s.execTransaction(address(target), 0, "", 0, 0, 0, 0, address(0), payable(address(0)), "");
    }

    function test_domainSeparator() public view {
        assertEq(safe.domainSeparator(), _domainSeparator(safe));
        assertEq(safe.getChainId(), block.chainid);
    }

    function test_receive_emitsSafeReceived() public {
        vm.expectEmit(true, true, true, true, address(safe));
        emit SafeReceived(address(this), 1 ether);
        (bool ok,) = address(safe).call{value: 1 ether}("");
        assertTrue(ok);
    }

    // ---------------------------------------------------------------- ECDSA

    function test_exec_ecdsa_callWithValue() public {
        SafeTx memory t = _call(address(target), 1 ether, hex"c0ffee");
        bytes32 h = _txHash(safe, t, 0);
        vm.expectEmit(true, true, true, true, address(safe));
        emit ExecutionSuccess(h, 0);
        assertTrue(_exec(t, _sigs(t, 2)));
        assertEq(safe.nonce(), 1);
        assertEq(target.calls(), 1);
        assertEq(target.lastValue(), 1 ether);
        assertEq(target.lastData(), hex"c0ffee");
        assertEq(target.lastSender(), address(safe));
        assertEq(address(target).balance, 1 ether);
    }

    function test_exec_moreSignaturesThanThreshold() public {
        SafeTx memory t = _call(address(target), 0, "");
        assertTrue(_exec(t, _sigs(t, 3)));
    }

    function test_exec_replay_GS026() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs(t, 2);
        _exec(t, sigs);
        _expectRevertGS("GS026");
        _exec(t, sigs);
    }

    function test_exec_unsorted_GS026() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        _expectRevertGS("GS026");
        _exec(t, abi.encodePacked(_sign(keys[1], h), _sign(keys[0], h)));
    }

    function test_exec_duplicateSigner_GS026() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        _expectRevertGS("GS026");
        _exec(t, abi.encodePacked(_sign(keys[0], h), _sign(keys[0], h)));
    }

    function test_exec_nonOwner_GS026() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        uint256[] memory ks = new uint256[](2);
        ks[0] = keys[0];
        ks[1] = 999;
        bytes memory sigs = vm.addr(999) > vm.addr(keys[0])
            ? abi.encodePacked(_sign(keys[0], h), _sign(999, h))
            : abi.encodePacked(_sign(999, h), _sign(keys[0], h));
        _expectRevertGS("GS026");
        _exec(t, sigs);
    }

    function test_exec_wrongTx_GS026() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs(t, 2);
        t.value = 1;
        _expectRevertGS("GS026");
        _exec(t, sigs);
    }

    function test_exec_invalidV_GS026() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs(t, 2);
        sigs[64] = bytes1(uint8(29));
        _expectRevertGS("GS026");
        _exec(t, sigs);
    }

    function test_exec_tooShort_GS020() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs(t, 2);
        assembly { mstore(sigs, 129) }
        _expectRevertGS("GS020");
        _exec(t, sigs);
    }

    function test_exec_operationOutOfRange_reverts() public {
        SafeTx memory t = _call(address(target), 0, "");
        t.operation = 2;
        bytes memory sigs = _sigs(t, 2);
        vm.expectRevert();
        _exec(t, sigs);
        assertEq(safe.nonce(), 0);
    }

    // ---------------------------------------------------------------- eth_sign, approved hashes

    function test_exec_ethSign() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        assertTrue(_exec(t, abi.encodePacked(_ethSign(keys[0], h), _sign(keys[1], h))));
    }

    function test_exec_ethSign_withoutPrefix_GS026() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(keys[0], h);
        _expectRevertGS("GS026");
        _exec(t, abi.encodePacked(r, s, v + 4, _sign(keys[1], h)));
    }

    function test_approveHash() public {
        bytes32 h = keccak256("x");
        vm.expectEmit(true, true, true, true, address(safe));
        emit ApproveHash(h, owners[0]);
        vm.prank(owners[0]);
        safe.approveHash(h);
        assertEq(safe.approvedHashes(owners[0], h), 1);
        bytes32 slot = keccak256(abi.encode(h, keccak256(abi.encode(owners[0], uint256(8)))));
        assertEq(uint256(vm.load(address(safe), slot)), 1, "approvedHashes slot 8");
    }

    function test_approveHash_nonOwner_GS030() public {
        _expectRevertGS("GS030");
        safe.approveHash(keccak256("x"));
    }

    function test_exec_preApprovedHash() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        vm.prank(owners[0]);
        safe.approveHash(h);
        assertTrue(_exec(t, abi.encodePacked(_approved(owners[0]), _sign(keys[1], h))));
    }

    function test_exec_senderIsOwner_implicitApproval() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        vm.prank(owners[0]);
        assertTrue(_exec(t, abi.encodePacked(_approved(owners[0]), _sign(keys[1], h))));
    }

    function test_exec_sentinelAsApprover_GS026() public {
        // owners[SENTINEL] is non-zero (it heads the owner list), so only the explicit
        // currentOwner != SENTINEL check stops address(1) from counting as an owner.
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        bytes memory sigs = abi.encodePacked(_approved(SENTINEL), _sign(keys[1], h));
        vm.prank(SENTINEL);
        _expectRevertGS("GS026");
        _exec(t, sigs);
    }

    function test_exec_notApproved_GS025() public {
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        _expectRevertGS("GS025");
        _exec(t, abi.encodePacked(_approved(owners[0]), _sign(keys[1], h)));
    }

    function test_exec_approvalForOtherNonce_GS025() public {
        SafeTx memory t = _call(address(target), 0, "");
        vm.prank(owners[0]);
        safe.approveHash(_txHash(safe, t, 1));
        bytes32 h = _txHash(safe, t, 0);
        _expectRevertGS("GS025");
        _exec(t, abi.encodePacked(_approved(owners[0]), _sign(keys[1], h)));
    }

    // ---------------------------------------------------------------- EIP-1271 contract signatures

    Validator1271 validator;
    uint256 eoaKey;

    /// A fresh 2-of-2 Safe owned by a validator contract and one EOA.
    function _setup1271() internal returns (ISafe s) {
        validator = new Validator1271();
        eoaKey = keys[0];
        s = deploySafe();
        address[] memory os = new address[](2);
        (os[0], os[1]) = address(validator) < vm.addr(eoaKey)
            ? (address(validator), vm.addr(eoaKey)) : (vm.addr(eoaKey), address(validator));
        s.setup(os, 2, address(0), "", address(0), address(0), 0, payable(address(0)));
        safe = s;
    }

    /// Static part (two 65-byte entries in owner order) + the dynamic contract signature.
    function _sigs1271(SafeTx memory t, bytes memory contractSig, uint256 sOverride, bool useOverride)
        internal view returns (bytes memory)
    {
        bytes32 h = _txHash(safe, t, safe.nonce());
        uint256 sPtr = useOverride ? sOverride : 130;
        bytes memory c = abi.encodePacked(bytes32(uint256(uint160(address(validator)))), bytes32(sPtr), uint8(0));
        bytes memory e = _sign(eoaKey, h);
        bytes memory head = address(validator) < vm.addr(eoaKey) ? abi.encodePacked(c, e) : abi.encodePacked(e, c);
        return abi.encodePacked(head, uint256(contractSig.length), contractSig);
    }

    function test_exec_1271_valid() public {
        _setup1271();
        validator.expect(hex"abcdef");
        SafeTx memory t = _call(address(target), 0, "");
        assertTrue(_exec(t, _sigs1271(t, hex"abcdef", 0, false)));
    }

    function test_exec_1271_wrongMagic_GS024() public {
        _setup1271();
        validator.setMode(Validator1271.Mode.Wrong);
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs1271(t, hex"abcdef", 0, false);
        _expectRevertGS("GS024");
        _exec(t, sigs);
    }

    function test_exec_1271_wrongSignatureBytes_GS024() public {
        _setup1271();
        validator.expect(hex"abcdef");
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs1271(t, hex"abcd00", 0, false);
        _expectRevertGS("GS024");
        _exec(t, sigs);
    }

    function test_exec_1271_revertBubbles() public {
        _setup1271();
        validator.setMode(Validator1271.Mode.Revert);
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs1271(t, hex"abcdef", 0, false);
        vm.expectRevert(bytes("1271 says no"));
        _exec(t, sigs);
    }

    function test_exec_1271_shortReturn_reverts() public {
        _setup1271();
        validator.setMode(Validator1271.Mode.Short);
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs1271(t, hex"abcdef", 0, false);
        vm.expectRevert(bytes(""));
        _exec(t, sigs);
    }

    function test_exec_1271_dirtyReturn_accepted() public {
        _setup1271();
        validator.setMode(Validator1271.Mode.Dirty);
        SafeTx memory t = _call(address(target), 0, "");
        assertTrue(_exec(t, _sigs1271(t, hex"abcdef", 0, false)));
    }

    function test_exec_1271_pointerInStaticPart_GS021() public {
        _setup1271();
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs1271(t, hex"abcdef", 129, true);
        _expectRevertGS("GS021");
        _exec(t, sigs);
    }

    function test_exec_1271_pointerPastEnd_GS022() public {
        _setup1271();
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs1271(t, hex"abcdef", 140, true);
        _expectRevertGS("GS022");
        _exec(t, sigs);
    }

    function test_exec_1271_pointerOverflow_reverts() public {
        _setup1271();
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs1271(t, hex"abcdef", type(uint256).max - 10, true);
        vm.expectRevert(bytes(""));
        _exec(t, sigs);
    }

    function test_exec_1271_lengthPastEnd_GS023() public {
        _setup1271();
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs1271(t, hex"abcdef", 0, false);
        assembly { mstore(sigs, sub(mload(sigs), 1)) }
        _expectRevertGS("GS023");
        _exec(t, sigs);
    }

    function test_exec_1271_eoaOwner_reverts() public {
        // v = 0 naming an account without code: the high-level call reverts before GS024.
        SafeTx memory t = _call(address(target), 0, "");
        bytes32 h = _txHash(safe, t, 0);
        bytes memory c = abi.encodePacked(bytes32(uint256(uint160(owners[0]))), bytes32(uint256(130)), uint8(0));
        bytes memory sigs = abi.encodePacked(c, _sign(keys[1], h), uint256(1), hex"00");
        vm.expectRevert(bytes(""));
        _exec(t, sigs);
    }

    // ---------------------------------------------------------------- execution outcome

    function test_exec_targetReverts_GS013() public {
        target.setRevert(true, "boom");
        SafeTx memory t = _call(address(target), 0, "");
        bytes memory sigs = _sigs(t, 2);
        _expectRevertGS("GS013");
        _exec(t, sigs);
        assertEq(safe.nonce(), 0);
    }

    function test_exec_targetReverts_withSafeTxGas_failureEvent() public {
        target.setRevert(true, "boom");
        SafeTx memory t = _call(address(target), 0, "");
        t.safeTxGas = 100_000;
        bytes32 h = _txHash(safe, t, 0);
        bytes memory sigs = _sigs(t, 2);
        vm.expectEmit(true, true, true, true, address(safe));
        emit ExecutionFailure(h, 0);
        assertFalse(_exec(t, sigs));
        assertEq(safe.nonce(), 1);
    }

    function test_exec_delegatecall_writesSafeStorage() public {
        StorageWriter w = new StorageWriter();
        SafeTx memory t = _call(address(w), 0, abi.encodeCall(StorageWriter.write, (100, 42)));
        t.operation = 1;
        assertTrue(_exec(t, _sigs(t, 2)));
        assertEq(uint256(vm.load(address(safe), bytes32(uint256(100)))), 42);
        assertEq(uint256(vm.load(address(w), bytes32(uint256(100)))), 0);
    }

    function test_exec_delegatecall_ignoresValue() public {
        StorageWriter w = new StorageWriter();
        SafeTx memory t = _call(address(w), 1 ether, abi.encodeCall(StorageWriter.write, (100, 42)));
        t.operation = 1;
        uint256 before = address(safe).balance;
        assertTrue(_exec(t, _sigs(t, 2)));
        assertEq(address(safe).balance, before);
    }

    function test_exec_delegatecallFails_GS013() public {
        StorageWriter w = new StorageWriter();
        SafeTx memory t = _call(address(w), 0, abi.encodeCall(StorageWriter.fail, ()));
        t.operation = 1;
        bytes memory sigs = _sigs(t, 2);
        _expectRevertGS("GS013");
        _exec(t, sigs);
    }

    function test_exec_selfCallChangesNonce() public {
        // A Safe transaction can call the Safe itself; here approveHash from the Safe (not an owner) fails.
        SafeTx memory t = _call(address(safe), 0, abi.encodeCall(ISafe.approveHash, (bytes32(0))));
        t.safeTxGas = 100_000;
        assertFalse(_exec(t, _sigs(t, 2)));
        assertEq(safe.nonce(), 1);
    }

    function test_exec_notEnoughGas_GS010() public {
        SafeTx memory t = _call(address(target), 0, "");
        t.safeTxGas = 5_000_000;
        bytes memory sigs = _sigs(t, 2);
        _expectRevertGS("GS010");
        safe.execTransaction{gas: 1_000_000}(t.to, t.value, t.data, t.operation, t.safeTxGas, t.baseGas,
            t.gasPrice, t.gasToken, payable(t.refundReceiver), sigs);
    }

    function test_exec_safeTxGasOverflow_wraps_GS010() public {
        // Solidity 0.7: (safeTxGas * 64) wraps; safeTxGas + 2500 wraps too, so the bound is tiny.
        SafeTx memory t = _call(address(target), 0, "");
        t.safeTxGas = type(uint256).max - 1000;
        t.gasPrice = 0;
        bytes memory sigs = _sigs(t, 2);
        // max((s*64)/63, s+2500)+500 with wrapping: s*64 = 2^256 - 64064 ... so the bound is huge: GS010.
        _expectRevertGS("GS010");
        _exec(t, sigs);
    }

    // ---------------------------------------------------------------- refunds

    function test_refund_eth_toReceiver() public {
        address receiver = makeAddr("receiver");
        SafeTx memory t = _call(address(target), 0, "");
        t.safeTxGas = 100_000;
        t.baseGas = 21_000;
        t.gasPrice = 100 gwei;
        t.refundReceiver = receiver;
        bytes memory sigs = _sigs(t, 2);
        vm.txGasPrice(1 gwei);
        vm.recordLogs();
        assertTrue(_exec(t, sigs));
        (uint256 payment, bool found) = _paymentFromLogs();
        assertTrue(found);
        assertEq(receiver.balance, payment, "receiver got the logged payment");
        assertEq(payment % 1 gwei, 0, "price is min(gasPrice, tx.gasprice)");
        assertGt(payment / 1 gwei, 21_000, "gasUsed + baseGas");
        assertLt(payment, 1_000_000 gwei, "priced at tx.gasprice (1 gwei), not the signed 100 gwei");
    }

    function test_refund_eth_toOrigin() public {
        address origin = makeAddr("origin");
        SafeTx memory t = _call(address(target), 0, "");
        t.safeTxGas = 100_000;
        t.gasPrice = 1 gwei;
        bytes memory sigs = _sigs(t, 2);
        vm.txGasPrice(5 gwei);
        vm.recordLogs();
        vm.prank(origin, origin);
        assertTrue(_exec(t, sigs));
        (uint256 payment,) = _paymentFromLogs();
        assertGt(payment, 0);
        assertEq(origin.balance, payment);
    }

    function test_refund_eth_rejected_GS011() public {
        SafeTx memory t = _call(address(target), 0, "");
        t.gasPrice = 1 gwei;
        t.refundReceiver = address(new Rejecter());
        bytes memory sigs = _sigs(t, 2);
        vm.txGasPrice(1 gwei);
        _expectRevertGS("GS011");
        _exec(t, sigs);
    }

    function test_refund_eth_insufficientBalance_GS011() public {
        SafeTx memory t = _call(address(target), 10 ether, "");
        t.safeTxGas = 100_000;
        t.gasPrice = 1 gwei;
        t.refundReceiver = makeAddr("receiver");
        bytes memory sigs = _sigs(t, 2);
        vm.txGasPrice(1 gwei);
        _expectRevertGS("GS011");
        _exec(t, sigs);
    }

    function test_refund_failedTxStillPays() public {
        target.setRevert(true, "boom");
        address receiver = makeAddr("receiver");
        SafeTx memory t = _call(address(target), 0, "");
        t.safeTxGas = 100_000;
        t.gasPrice = 1 gwei;
        t.refundReceiver = receiver;
        bytes memory sigs = _sigs(t, 2);
        vm.txGasPrice(1 gwei);
        vm.recordLogs();
        assertFalse(_exec(t, sigs));
        (uint256 payment,) = _paymentFromLogs();
        assertGt(payment, 0);
        assertEq(receiver.balance, payment);
    }

    function _tokenRefund(Token.Mode mode) internal returns (Token token, address receiver, SafeTx memory t, bytes memory sigs) {
        token = new Token();
        token.mint(address(safe), 1e30);
        token.setMode(mode);
        receiver = makeAddr("receiver");
        t = _call(address(target), 0, "");
        t.safeTxGas = 100_000;
        t.baseGas = 1000;
        t.gasPrice = 3;
        t.gasToken = address(token);
        t.refundReceiver = receiver;
        sigs = _sigs(t, 2);
    }

    function test_refund_zeroSafeTxGas_innerCallGetsNoGas() public {
        // gasPrice > 0 and safeTxGas = 0: the inner call gets 0 gas and fails, yet GS013 does not apply.
        SafeTx memory t = _call(address(target), 0, "");
        t.gasPrice = 1 gwei;
        t.refundReceiver = makeAddr("receiver");
        bytes memory sigs = _sigs(t, 2);
        vm.txGasPrice(1 gwei);
        assertFalse(_exec(t, sigs));
        assertEq(target.calls(), 0);
        assertEq(safe.nonce(), 1);
    }

    function test_refund_token_returnsTrue() public {
        (Token token, address receiver, SafeTx memory t, bytes memory sigs) = _tokenRefund(Token.Mode.ReturnsTrue);
        vm.recordLogs();
        assertTrue(_exec(t, sigs));
        (uint256 payment,) = _paymentFromLogs();
        assertEq(token.balanceOf(receiver), payment);
        assertEq(payment % 3, 0, "token refund uses the signed gasPrice");
        assertGt(payment / 3, 1000);
    }

    function test_refund_token_noReturnValue() public {
        (Token token, address receiver, SafeTx memory t, bytes memory sigs) = _tokenRefund(Token.Mode.NoReturn);
        vm.recordLogs();
        assertTrue(_exec(t, sigs));
        (uint256 payment,) = _paymentFromLogs();
        assertEq(token.balanceOf(receiver), payment);
    }

    function test_refund_token_returnsFalse_GS012() public {
        (,, SafeTx memory t, bytes memory sigs) = _tokenRefund(Token.Mode.ReturnsFalse);
        _expectRevertGS("GS012");
        _exec(t, sigs);
    }

    function test_refund_token_reverts_GS012() public {
        (,, SafeTx memory t, bytes memory sigs) = _tokenRefund(Token.Mode.Reverts);
        _expectRevertGS("GS012");
        _exec(t, sigs);
    }

    function test_refund_token_longReturn_GS012() public {
        (,, SafeTx memory t, bytes memory sigs) = _tokenRefund(Token.Mode.ReturnsLong);
        _expectRevertGS("GS012");
        _exec(t, sigs);
    }

    function test_refund_paymentOverflow_reverts() public {
        address receiver = makeAddr("receiver");
        SafeTx memory t = _call(address(target), 0, "");
        t.baseGas = type(uint256).max / 2;
        t.gasPrice = 1 gwei;
        t.refundReceiver = receiver;
        bytes memory sigs = _sigs(t, 2);
        vm.txGasPrice(1 gwei);
        vm.expectRevert(bytes(""));
        _exec(t, sigs);
    }
}

contract SolcSafeTest is SafeBehaviour {
    function deploySafe() internal override returns (ISafe) {
        return _deploySolc();
    }
}

contract VeritySafeTest is SafeBehaviour {
    function deploySafe() internal override returns (ISafe) {
        return _deployVerity();
    }
}
