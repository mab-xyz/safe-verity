// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {SafeDeployer} from "./SafeBehaviour.t.sol";
import {ISafe, Target, StorageWriter} from "./helpers/Helpers.sol";

/// Differential fuzzing: the solc reference and the Verity build, set up identically, receive the same
/// fuzzed transaction (each signed for its own address) and must agree on the outcome bit for bit:
/// success flag, return/revert data, nonce, and the effect on the call target.
contract SafeDifferentialTest is SafeDeployer {
    bytes32 constant DOMAIN_SEPARATOR_TYPEHASH = 0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218;
    bytes32 constant SAFE_TX_TYPEHASH = 0xbb8310d486368db6bd6f849402fdd73ad53d316b5a4b2644ad6efe0f941286d8;

    ISafe ref;
    ISafe ver;
    Target targetRef;
    Target targetVer;
    StorageWriter writer;
    uint256[] keys;
    address[] owners;

    struct Tx {
        uint256 value;
        bytes data;
        uint8 operation;
        uint256 safeTxGas;
    }

    function setUp() public {
        for (uint256 k = 201; k <= 205; k++) keys.push(k);
        for (uint256 i = 0; i < keys.length; i++)
            for (uint256 j = i + 1; j < keys.length; j++)
                if (vm.addr(keys[j]) < vm.addr(keys[i])) (keys[i], keys[j]) = (keys[j], keys[i]);
        for (uint256 i = 0; i < keys.length; i++) owners.push(vm.addr(keys[i]));
        writer = new StorageWriter();
        targetRef = new Target();
        targetVer = new Target();
    }

    function _deployBoth(uint256 threshold) internal {
        ref = _deploySolc();
        ver = _deployVerity();
        ref.setup(owners, threshold, address(0), "", address(0), address(0), 0, payable(address(0)));
        ver.setup(owners, threshold, address(0), "", address(0), address(0), 0, payable(address(0)));
        vm.deal(address(ref), 5 ether);
        vm.deal(address(ver), 5 ether);
    }

    function _txHash(ISafe s, address to, Tx memory t, uint256 n) internal view returns (bytes32) {
        bytes32 ds = keccak256(abi.encode(DOMAIN_SEPARATOR_TYPEHASH, block.chainid, address(s)));
        bytes32 h = keccak256(abi.encode(SAFE_TX_TYPEHASH, to, t.value, keccak256(t.data), t.operation,
            t.safeTxGas, uint256(0), uint256(0), address(0), address(0), n));
        return keccak256(abi.encodePacked(bytes1(0x19), bytes1(0x01), ds, h));
    }

    /// Signatures from the owners selected by `mask` (ascending), kind per owner from `kinds`
    /// (0 ECDSA, 1 eth_sign, 2 pre-approved hash), then `corrupt` flips one byte if non-zero.
    function _signatures(ISafe s, address to, Tx memory t, uint8 mask, uint256 kinds, uint256 corrupt)
        internal returns (bytes memory sigs)
    {
        bytes32 h = _txHash(s, to, t, s.nonce());
        for (uint256 i = 0; i < keys.length; i++) {
            if (mask & (1 << i) == 0) continue;
            uint256 kind = (kinds >> (2 * i)) % 3;
            if (kind == 2) {
                vm.prank(owners[i]);
                s.approveHash(h);
                sigs = abi.encodePacked(sigs, bytes32(uint256(uint160(owners[i]))), bytes32(0), uint8(1));
            } else if (kind == 1) {
                (uint8 v, bytes32 r, bytes32 ss) =
                    vm.sign(keys[i], keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n32", h)));
                sigs = abi.encodePacked(sigs, r, ss, v + 4);
            } else {
                (uint8 v, bytes32 r, bytes32 ss) = vm.sign(keys[i], h);
                sigs = abi.encodePacked(sigs, r, ss, v);
            }
        }
        if (corrupt != 0 && sigs.length != 0) {
            uint256 at = corrupt % sigs.length;
            sigs[at] = bytes1(uint8(sigs[at]) ^ uint8(1 + (corrupt >> 128) % 255));
        }
    }

    function _run(ISafe s, address to, Tx memory t, bytes memory sigs) internal returns (bool ok, bytes memory ret) {
        (ok, ret) = address(s).call(abi.encodeCall(ISafe.execTransaction,
            (to, t.value, t.data, t.operation, t.safeTxGas, 0, 0, address(0), payable(address(0)), sigs)));
    }

    struct Case {
        uint8 threshold;
        uint8 mask;
        uint256 kinds;
        uint256 corrupt;
        uint96 value;
        bytes data;
        bool delegate;
        bool withSafeTxGas;
        bool targetReverts;
    }

    function testFuzz_execTransaction_agrees(Case memory c) public {
        c.threshold = uint8(bound(c.threshold, 1, keys.length));
        _deployBoth(c.threshold);
        Tx memory t = Tx(uint256(c.value) % 6 ether, c.data, c.delegate ? 1 : 0, c.withSafeTxGas ? 100_000 : 0);
        if (c.delegate) t.data = abi.encodeCall(StorageWriter.write, (77, uint256(keccak256(c.data))));
        if (c.targetReverts) {
            targetRef.setRevert(true, c.data);
            targetVer.setRevert(true, c.data);
        }
        address toRef = c.delegate ? address(writer) : address(targetRef);
        address toVer = c.delegate ? address(writer) : address(targetVer);
        _compare(toRef, toVer, t, c);
    }

    function _compare(address toRef, address toVer, Tx memory t, Case memory c) internal {
        (bool okR, bytes memory retR) =
            _run(ref, toRef, t, _signatures(ref, toRef, t, uint8(c.mask & 0x1f), c.kinds, c.corrupt));
        (bool okV, bytes memory retV) =
            _run(ver, toVer, t, _signatures(ver, toVer, t, uint8(c.mask & 0x1f), c.kinds, c.corrupt));
        assertEq(okV, okR, "success flag");
        assertEq(retV, retR, "return / revert data");
        assertEq(ver.nonce(), ref.nonce(), "nonce");
        assertEq(targetVer.calls(), targetRef.calls(), "target calls");
        assertEq(address(targetVer).balance, address(targetRef).balance, "target balance");
        assertEq(address(ver).balance, address(ref).balance, "safe balance");
        assertEq(vm.load(address(ver), bytes32(uint256(77))), vm.load(address(ref), bytes32(uint256(77))), "slot 77");
    }

    /// Arbitrary signature bytes: both builds reject (or accept) identically.
    function testFuzz_garbageSignatures_agree(uint8 threshold, bytes calldata sigs) public {
        threshold = uint8(bound(threshold, 1, keys.length));
        _deployBoth(threshold);
        Tx memory t = Tx(0, "", 0, 0);
        (bool okR, bytes memory retR) = _run(ref, address(targetRef), t, sigs);
        (bool okV, bytes memory retV) = _run(ver, address(targetVer), t, sigs);
        assertEq(okV, okR, "success flag");
        assertEq(retV, retR, "revert data");
    }

    /// Fuzzed setup arguments: same acceptance, revert data and resulting owner list.
    function testFuzz_setup_agrees(uint8 count, uint256 seed, uint256 threshold) public {
        count = uint8(bound(count, 0, 6));
        threshold = bound(threshold, 0, 7);
        ref = _deploySolc();
        ver = _deployVerity();
        address[] memory os = new address[](count);
        for (uint256 i = 0; i < count; i++) {
            uint256 pick = uint256(keccak256(abi.encode(seed, i))) % 8;
            os[i] = pick == 5 ? address(0) : pick == 6 ? address(1) : pick == 7 ? owners[0] : owners[pick % 5];
        }
        bytes memory call_ = abi.encodeCall(ISafe.setup,
            (os, threshold, address(0), "", address(0), address(0), 0, payable(address(0))));
        (bool okR, bytes memory retR) = address(ref).call(call_);
        (bool okV, bytes memory retV) = address(ver).call(call_);
        assertEq(okV, okR, "success flag");
        assertEq(retV, retR, "revert data");
        if (okR) {
            assertEq(ver.getOwners(), ref.getOwners(), "owners");
            assertEq(ver.getThreshold(), ref.getThreshold(), "threshold");
        }
    }
}
