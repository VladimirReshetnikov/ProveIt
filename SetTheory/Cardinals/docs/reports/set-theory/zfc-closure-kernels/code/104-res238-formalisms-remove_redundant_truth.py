#!/usr/bin/env python3
"""Delete one provably redundant equation from the supplied 946-bit packet.

This verifies serialization and finite Boolean-algebra diagnostics. The
unbounded ordinary proof is truth_redundancy.md. This does not emit a TM.
The two imported encoders/checkers are unchanged files from the user's
BusyBeaver239_Research_2026-10-19.zip, with attribution preserved separately.
"""
from __future__ import annotations

import copy
import hashlib
import itertools
import json
from pathlib import Path

import fuse_stack_packet as fused
import stack_kernel_source79 as base


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def main() -> None:
    root = Path(__file__).resolve().parent
    original = fused.transform(base.build(False), cons_nand=True,
                               truth_fusion=True, spare_witness='Pick')
    bits946, metrics946 = fused.verify(original)
    supplied = json.loads((root / 'packet946.json').read_text())
    assert json.loads(json.dumps(original['equations'])) == supplied['equations']
    assert json.loads(json.dumps(original['signature'])) == supplied['signature']
    assert metrics946 == supplied['metrics']
    assert metrics946['complete_packet_bits'] == 946
    assert sha(bits946.encode()) == '19d0a84437a01f11dc6e53ccbcb5492ce1ca0748a8f8e4b354f36a52e0e8c340'

    reduced = copy.deepcopy(original)
    removed = reduced['equations'].pop(1)
    assert removed == (('d',), ('N', ('d',), ('N', ('d',), ('d',))))
    # Literal unchanged order and terms of every other equation.
    assert reduced['equations'] == original['equations'][:1] + original['equations'][2:]
    bits921, metrics921 = fused.verify(reduced)
    assert metrics921['complete_packet_bits'] == 921
    assert metrics921['both_side_tree_nodes'] == 209
    assert metrics921['equations'] == 13
    assert metrics946['complete_packet_bits'] - metrics921['complete_packet_bits'] == 25
    assert 25 == 1 + 4 * sum(base.nodes(t) for t in removed)

    # All Boolean algebras of subsets of a k-element set for 0 <= k <= 4.
    # q and r are treated as independent values. This is only a diagnostic;
    # the note proves the assertion in every Boolean algebra.
    cases = 0
    satisfiers = 0
    per_algebra = []
    for k in range(5):
        top = (1 << k) - 1
        count = 0
        valid = 0
        N = lambda x, y: top ^ (x & y)
        for d, e, q, r in itertools.product(range(1 << k), repeat=4):
            count += 1
            if d == N(e, N(d, q)) and d == N(N(e, e), N(d, r)):
                assert d == top
                assert d == N(d, N(d, d))
                valid += 1
        per_algebra.append({'atoms': k, 'elements': 1 << k,
                            'assignments': count, 'satisfying_pairs': valid})
        cases += count
        satisfiers += valid
    assert cases == 69905

    reduced['name'] = 'stack_epsc_redundant_truth_removed_921'
    reduced['metrics'] = metrics921
    reduced['transformation'] = {'removed_original_equation_index': 1,
                                'other_equations_changed': False,
                                'signature_and_endpoints_changed': False}
    (root / 'packet921.bits').write_text(bits921 + '\n')
    (root / 'packet921.json').write_text(json.dumps(reduced, indent=2) + '\n')
    (root / 'packet921.equations').write_text(''.join(
        f'{i:02}: {base.pretty(a)} = {base.pretty(b)}\n'
        for i, (a, b) in enumerate(reduced['equations'])))
    receipt = {
        'status': 'PASS: exact same-codec reduction and finite algebra diagnostics',
        'ordinary_theorem': 'The removed equation follows from Sh1, class-NAND and arbitrary-witness.',
        'machine_status': 'No new binary interpreter, initializer, or machine-state count.',
        'input_archive': '../inputs/BusyBeaver239_Research_2026-10-19.zip',
        'input_member': 'zfc239-coordinated-reuse-2026-10-19/foundations/generated/stack_epsc_explicit_pick_cons_nand_truth_fused_spare_pick.json',
        'source_hashes': {name: sha((root/name).read_bytes()) for name in (
            'stack_kernel_source79.py', 'fuse_stack_packet.py', 'packet946.json')},
        'baseline': metrics946,
        'reduced': metrics921,
        'finite_algebra_assignments': cases,
        'finite_algebra_satisfiers': satisfiers,
        'finite_algebras': per_algebra,
        'ordinary_proof': 'truth_redundancy.md',
        'proof_assistant_status': 'No new Lean or Rocq check.',
    }
    (root / 'truth_redundancy_verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
