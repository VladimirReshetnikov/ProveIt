#!/usr/bin/env python3
"""Reproduce the rejected 244-state scanner contraction.

This discovery audit deliberately records every failed guarded instruction
contract. A PASS for blank initialization is not a PASS for the machine.
The pristine 245-state package supplies the unchanged affine oracle.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
import time


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled; do not use Python -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--package', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    b, out = args.package.resolve(), args.output.resolve()
    if out.exists():
        ap.error('--output must be a new directory')
    source = b/'machine/zfc245_old.tm'
    assert hashlib.sha256(source.read_bytes()).hexdigest() == (
        'f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267')
    sys.path[:0] = [str(b/'code'), str(b/'reference/context246/code')]
    import parametric_prefix_affine as a
    from review_affine_source import full_inc, full_strip
    from build_routing_machine import sparse_boot
    from rebuild_machines import read_table, encode
    out.mkdir(parents=True)
    table, _ = read_table(source)
    assert len(table) == 490
    assert table[41, 0] == (0, 'L', 58)
    assert table[58, 0] == (0, 'L', 84)
    assert table[58, 1] == (1, 'L', 4)
    table[41, 0] = (0, 'L', 84)
    del table[58, 0]
    del table[58, 1]
    assert len(table) == 488
    assert all(t != 58 for w, d, t in table.values())
    candidate = out/'second_short244.tm'
    candidate.write_text(encode(table, 95))
    symbolic = {(str(q), bit): (w, d, str(t))
                for (q, bit), (w, d, t) in table.items()}
    a.PADDING = 64
    sites = json.loads((b/'certificate/sites_physical.json').read_text())
    failures, passed = [], Counter()
    begin = time.monotonic()
    for i, (pc, op, r) in enumerate(sites):
        for zero in ((True, False) if op == 'CD' else (None,)):
            branch = (r, zero) if op == 'CD' else None
            extra, effect, overflow = 0, None, False
            if op == 'CI':
                successor, overflow = full_inc(pc)
                effect = 'inc', r
            elif op == 'CD' and not zero:
                successor, overflow = full_inc(pc)
                effect, extra = ('dec', r), 1
            elif op == 'CD':
                successor, overflow = full_inc(full_strip(pc, '0', 1))
            elif op == 'CB':
                successor, overflow = full_inc(full_strip(pc, '0', r))
            elif op == 'CC':
                successor = full_strip(pc, '1', r)
            else:
                successor = ''
            target = a.canon([('b', 1)],
                            [('b', int(c)) for c in successor] + [
                                ('r', 0, 1, 64 + extra + int(overflow) - len(successor)),
                                ('b', 1), ('box', ('plain', effect))])
            try:
                rules, literal_steps = a.run(symbolic, pc, branch, target,
                                             halt=op == 'CH', fuel=1000)
                assert literal_steps > 0
                passed[op] += 1
            except Exception as error:
                # Discovery audit: a checker error is recorded as a failure,
                # never as a successful instruction or a logical refutation.
                failures.append(dict(index=i, pc=pc, op=op, r=r, zero=zero,
                                     error=str(error)))
    boot = sparse_boot(table, limit=1000000, minimum_gap=64)
    failed_pcs = {f['pc'] for f in failures}
    suffix_six = {pc for pc, op, r in sites if len(pc)-len(pc.rstrip('0')) >= 6}
    assert failed_pcs == suffix_six
    assert sum(passed.values()) == 8292 and len(failures) == 99
    assert len(failed_pcs) == 50
    assert boot['status'] == 'PASS' and boot['blank_steps'] == 818324
    assert boot['logical_registers'] == [6, 0, 0, 0, 4, 0, 0, 0, 1]
    assert boot['sparse_dense_exact_agreement']
    result = dict(status='REJECTED', working_states=244, rows=488,
                  candidate_sha256=hashlib.sha256(candidate.read_bytes()).hexdigest(),
                  passed=sum(passed.values()), passed_by_operation=dict(passed),
                  failures=failures, failed_sites=len(failed_pcs),
                  failures_exactly_suffix_six=True, boot=boot,
                  seconds=time.monotonic()-begin,
                  scope='Failed universal-contract attempt; not a solution and not a lower bound.')
    (out/'second_scan_result.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('failures', 'boot')}, indent=2))


if __name__ == '__main__':
    main()
