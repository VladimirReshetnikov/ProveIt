#!/usr/bin/env python3
"""Exact further specialization of the inspected 946-bit native-stack packet.

This emits a finite equational input, not a binary Turing machine.  It removes
Target, Next and Mem by Target=Q, Next=P and Mem=A.  The separate research note
gives the ordinary weighted-tag model construction and identifies inherited
calibration dependencies.  No historical-minimality claim is made.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys


def main():
    if sys.flags.optimize or not __debug__:
        raise SystemExit('This verifier requires assertions; omit -O and -OO.')
    parser = argparse.ArgumentParser()
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    source = args.reference / 'generated/stack_epsc_explicit_pick_cons_nand_truth_fused_spare_pick.bits'
    digest = hashlib.sha256(source.read_text().strip().encode()).hexdigest()
    assert digest == '19d0a84437a01f11dc6e53ccbcb5492ce1ca0748a8f8e4b354f36a52e0e8c340'
    sys.path.insert(0, str(args.reference.resolve()))
    import fuse_stack_packet as ref
    base = ref.base
    old = ref.transform(base.build(False), cons_nand=True,
                        truth_fusion=True, spare_witness='Pick')
    old_bits, old_metrics = ref.verify(old)
    assert old_bits == source.read_text().strip()
    data = copy.deepcopy(old)
    aliases = {'Target': 'Q', 'Next': 'P', 'Mem': 'A'}
    rw = lambda term: ref.rewrite_term(term, aliases)
    for field in ('equations', 'native_equations'):
        data[field] = [tuple(map(rw, e)) for e in old[field]]
    data['groups'] = [(label, [[(lit[0], lit[1], *(rw(x) for x in lit[2:]))
                              for lit in clause] for clause in clauses],
                       tuple(map(rw, equation)))
                      for label, clauses, equation in old['groups']]
    data['signature'] = {name: arity for name, arity in old['signature'].items()
                         if name not in aliases}
    data['start'], data['target'] = rw(old['start']), rw(old['target'])
    data['name'] = 'stack_epsc_structural_witness_sharing937'
    data['additional_aliases'] = aliases
    bits, metrics = ref.verify(data)
    assert metrics['complete_packet_bits'] == 937
    assert metrics['both_side_tree_nodes'] == 215
    assert metrics['signature_symbols'] == 10
    assert metrics['opcode_width'] == 4
    data['metrics'] = metrics
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / 'stack937.json').write_text(json.dumps(data, indent=2) + '\n')
    (args.out / 'stack937.bits').write_text(bits + '\n')
    (args.out / 'stack937.equations').write_text('\n'.join(
        f'{i:02}: {base.pretty(a)} = {base.pretty(b)}'
        for i, (a, b) in enumerate(data['equations'])) + '\n')
    report = {'status': 'finite syntax and Boolean-clause audit; no TM state count',
              'inherited946_sha256': digest, 'before': old_metrics,
              'after': metrics, 'aliases': aliases}
    (args.out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
