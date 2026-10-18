#!/usr/bin/env python3
"""All 8,391 symbolic instruction cases, under the proved register contracts.

The checker is a small reviewable computational proof, not a proof-assistant
kernel. Every accepted trace denotes all n >= 0, all allowed register values,
and all finite nonempty spare suffixes. A JSONL certificate records each case.
"""
from pathlib import Path
from collections import Counter
import argparse
import json
import time
import prefix_affine as affine
import prefix_model as model

ROOT = Path(__file__).resolve().parents[1]

def verify(certificate):
    table = {(str(q), b): (w, d, str(t))
             for (q, b), (w, d, t) in model.build().items()}
    totals = Counter()
    cases, minimum, maximum = 0, 10**9, 0
    began = time.monotonic()
    with certificate.open('w', encoding='utf-8') as record:
        for site, (pc, op, r) in enumerate(model.sites()):
            for zero in ((True, False) if op == 'CD' else (None,)):
                branch = (r, zero) if op == 'CD' else None
                if op == 'CI' or op == 'CD' and not zero:
                    successor = model.inc(pc)
                elif op == 'CD':
                    successor = model.inc(model.strip(pc, '0', 1))
                elif op == 'CB':
                    successor = model.inc(model.strip(pc, '0', r))
                elif op == 'CC':
                    successor = model.strip(pc, '1', r)
                else:
                    successor = ''
                effect = ('inc', r) if op == 'CI' else (
                    ('dec', r) if op == 'CD' and not zero else None)
                extra = int(op == 'CD' and not zero)
                right = ([('r', 0, 1, 41+extra), ('b', 1),
                          ('box', ('plain', effect))] if successor is None else
                         [('b', int(b)) for b in successor] +
                         [('r', 0, 1, 40+extra-len(successor)), ('b', 1),
                          ('box', ('plain', effect))])
                target = affine.canon([('b', 1)], right)
                rules, literal = affine.run(table, pc, branch, target,
                                             halt=op == 'CH', fuel=1000)
                totals.update(rules)
                cases += 1
                minimum = min(minimum, literal)
                maximum = max(maximum, sum(rules.values()))
                record.write(json.dumps(dict(site=site, pc=pc, operation=op,
                    physical_register_or_control_count=r, zero_guard=zero,
                    successor_pc=None if op == 'CH' else successor, halt=op == 'CH',
                    header_increase=None if op == 'CH' else extra+int(successor is None),
                    literal_progress=literal, rules=dict(rules)),
                    separators=(',', ':'))+'\n')
    assert cases == 8391 and minimum > 0
    return dict(status='PASS', cases=cases,
        minimum_literal_steps_per_case=minimum, max_rules_per_case=maximum,
        rule_totals=dict(totals), elapsed_seconds=time.monotonic()-began,
        semantics='All gap parameters n>=0, all nine primary values satisfying '
                  'the named decrement guard, every finite nonempty spare suffix.',
        gap_effect='For returning instructions: positive decrement +1; '
                   'overflow +1; all other cases +0. Halt has no target frame.',
        spare_effect='For returning instructions: increment appends [1]; '
                     'other operations preserve suffix',
        scope='Finite exhaustive symbolic check using four proved mathematical '
              'register contracts; not a Lean or Rocq kernel check.')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path,
                    default=ROOT/'evidence/prefix-affine-result.json')
    ap.add_argument('--certificate', type=Path,
                    default=ROOT/'evidence/affine-cases.jsonl')
    args = ap.parse_args()
    if not __debug__:
        ap.error('Assertions are required; do not use Python -O.')
    result = verify(args.certificate)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()

