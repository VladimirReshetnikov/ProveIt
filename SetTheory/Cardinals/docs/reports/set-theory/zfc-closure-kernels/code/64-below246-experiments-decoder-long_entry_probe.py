#!/usr/bin/env python3
"""Finite census of the original counter's long exit; not an invariant proof."""
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = Path(os.environ.get('ZFC246_BASE', ROOT.parents[1] / 'baseline/context246'))
sys.path.insert(0, str(BASE / 'code'))
from check_literal_instructions import read_table, program_sites, paint, expected, PHYSICAL

table = read_table(BASE / 'machine/zfc_prefix246_old.tm')
tested = 0
events = 0
counterexamples = []
for pc, op, r in program_sites(BASE / 'sources/Prog254.v'):
    for positive in ([False, True] if op == 'CD' else [None]):
        regs = [0] * 9
        if op == 'CD':
            regs[PHYSICAL[r]] = int(positive)
        want = expected(pc, op, r, regs, [0], 0, 40)
        one = paint(pc, 40, regs, [0], 0)
        q, h = 96, 0
        for tick in range(4000):
            bit = int(h in one)
            if (q, bit) == (74, 0):
                events += 1
                if any(p < h for p in one):
                    counterexamples.append(dict(pc=pc, op=op, register=r,
                        positive=positive, tick=tick, head=h, ones=sorted(one)))
            w, move, q = table[q, bit]
            one.add(h) if w else one.discard(h)
            h += move
            if q == 254:
                assert op == 'CH'
                break
            if q == 96 and want is not None and (h, one) == want[:2]:
                break
        else:
            raise AssertionError((pc, op, r, 'fuel'))
        tested += 1
result = dict(scope='Finite one-suite diagnostic, not an invariant proof.',
    cases=tested, long_exit_events=events,
    events_with_a_one_to_the_left=len(counterexamples), counterexamples=counterexamples)
(ROOT / 'long-entry-contexts.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'counterexamples'}, indent=2))
