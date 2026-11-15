#!/usr/bin/env python3
"""Replay the first symbolic counterexample in each rejected 193-state design."""
from pathlib import Path
import json, sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
sys.path.insert(0, str(BASE / 'construction/vendor'))
import symbolic_runtime as rt
import support

def contracts(sites, instructions):
    def frame(i, extra=0, effect=rt.PLAIN):
        return rt.frame(tuple(map(int, sites[i][0])), extra, effect)
    def target(i, extra=0, effect=rt.PLAIN):
        return rt.canonical(frame(i, extra, effect))
    out = []
    for i, code in enumerate(instructions):
        start = frame(i)
        if code[0] == 'inc':
            _, r, nxt = code
            out.append((i, None, start, target(nxt, 0, ('x', 'inc', rt.PHYSICAL[r]))))
        elif code[0] == 'dec':
            _, r, zero, positive = code
            out.extend([(i, (rt.PHYSICAL[r], True), start, target(zero)),
                        (i, (rt.PHYSICAL[r], False), start,
                         target(positive, 1, ('x', 'dec', rt.PHYSICAL[r])))])
        elif code[0] == 'jump':
            out.append((i, None, start, target(code[1])))
        else:
            out.append((i, None, start, None))
    return out

results = []
for folder, table, sites_file, ins_file, expected in [
    ('rejected_operand193', 'native.tm', 'sites.json', 'instructions.json', 11),
    ('rejected_scanner193', 'first193.native.tm', 'first193_sites.json', 'first193_ins.json', 50),
]:
    directory = HERE / folder
    rows = support.read_table(directory / table)
    assert len(rows) == 386
    sites = json.loads((directory / sites_file).read_text())
    instructions = json.loads((directory / ins_file).read_text())
    result = rt.validate(rows, contracts(sites, instructions))
    assert not result['ok'] and result['failed'][0] == expected, result
    results.append(dict(candidate=folder, states=len(rows)//2, validation=result,
                        failed_site=sites[expected],
                        maximum_zero_run=max(len(z) for p, _, _ in sites for z in p.split('1'))))
print(json.dumps(results, indent=2))
