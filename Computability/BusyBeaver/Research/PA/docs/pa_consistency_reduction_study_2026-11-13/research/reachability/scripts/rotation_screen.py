#!/usr/bin/env python3
"""Exact source rotations and failed physical candidates, not a new TM theorem."""
from pathlib import Path
import json
import compiler as c

HERE = Path(__file__).resolve().parent
INPUT = HERE.parent / 'inputs'
OUT = HERE.parent / 'receipts'
c.ROOT = INPUT
grammar = c.read_grammar(INPUT / 'pa194.grammar.json')
old_sites, old_instructions, old_contracts = c.source(grammar)
nodes = c.raw_nodes()
nodes.update(node21=('node20', 'node170'),
             node171=('node21', 'node23'),
             node172=('node7', 'node171'),
             node162=('node37', 'node163'),
             node164=('node75', 'node162'))
c.raw_nodes = lambda: nodes
sites, instructions, contracts = c.source(grammar)
assert old_instructions == instructions
labels = json.loads((INPUT / 'pa194.labels.json').read_text())
base = {}
for line in (INPUT / 'pa194.tm').read_text().splitlines():
    q, bit, write, direction, target = line.split()
    base[labels[int(q)], int(bit)] = (
        int(write), direction == 'R', labels[int(target)])

rotation_rows = {
    (84, 0): (0, True, 68),
    (53, 0): (0, True, 69),
    (53, 1): (1, True, 214),
    (310, 0): (0, True, 53),
    (100, 0): (0, True, 213),
    (100, 1): (1, True, 174),
    (174, 0): (0, True, 28),
    (174, 1): (1, True, 164),
}
naive = base | rotation_rows
repaired = naive | {(53, 0): (0, True, 333),
                    (333, 0): (0, True, 105),
                    (333, 1): (1, True, 31)}
short_naive = {key: act for key, act in naive.items() if key[0] != 34}
short_naive[23, 0] = (0, False, 75)
short_repaired = {key: act for key, act in repaired.items() if key[0] != 34}
short_repaired[23, 0] = (0, False, 75)

def failed_contracts(rows):
    result = []
    for contract in contracts:
        if c.run(rows, contract) is None:
            site, branch = contract[:2]
            path, opcode, argument = sites[site]
            result.append({'site': site, 'branch': branch,
                           'path': ''.join(map(str, path)),
                           'opcode': opcode, 'argument': argument})
    return result

def max_run(path):
    return max(map(len, ''.join(map(str, path)).split('1')))

fixed = [i for i in range(len(sites)) if i < 50 or i >= 3554]
result = {
    'accepted_machine': False,
    'source_instruction_equality': True,
    'source_sites': len(sites),
    'source_contracts': len(contracts),
    'source_nodes_updated': {name: nodes[name] for name in
                             ('node21', 'node171', 'node172', 'node162', 'node164')},
    'first_path_before': ''.join(map(str, old_sites[0][0])),
    'first_path_after': ''.join(map(str, sites[0][0])),
    'fixed_sites_with_six_zeros': [i for i in fixed if max_run(sites[i][0]) >= 6],
    'fixed_inc_sites_with_five_zeros': [i for i in fixed
        if sites[i][1] == 'inc' and max_run(sites[i][0]) >= 5],
    'modes': {},
}
for name, rows in [('rotated7_naive', naive),
                   ('rotated7_extra_reader', repaired),
                   ('rotated6_naive', short_naive),
                   ('rotated6_extra_reader', short_repaired)]:
    failures = failed_contracts(rows)
    result['modes'][name] = {
        'working_states': len({q for q, bit in rows}),
        'failures': failures,
        'failure_count': len(failures),
        'fixed_failure_count': sum(f['site'] in fixed for f in failures),
        'all_source_contracts_pass': not failures,
        'startup_proved': False,
    }
    print(name, result['modes'][name]['working_states'], len(failures),
          result['modes'][name]['fixed_failure_count'], flush=True)

OUT.mkdir(exist_ok=True)
(OUT / 'rotation_screen.json').write_text(json.dumps(result, indent=2) + '\n')
