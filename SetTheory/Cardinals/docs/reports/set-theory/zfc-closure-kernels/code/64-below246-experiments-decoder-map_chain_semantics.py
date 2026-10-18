#!/usr/bin/env python3
"""Associate late counter cases with their original DAG helper ancestry.

Prog254 is reassociated, so following a Prog254 address directly in Dag254 is
invalid. We instead align the complete in-order leaf sequences, asserting all
operation kinds and every decrement register agree. This is a provenance
diagnostic; it does not prove equivalence of the whole reassociated programs.
"""
import hashlib
import json
import os
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = Path(os.environ.get('ZFC246_BASE', ROOT.parents[1] / 'baseline/context246'))
sys.path.insert(0, str(BASE / 'code'))
from check_literal_instructions import program_sites

dag_path = ROOT / 'Dag254.v'
assert hashlib.sha256(dag_path.read_bytes()).hexdigest() == '538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3'
nodes = {}
names = {}
pattern = r'\| ([0-9]+) => \((E\w+(?: [0-9]+)?), (E\w+(?: [0-9]+)?)\)\s+\(\* (.*?) \*\)'
for q, left, right, name in re.findall(pattern, dag_path.read_text()):
    nodes[int(q)] = (left, right)
    names[int(q)] = name
assert len(nodes) == 219
opmap = dict(EInc='CI', EDecnz='CD', EBreak='CB', EContinue='CC', EHalt='CH')


def walk(q, prefix='', trace=()):
    for bit, edge in enumerate(nodes[q]):
        kind, *arg = edge.split()
        path = prefix + str(bit)
        ancestry = trace + ((q, names[q], bit),)
        if kind == 'ENode':
            yield from walk(int(arg[0]), path, ancestry)
        else:
            yield path, opmap[kind], int(arg[0]) if arg else None, ancestry


dag_sites = list(walk(0))
prog_sites = program_sites(BASE / 'sources/Prog254.v')
assert len(dag_sites) == len(prog_sites) == 6460
assert all(d[1] == p[1] for d, p in zip(dag_sites, prog_sites))
assert all(d[2] == p[2] for d, p in zip(dag_sites, prog_sites) if p[1] == 'CD')
lookup = {p[0]: d for d, p in zip(dag_sites, prog_sites)}
events = json.loads((ROOT / 'chain-contexts.json').read_text())
rows = []
seen = set()
for event in events:
    pc = event['pc']
    if pc in seen:
        continue
    seen.add(pc)
    dag_pc, op, register, trace = lookup[pc]
    assert op == event['op'] == 'CD' and register == event['r']
    rows.append(dict(pc=pc, op=event['op'], register=event['r'], dag_pc=dag_pc,
                     dag_op=op, dag_register=register, trace=trace))
assert len(rows) == 18
(ROOT / 'chain-semantic-map.json').write_text(json.dumps(rows, indent=2) + '\n')
stats = dict(scope='In-order source ancestry diagnostic, not a program equivalence proof.',
    dag_sha256=hashlib.sha256(dag_path.read_bytes()).hexdigest(), leaves=6460,
    matched_operation_kinds=6460,
    matched_decrement_registers=sum(p[1] == 'CD' for p in prog_sites),
    mismatched_increment_registers=sum(p[1] == 'CI' and d[2] != p[2] for d, p in zip(dag_sites, prog_sites)),
    late_sites=18, late_register_counts=dict(Counter(row['register'] for row in rows)))
(ROOT / 'chain-semantic-map-stats.json').write_text(json.dumps(stats, indent=2) + '\n')
print(json.dumps(stats, indent=2))
