#!/usr/bin/env python3
"""Reproduce PA194OR, the operand reassociation applied to the primary PA194."""
from pathlib import Path
import argparse, hashlib, json, sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
INPUTS = HERE / 'inputs'
sys.path.insert(0, str(HERE / 'vendor'))
import compiler as c
import support as s

def tup(x):
    return tuple(map(tup, x)) if isinstance(x, list) else x

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=BASE / 'machines/PA194OR')
args = parser.parse_args()
out = args.output
out.mkdir(parents=True, exist_ok=True)
def dump(name, obj):
    (out / name).write_text(json.dumps(obj, indent=2) + '\n')

original = s.read_table(INPUTS / 'primary.raw.native.tm')
folds = json.loads((INPUTS / 'primary.folds.json').read_text())
parent, _ = s.apply_folds(original, folds)
nodes = {k: tup(v) for k, v in json.loads((INPUTS / 'primary.nodes.json').read_text()).items()}
grammar = c.read_grammar(INPUTS / 'primary.grammar.json')
c.raw_nodes = lambda: nodes
oldsites, oldins, _ = c.source(grammar)

def expand(t):
    if isinstance(t, str):
        return expand(grammar if t == 'x67' else nodes[t])
    return t if t[0] == 'leaf' else tuple(expand(x) for x in t)

A, B, C, D = map(expand, ('node32', 'node53', 'node55', 'node65'))
assert expand('node75') == ((A, (B, C)), D)
nodes['node75'] = (A, (B, (C, D)))
raw = dict(original)
raw.update({(69, 0): (0, False, 92),
            (92, 0): (0, True, 111),
            (92, 1): (1, True, 90),
            (185, 1): (1, True, 2004),
            (213, 0): (0, True, 104),
            (213, 1): (1, True, 185)})
assert raw[2004, 0] == (0, True, 98) and raw[2004, 1] == (1, True, 90)
rows, aliases = s.apply_folds(raw, folds)
local = s.check_local_folds(raw, rows, aliases, folds)
sites, ins, contracts = c.source(grammar)
assert ins == oldins
runtime = c.validate(rows, contracts)
assert runtime['ok'], runtime
startup = s.startup(rows, sites[25][0])
dense, labels = s.dense_table(rows, 194)
pdense, _ = s.dense_table(parent, 194)
digest = hashlib.sha256(s.table_text(dense).encode()).hexdigest()
assert digest == '379e12957eafc5ecb1ec04868067fe931af913e7bc46e69a36b6067d83c4c79f'
for name, table in [('machine.tm', dense), ('machine.native.tm', rows),
                    ('raw.native.tm', raw), ('parent.tm', pdense),
                    ('parent.native.tm', parent)]:
    (out / name).write_text(s.table_text(table))
for name, value in [('labels.json', labels), ('nodes.json', nodes),
                    ('sites.json', [[''.join(map(str, p)), op, a] for p, op, a in sites]),
                    ('instructions.json', ins), ('folds.json', folds),
                    ('local_folds.json', local),
                    ('parent.sites.json', [[''.join(map(str, p)), op, a] for p, op, a in oldsites]),
                    ('parent.instructions.json', oldins)]:
    dump(name, value)
(out / 'grammar.json').write_bytes((INPUTS / 'primary.grammar.json').read_bytes())
receipt = dict(name='PA194OR', states=194, rows=388, raw=len(raw)//2,
               source_sites=len(sites), source_outcomes=len(contracts),
               source_instructions_identical=True,
               changed_source_addresses=sum(a[0] != b[0] for a, b in zip(sites, oldsites)),
               construction_symbolic=runtime, startup=startup, dense_sha256=digest,
               native_sha256=hashlib.sha256(s.table_text(rows).encode()).hexdigest(),
               changed_rows=[{'state': q, 'read': bit, 'old': parent[q, bit], 'new': act}
                             for (q, bit), act in sorted(rows.items()) if act != parent[q, bit]])
dump('receipt.json', receipt)
print(json.dumps(receipt, indent=2), flush=True)
