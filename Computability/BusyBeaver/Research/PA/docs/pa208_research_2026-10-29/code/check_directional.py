#!/usr/bin/env python3
"""Recheck all58initial directional rotations against both CFG resolvers."""
from pathlib import Path
import sys,json
ROOT=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'analysis/comparison'))
import source_inventory as I
import search_directional as D
L=I.L
rows=json.loads((I.base/'machine/variant_plain/u208.sites.json').read_text())
table=I.read(I.base/'machine/variant_plain/u208.native.tm');tree=L.tree(rows)
expected=L.graph_intervals(rows)
assert expected==L.graph_arithmetic(rows)[0]
rotations=D.enum(table,tree)
assert len(rotations)==58
for rotation in rotations:
    nt,newtree=D.rotate(table,tree,rotation)
    nr=L.sites(newtree)
    assert [(o,a)for _,o,a in nr]==[(o,a)for _,o,a in rows]
    graph,checks=L.graph_arithmetic(nr)
    assert graph==L.graph_intervals(nr)==expected
print(json.dumps({'status':'PASS','rotations':len(rotations),
    'primitive_word_and_both_cfg_resolvers_agree':True,
    'physical_runtime_not_implied':True},indent=2))
