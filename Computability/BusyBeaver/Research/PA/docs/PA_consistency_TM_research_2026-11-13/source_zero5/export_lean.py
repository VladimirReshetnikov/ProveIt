#!/usr/bin/env python3
"""Regenerate definitions-only Lean source; does not claim a checked theorem."""
from pathlib import Path
import json
from verify import parse,leaf

ROOT=Path(__file__).resolve().parent
tree=parse(json.loads((ROOT/'source159_zero5.json').read_text()))
names={};lines=[]
ops={'CI':'inc','CD':'dec','CB':'breakTo','CC':'continueTo','CH':'halt'}
def emit(t):
    if leaf(t):
        op,arg=t
        return f'(.leaf (.{ops[op]}'+(''if arg is None else f' {arg}')+'))'
    if t not in names:
        left,right=emit(t[0]),emit(t[1]);name=f'node{len(names)}';names[t]=name
        lines.append(f'def {name} : Tree := .node {left} {right}')
    return names[t]
root=emit(tree)
text='''module
public import M6.TreeSite
/-! Definitions-only rendering of the checked JSON source witness.
This file has not been newly Lean-compiled. It supplies no machine or PA theorem. -/
@[expose] public section
namespace PAZeroFive
open M6.Source M6.Source.PathTrie
'''+ '\n'.join(lines)+f'\ndef trie : Tree := {root}\nend PAZeroFive\n'
(ROOT/'Source159.lean').write_text(text)
print(f'Wrote {len(names)} internal source definitions; not a physical state count.')
