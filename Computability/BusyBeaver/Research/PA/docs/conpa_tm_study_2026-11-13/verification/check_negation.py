#!/usr/bin/env python3
"""Check the exact macro-word and source binding for direct negation.
The arithmetic identity is proved in report.tex, not inferred from samples.
"""
from pathlib import Path
import json,sys
import symbolic as S
ROOT=Path(__file__).resolve().parents[1]
def require(x,m):
    if not x:raise ValueError(m)
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
def restore(ss):
    leaves={tuple(p):('leaf',tuple(o))for p,o in ss}
    def go(p=()):return leaves[p]if p in leaves else(go(p+(0,)),go(p+(1,)))
    return go()
def at(t,p):
    for b in p:t=t[b]
    return t
def replace(t,p,new):
    if not p:return new
    a,b=t
    return (replace(a,p[1:],new),b)if p[0]==0 else(a,replace(b,p[1:],new))
def main():
    d=json.loads((ROOT/'research/direct_negation/grammar.json').read_text())
    _,defs=S.source_tree();atoms={v:defs[k]for k,v in d['tokens'].items()}
    atoms|={'i':('leaf',('inc',1)),'B':('leaf',('breakTo',1))}
    base=restore(json.loads((ROOT/'machines/h_only_mp_h_sites.json').read_text()))
    prefix=tuple(map(int,'100101001'));inverse={v:k for k,v in atoms.items()}
    def word(t):return [inverse[t]]if t in inverse else word(t[0])+word(t[1])
    oldword=word(at(base,prefix));require(oldword==d['original_word'],'original AX macro word')
    require(''.join(oldword).count('PiC')==8,'eight disjoint original negation patterns')
    newword=list(''.join(oldword).replace('PiC','N'))
    require(len(oldword)==201 and len(newword)==185,'macro counts')
    N=(('leaf',('inc',7)),(('leaf',('inc',7)),defs['node64']))
    require(freeze(d['negation_tree'])==N,'exact specialized negation body')
    atoms['N']=N
    def decode(q):return tuple(map(decode,d['rules'][q]))if q in d['rules']else q
    grammar=decode(d['root'])
    def flatten(t):return[t]if isinstance(t,str)else flatten(t[0])+flatten(t[1])
    require(flatten(grammar)==newword,'new grammar has the correct word')
    def expand(t):return atoms[t]if isinstance(t,str)else(expand(t[0]),expand(t[1]))
    new=replace(base,prefix,expand(grammar))
    expected=freeze(json.loads((ROOT/'machines/direct_negation197_sites.json').read_text()))
    require(tuple(S.flatten(new))==expected,'full modified source binding')
    require(len(expected)==3556,'source occurrence count')
    receipt=dict(status='PASS',old_macro_items=201,new_macro_items=185,negation_replacements=8,
                 source_sites=3556,scope='Exact macro-word/source binding; arbitrary-value arithmetic identity is a separate written proof.')
    (ROOT/'receipts/negation_binding.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
