#!/usr/bin/env python3
"""Exact AX words for reversing implication's Cantor-pair arguments.

All ordinary formula constructors emit their required child order. The rho8
prefix preserves its old field-read order and uses one reversed stack-pair
routine at its root; thus its old-d parameter is not accidentally overwritten.
"""
import argparse
import importlib.util
import itertools
import json
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import gate_variants as g
import transposed_implication_macro as tm
scan=tm.scan
import formula_words as w

def emit(f):
    if isinstance(f,str):return ['node49',g.INC] if f==g.ONE else[g.TOK[f]]
    tag,a,b=f
    if tag==0:a,b=b,a
    return emit(a)+emit(b)+['node65']+[g.INC]*tag

def renamed(t):
    v=scan.store[t]
    if v[0]=='node':return scan.node(renamed(v[1]),renamed(v[2]))
    if v[0] in ('inc','dec'):
        return scan.interned((v[0],{1:6,6:1}.get(v[1],v[1])))
    return t

COPY=scan.node(scan.node(scan.interned(('dec',4)),scan.env['node40']),
               scan.node(scan.interned(('dec',7)),scan.env['node52']))
DIRECT=scan.node(scan.env['node32'],scan.node(scan.env['node53'],
                 scan.node(COPY,scan.env['node64'])))
REVERSE=scan.node(scan.env['node17'],scan.node(renamed(scan.env['node46']),scan.env['node63']))
ALIASES={'node75I':DIRECT,'node65Rev':REVERSE}
PREFIX=['node58','node55','node65',g.INC,g.INC,'node72',
        'node55','node58','node65','node75I',
        'node58','node70','node65','node58','node55','node65','node65','node65Rev']

def pair(a,b):return (a+b)*(a+b+1)//2+b
def im(a,b):return 4*pair(b,a)
def U(a,b):return 4*pair(b,a)+2

def symbolic_prefix(t,stack,d,h,a,x,y):
    """Unbounded exact macro contracts on an explicit stack (not sampling)."""
    st=list(stack)
    field=iter((y,x))
    for op in PREFIX:
        if op in ('node58','node55','node70','node49'):
            st.insert(0,t)
            t={'node58':h,'node55':d,'node70':a,'node49':0}[op]
        elif op=='node65':
            t=4*pair(st.pop(0),t)
        elif op=='node65Rev':
            t=4*pair(t,st.pop(0))
        elif op=='node72':h+=next(field)
        elif op=='node75I':
            d+=next(field);t=4*pair(d,t)
        elif op==g.INC:t+=1
        else:raise ValueError(op)
    return t,st,d,h

def expand_token(tok):
    if isinstance(tok,str):return ALIASES[tok] if tok in ALIASES else scan.env[tok]
    _,op,arg=tok;return scan.interned((op,0 if arg is None else arg))

def baseline_association(word):
    it=iter(word)
    def rec(t):
        if not w.isnode(t):return expand_token(next(it))
        return scan.node(rec(t[0]),rec(t[1]))
    result=rec(w.initial)
    try:next(it);raise AssertionError('extra macros')
    except StopIteration:pass
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    reverse_tests=0
    for t,a,b in itertools.product(range(7),repeat=3):
        inp=[11,t,pair(a,b),17,19,23,0,0,29,31]
        act,n=tm.run(REVERSE,inp)
        exp=inp.copy();exp[1]=4*pair(t,a);exp[2]=b
        assert act==exp,(inp,act,exp)
        reverse_tests+=1
    prefix_tests=0
    for d,h,a,x,y in itertools.product(range(3),repeat=5):
        t,stack,D,H=symbolic_prefix(37,[41,43],d,h,a,x,y)
        L=im(im(H,d),D);right=im(im(D,H),im(a,H));rho=im(L,right)
        assert t==rho
        assert stack==[U(d,h),37,41,43]
        assert D==d+x and H==h+y
        prefix_tests+=1
    variants=[]
    for flags in itertools.product((False,True),repeat=3):
        gate=emit(g.gate(*flags))
        word=PREFIX+sum((emit(h) for h in w.heads(0,False)),[])+gate+w.suffix
        assert len(word)==201
        ax=baseline_association(word)
        source=scan.rewrite(scan.root,scan.env['x67'],ax)
        source=scan.rewrite(source,scan.env['node75'],DIRECT)
        variants.append({'commute_matrix_antecedents':flags[0],
                         'swap_matrix_conjuncts':flags[1],
                         'swap_gate_vacuities':flags[2],
                         'word':word,'gate_word':gate,
                         'baseline_association_source_nodes':scan.metric(source),
                         'baseline_association_source_sites':len(list(scan.leaf_occurrences(source)))})
    result={'scope':'Exact local source and macro-word construction, without a binary allocation or internal PA proof.',
            'implication_encoding':'I(a,b)=4*pair(b,a)',
            'unchanged_encodings':['M(a,b)=4*pair(a,b)+1','U(a,b)=4*pair(b,a)+2','E(a,b)=4*pair(a,b)+3'],
            'prefix_word':PREFIX,'macros':{k:tm.export(v) for k,v in ALIASES.items()},
            'reverse_cons_tests':reverse_tests,'prefix_tests':prefix_tests,
            'prefix_contract':'T=rho8(D,A,H,oldD), stack=[U(oldD,oldH),oldT]+oldstack, D=oldD+x,H=oldH+y; all with transposed I.',
            'head_words':[emit(h) for h in w.heads(0,False)],
            'variants':variants}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'reverse_cons_tests':reverse_tests,'prefix_tests':prefix_tests,
                      'variants':[(x['baseline_association_source_nodes'],x['baseline_association_source_sites'])for x in variants]}))

if __name__=='__main__':main()
