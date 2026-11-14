#!/usr/bin/env python3
"""Exact, mathematically justified AX source variants (not certified TMs)."""
import itertools
import json
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]/'construction/inputs/pa194.grammar.json'
OUT=Path(__file__).resolve().parent
NAMES={'node49':'push','node55':'copyD','node58':'copyH','node70':'copyA',
       'node65':'cons','node72':'readH','node75':'readDCons',
       'node142':'copyGuard','node150':'compareGuard'}
NATIVE={v:k for k,v in NAMES.items()}
NATIVE.update(incT=['leaf','inc',1],close=['leaf','breakTo',1])
def flatten_grammar(d):
    def go(t):
        if isinstance(t,list):
            return ['incT'] if t==['leaf','inc',1] else ['close'] if t==['leaf','breakTo',1] else (_ for _ in ()).throw(ValueError(t))
        if t in d['rules']:return sum((go(c) for c in d['rules'][t]),[])
        if t=='node60':return ['incT']*2
        if t=='node61':return ['incT']*4
        return [NAMES[t]]
    return go(d['root'])
base=flatten_grammar(json.loads(BASE.read_text()))
I=lambda a,b:('I',a,b)
M=lambda a,b:('M',a,b)
U=lambda a,b:('U',a,b)
E=lambda a,b:('E',a,b)
N=lambda a:I(a,1)
And=lambda a,b:N(I(a,N(b)))
Ex=lambda a,b:N(U(a,N(b)))
D,H,A='D','H','A'
heads=[I(Ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),
       I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),
       Ex(D,E(H,D)),I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
gamma=I(A,U(A,A))
v=I(M(H,D),U(A,M(H,D)))
point=I(A,M(A,D))
def gate(swap_conj=False,swap_inner=False):
    left=I(A,I(M(H,D),M(A,D))) if swap_inner else I(M(H,D),point)
    right=I(M(A,D),A)
    matrix=And(right,left) if swap_conj else And(left,right)
    s=U(D,matrix)
    q=U(A,I(s,N(point)))
    return N(I(v,q))
def emit(t,flipE=False,flipM=False,swap_tags=False):
    if isinstance(t,str):return ['copy'+t]
    if t==1:return ['push','incT']
    op,x,y=t
    if op=='U' or (op=='E' and flipE) or (op=='M' and flipM):x,y=y,x
    tags={'I':0,'M':1,'U':3 if swap_tags else 2,'E':2 if swap_tags else 3}
    return emit(x,flipE,flipM,swap_tags)+emit(y,flipE,flipM,swap_tags)+['cons']+['incT']*tags[op]
assert len(base)==190
assert base[:5]==['copyH','copyD','cons','incT','incT']
assert base==base[:18]+sum((emit(h) for h in heads),[])+emit(gamma)+emit(gate())+base[-3:]
variants=[]
for swap_conj,swap_inner,flipM,flipE,swap_tags in itertools.product([False,True],repeat=5):
    if not any((swap_conj,swap_inner,flipM,flipE,swap_tags)):continue
    for curry in range(8):
        hs=heads[:]
        for bit,j in enumerate((2,3,5)):
            if curry>>bit&1:
                op,x,yy=hs[j];_,y,z=yy
                hs[j]=I(y,I(x,z))
        name='_'.join(k for k,b in [('conj',swap_conj),('inner',swap_inner),('flipM',flipM),('flipE',flipE),('tags',swap_tags)] if b)+f'_curry{curry}'
        pref=base[:5]+(['incT'] if swap_tags else [])+base[5:18]
        es=lambda x:emit(x,flipE,flipM,swap_tags)
        word=pref+sum((es(h) for h in hs),[])+es(gamma)+es(gate(swap_conj,swap_inner))+base[-3:]
        variants.append({'name':name,'macro_tokens':len(word),'word':word,
                         'native_word':[NATIVE[t] for t in word],
                         'changes':dict(swap_conj=swap_conj,swap_inner=swap_inner,flipM=flipM,flipE=flipE,swap_tags=swap_tags,curry_mask=curry)})
(OUT/'safe_gate_and_encoding_variants.json').write_text(json.dumps(variants,indent=2)+'\n')
(OUT/'base_tokens.json').write_text(json.dumps(base,indent=2)+'\n')
print(f'{len(variants)} variants; sizes {sorted(set(v["macro_tokens"] for v in variants))}')
print(OUT/'safe_gate_and_encoding_variants.json')
