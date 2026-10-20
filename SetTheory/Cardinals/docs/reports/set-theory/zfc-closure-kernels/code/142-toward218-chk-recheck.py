#!/usr/bin/env python3
"""Owned, dependency-free checks for this research companion.

Reads the packaged JSON and formal-source text as inert data. It imports no
received source, does not compile Rocq, and does not claim a Turing-machine
runtime proof. The infinite claims are proved in companion.tex.
"""
from pathlib import Path
import hashlib, json, itertools
ROOT=Path(__file__).resolve().parents[1]
def read(p): return json.loads((ROOT/p).read_text())
def h(p): return hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
manifest=read('PROVENANCE.json')
for p, v in manifest.items():
    if not p.startswith('upstream:'): assert h(p)==v['sha256'], p

def tree(sites):
    leaves={p:(o,n) for p,o,n in sites}
    assert len(leaves)==len(sites)
    prefixes={p[:k] for p in leaves for k in range(len(p))}
    assert not prefixes.intersection(leaves)
    assert all(p+b in leaves or p+b in prefixes for p in prefixes for b in '01')
    def get(p=''):
        return leaves[p] if p in leaves else (get(p+'0'),get(p+'1'))
    return get(),leaves,prefixes

def isatom(t): return isinstance(t[0],str)
def freeze(t): return tuple(map(freeze,t)) if isinstance(t,list) else t
def at(t,p):
    for b in p:t=t[int(b)]
    return t

def metrics(t,sites):
    seen=set();internal=set()
    def walk(q):
        seen.add(q)
        if not isatom(q):internal.add(q);walk(q[0]);walk(q[1])
    walk(t)
    return dict(distinct=len(seen),internal=len(internal),primitives=len(seen-internal),
                occurrences=len(sites),depth=max(len(p) for p,o,n in sites),
                max_zero_run=max(max(map(len,p.split('1'))) for p,o,n in sites),
                right_decrements=sum(o=='CD' and p.endswith('1') for p,o,n in sites))

baseline=read('evidence/source/baseline_sites.json'); shared=read('evidence/source/shared_sites.json')
bt,bl,bp=tree(baseline); st,sl,sp=tree(shared); macro=freeze(read('evidence/source/shared_macro.json'))
old=at(bt,'111110');paths=[]
def replace(t,p=''):
    if t==old:paths.append(p);return macro
    if isatom(t):return t
    return replace(t[0],p+'0'),replace(t[1],p+'1')
assert replace(bt)==st
assert paths==['111010010011101111000','11101001001110111110','1110100101100','111110']
bm,sm=metrics(bt,baseline),metrics(st,shared)
assert (bm['distinct'],bm['occurrences'])==(206,4744)
assert sm==dict(distinct=206,internal=183,primitives=23,occurrences=4752,depth=38,max_zero_run=6,right_decrements=0)

# Structurally reconstruct control flow, independently of binary-address arithmetic.
def graph(sites):
    inds={p:i for i,(p,o,n) in enumerate(sites)}
    def first(p):
        while p not in inds:p+='0'
        return inds[p]
    def next_(p,control,level=0):
        while p:
            side=p[-1];parent=p[:-1]
            if control=='N':
                if side=='0':return first(parent+'1')
            elif control=='B' and side=='0':
                level-=1
                if level==0:control='N'
            elif control=='C' and side=='1':
                level-=1
                if level==0:return first(parent)
            p=parent
        return first('')
    out=[]
    for i,(p,o,n) in enumerate(sites):
        for pos in ([False,True] if o=='CD' else [False]):
            if o=='CH':j=None
            elif o=='CI' or (o=='CD' and pos):j=next_(p,'N')
            elif o in ['CD','CB']:j=next_(p,'B',1 if o=='CD' else n)
            elif o=='CC':j=next_(p,'C',n)
            else:raise AssertionError(o)
            out.append(dict(case_index=len(out),site_index=i,path=p,op=o,argument=n,
                            positive=pos,target=j,target_path=sites[j][0] if j is not None else None))
    return out
scfg=graph(shared); assert scfg==read('evidence/source/shared_cfg.json')
assert len(scfg)==6179
assert [c['site_index'] for c in scfg if c['op']=='CH']==[4615]

# All-natural source proof is in the document; this is a finite diagnostic only.
def run(t,regs,fuel):
    fuel[0]-=1
    assert fuel[0]>=0,'Finite diagnostic cap exceeded'
    if isatom(t):
        o,k=t
        if o=='CI':regs[k]+=1;return ('N',0)
        if o=='CD':
            if regs[k]:regs[k]-=1;return ('N',0)
            return ('B',1)
        if o=='CB':return ('B',k)
        if o=='CC':return ('C',k)
        return ('H',0)
    while True:
        c,k=run(t[0],regs,fuel)
        if c=='B':return ('N',0) if k==1 else ('B',k-1)
        if c!='N':return c,k
        c,k=run(t[1],regs,fuel)
        if c=='C' and k==1:continue
        if c=='C':return 'C',k-1
        return c,k
pairs=list(itertools.product(range(41),repeat=2))+[(0,10000),(10000,0),(10000,10000),(9999,10000),(10000,9999)]
for a,b in pairs:
    r=[17,19,23,29,31,a,b,37,41];expected=r.copy();expected[5]=expected[6]=0
    c=run(macro,r,[100*(a+b+1)+100])
    assert r==expected and c==(('N',0) if a==b else ('B',1)),(a,b,r,c)

# The baseline seeded invariant is an exact finite abstraction of unbounded N.
facts=read('evidence/source/baseline_invariant.json')
assert len(facts)==len(baseline)
assert all(f is None or len(f)==9 and all(isinstance(m,int) and 0<m<1024 for m in f) for f in facts)
def atoms(m):return {i for i in range(10) if m&(1<<i)}
def mask(s):return sum(1<<i for i in s)
def succ(i):return {i+1} if i<7 else {8} if i==7 else {9} if i==8 else {8}
def pred(i):
    assert i>0
    return {i-1} if i<8 else {7,9} if i==8 else {8}
def abstract_step(f,o,n,pos):
    ss=list(map(atoms,f))
    if o=='CI':ss[n]=set().union(*(succ(i) for i in ss[n]))
    elif o=='CD':
        if pos:
            dom=ss[n]-{0}
            if not dom:return None
            ss[n]=set().union(*(pred(i) for i in dom))
        else:
            if 0 not in ss[n]:return None
            ss[n]={0}
    return list(map(mask,ss))
seed=[3,0,0,0,3,0,0,0,0]
assert all(facts[0][i]&(1<<x) for i,x in enumerate(seed))
checked=impossible=0
for c in graph(baseline):
    if c['op']=='CH':continue
    f=facts[c['site_index']]
    dst=abstract_step(f,c['op'],c['argument'],c['positive']) if f is not None else None
    if dst is None:impossible+=1;continue
    target=facts[c['target']];assert target is not None
    assert all(a&~b==0 for a,b in zip(dst,target)),c
    checked+=1
nip=next(i for i,s in enumerate(baseline) if s[0]=='11101001010')
halt=[i for i,s in enumerate(baseline) if s[1]=='CH']
assert (checked,impossible,nip)==(6161,5,4598)
assert facts[nip][6]==1 and halt==[4609] and facts[halt[0]] is not None

# A count of the failed table is not a semantic proof.
rows={}
for line in (ROOT/'evidence/compiler/provisional_candidate.native.tm').read_text().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,z=line.split();key=int(q),int(b);assert key not in rows
    rows[key]=int(w),d,int(z)
states={q for q,b in rows};assert len(states)==220 and len(rows)==440
assert all((q,b) in rows for q in states for b in (0,1))
pricing=read('evidence/compiler/raw_pricing.json')
assert pricing['table_sha256']==h('evidence/compiler/provisional_candidate.native.tm')
assert pricing['source_sha256']==h('evidence/source/shared_sites.json')
assert pricing['states']==220
screen=read('evidence/compiler/CI6_SYNTHESIS_RESULT.json')
assert screen['counts']['actions']==872 and screen['counts']['RuntimeError']==173
assert screen['results']==[] and screen['partial_passes']==[]

# Boolean truth check supplements, but does not replace, the schema proof.
imp=lambda x,y:not x or y
for a,b,c,u in itertools.product([False,True],repeat=4):
    assert imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))
result=dict(status='PASS_SCOPED_COMPANION_CHECKS',
    source_hash=h('evidence/source/shared_sites.json'),baseline_metrics=bm,shared_metrics=sm,
    exact_replacement_paths=paths,cfg_cases=len(scfg),equality_diagnostic_pairs=len(pairs),
    invariant=dict(enabled_nonhalting_edges=checked,infeasible_edges=impossible,nip_index=nip,R6=0,halt_admitted=True),
    provisional_table_graph=dict(states=len(states),rows=len(rows),semantic_status='NOT_VERIFIED'),
    not_proved_by_script=['Set-theoretic model existence','Infinite equality contract','Cofinal-core calibration',
                          'Binary runtime','Blank startup','Any <=218 machine','Global minimality'])
print(json.dumps(result,indent=2))
