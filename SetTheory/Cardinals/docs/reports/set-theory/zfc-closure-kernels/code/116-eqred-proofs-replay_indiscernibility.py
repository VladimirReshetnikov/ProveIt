#!/usr/bin/env python3
"""Independent proof-local replay, including Boolean TAUT checks; safe under -O."""
from pathlib import Path
from functools import cache
from itertools import product
import json
PTH=Path(__file__).resolve().parent
raw=json.loads((PTH/'indiscernibility_proofs.json').read_text())
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
fs=list(map(tup,raw['formulas']));nodes=raw['proof_nodes']
F=('rel',0,0)
I=lambda p,q:('imp',p,q)
Q=lambda i,p:('all',i,p)
N=lambda p:I(p,F)
Ex=lambda i,p:N(Q(i,N(p)))
R=lambda a,b:('rel',a,b)
D=lambda a,b:('eq',a,b)
And=lambda p,q:N(I(p,N(q)))
def req(b,msg):
    if not b:raise ValueError(msg)
@cache
def atoms(f):
    if f==F:return frozenset()
    if f[0]=='imp':return atoms(f[1])|atoms(f[2])
    return frozenset((f,))
max_taut_atoms=0
@cache
def is_taut(f):
    global max_taut_atoms
    vs=sorted(atoms(f),key=repr);k=len(vs);max_taut_atoms=max(max_taut_atoms,k)
    req(k<=20,('unexpectedly large Boolean verification',k))
    n=1<<k;full=(1<<n)-1;valuation={}
    for i,a in enumerate(vs):
        block=1<<i
        repeat=full//((1<<(2*block))-1)
        valuation[a]=repeat*(((1<<block)-1)<<block)
    @cache
    def ev(p):
        if p==F:return 0
        if p[0]=='imp':return (~ev(p[1])|ev(p[2]))&full
        return valuation[p]
    return ev(f)==full

opens=[];counts={}
for ix,p in enumerate(nodes):
    r=p['rule'];f=fs[p['formula']];ar=p['args'];deps=frozenset();counts[r]=counts.get(r,0)+1
    if r=='TAUT':req(is_taut(f),(ix,'not a classical tautology',f))
    elif r=='K':req(f==I(f[1],I(f[2][1],f[1])),(ix,r))
    elif r=='S':
        a=f[1][1];b=f[1][2][1];c=f[1][2][2]
        req(f==I(I(a,I(b,c)),I(I(a,b),I(a,c))),(ix,r))
    elif r=='MP':
        l,h=ar;req(l<ix and h<ix,(ix,'acyclic'))
        req(fs[nodes[l]['formula']]==I(fs[nodes[h]['formula']],f),(ix,r));deps=opens[l]|opens[h]
    elif r=='GEN':
        i,h=ar;req(h<ix,(ix,'acyclic'));req(not opens[h],(ix,'GEN with hypotheses'))
        req(f==Q(i,fs[nodes[h]['formula']]),(ix,r))
    elif r=='rho1':
        i=f[1][1];d=f[1][2][1]
        req(d[0]=='eq' and d[1]==i and f==Ex(i,d),(ix,r))
    elif r=='rho2':
        i=f[1][1];a=f[1][2][1];b=f[1][2][2]
        req(f==I(Q(i,I(a,b)),I(Q(i,a),Q(i,b))),(ix,r))
    elif r=='rho4':
        i=f[1][1];j=f[1][2][1];a=f[1][2][2]
        req(f==I(Q(i,Q(j,a)),Q(j,Q(i,a))),(ix,r))
    elif r=='rho6':
        i=f[1][1][1];a=f[2]
        req(f==I(Ex(i,Q(i,a)),a),(ix,r))
    elif r=='SYM':
        a,b=f[1][1:];req(f==I(D(a,b),D(b,a)),(ix,r))
    elif r=='rho3':
        a,b=f[1][1:];c=f[2][1][1]
        req(f==I(D(a,b),I(R(c,a),R(c,b))),(ix,r))
    elif r=='rho5':
        a,b=f[1][1:];c=f[2][1][2]
        req(f==I(D(a,b),I(R(a,c),R(b,c))),(ix,r))
    elif r=='vacRel':
        a,b=f[1][1:];i=f[2][1]
        req(i!=a and i!=b and f==I(R(a,b),Q(i,R(a,b))),(ix,r))
    elif r=='HYP':deps=frozenset((f,))
    else:raise ValueError(('Forbidden or unknown rule',r))
    opens.append(deps)

def code(a,b):return 4*((a+b)*(a+b+1)//2+b)+3
def body(a,b,z,o=False):
    p,q=(R(a,z),R(b,z)) if o else (R(z,a),R(z,b))
    return And(I(p,q),I(q,p))
def Ez(a,b,z):return And(Q(z,body(a,b,z)),Q(z,body(a,b,z,True)))
def E(a,b):return Ez(a,b,code(a,b))
expected={}
for a,b in ((0,1),(1,0),(1,1),(0,0)):
    z=code(a,b);w=z+1
    expected[f'aux_{a}_{b}']=I(Ez(a,b,z),Ez(a,b,w))
    expected[f'aux_reverse_{a}_{b}']=I(Ez(a,b,w),Ez(a,b,z))
    expected[f'vac_internal_{a}_{b}']=I(E(a,b),Q(z,E(a,b)))
    expected[f'vac_external_{a}_{b}']=I(E(a,b),Q(w,E(a,b)))
    for c in (0,1,z):
        expected[f'rel_in_{a}_{b}_{c}']=I(E(a,b),I(R(c,a),R(c,b)))
        expected[f'rel_out_{a}_{b}_{c}']=I(E(a,b),I(R(a,c),R(b,c)))
for a,b,c in product(range(2),repeat=3):expected[f'e_rho7_{a}_{b}_{c}']=I(E(c,a),I(E(c,b),E(a,b)))
expected['e_rho7_distinct']=I(E(2,0),I(E(2,1),E(0,1)))
expected['e_refl_zero']=E(0,0)
f=And(I(R(0,1),R(0,2)),I(R(0,2),R(0,1)))
expected['qf_self_example']=I(Q(0,f),f)
req(set(expected)==set(raw['roots']),'Root name mismatch')
for name,r in raw['roots'].items():
    req(not opens[r],(name,'open root'))
    req(fs[nodes[r]['formula']]==expected[name],(name,'wrong root'))
report={'valid':True,'proof_nodes':len(nodes),'formulas':len(fs),'closed_roots':len(expected),
        'rules':counts,'max_taut_atoms':max_taut_atoms,
        'scope':'Uniform arbitrary-label proof construction documented separately; finite numerical certificates include coincident parameters, coordinate 0, and internal-binder equality vacuity. TAUT leaves are independently Boolean-checked and depend on the previously proved canonical-V classical bridge. No primitive rho7 or equality vacuity is used.'}
(PTH/'indiscernibility_replay_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
