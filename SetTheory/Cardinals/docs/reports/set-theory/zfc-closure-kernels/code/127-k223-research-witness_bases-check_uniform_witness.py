#!/usr/bin/env python3
"""Independent proof-local replay, including Boolean TAUT checks; safe under -O."""
from pathlib import Path
from functools import cache
from itertools import product
import json, argparse, hashlib
ap=argparse.ArgumentParser();ap.add_argument("--tag",type=int,default=1,choices=(1,3));ap.add_argument('--symmetric',action='store_true');args=ap.parse_args()
TAG=args.tag
PTH=Path(__file__).resolve().parent
prefix='symmetric_witness' if args.symmetric else 'uniform_witness'
artifact=PTH/f'{prefix}_tag{TAG}_dag.json'
raw=json.loads(artifact.read_text())
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
def natural(x):return type(x) is int and x>=0
if raw.get('format')!='formula_dag_v1':raise ValueError('Expected formula DAG')
fs=[]
for ix,entry in enumerate(raw['formulas']):
    if not isinstance(entry,list) or len(entry)!=3:raise ValueError('Bad formula record')
    op,a,b=entry
    if op in ('rel','eq'):
        if not natural(a) or not natural(b):raise ValueError('Bad natural atom label')
        f=(op,a,b)
    elif op=='all':
        if not natural(a) or not natural(b) or b>=ix:raise ValueError('Bad quantified formula')
        f=(op,a,fs[b])
    elif op=='imp':
        if not natural(a) or not natural(b) or a>=ix or b>=ix:raise ValueError('Bad implication reference')
        f=(op,fs[a],fs[b])
    else:raise ValueError('Unknown formula constructor')
    fs.append(f)
nodes=raw['proof_nodes']
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
    if not isinstance(p,dict) or set(p)!={'rule','formula','args'}:raise ValueError('Bad proof record')
    if not natural(p['formula']) or p['formula']>=len(fs):raise ValueError('Bad formula reference')
    r=p['rule'];f=fs[p['formula']];ar=p['args'];deps=frozenset();counts[r]=counts.get(r,0)+1
    if not isinstance(ar,list):raise ValueError('Bad arguments')
    if r in ('MP','GEN'):
        if len(ar)!=2 or not all(natural(a) for a in ar):raise ValueError('Bad rule arguments')
    elif ar:raise ValueError('Leaf has arguments')
    if r=='TAUT':req(is_taut(f),(ix,'not a classical tautology',f))
    elif r=='K':req(f==I(f[1],I(f[2][1],f[1])),(ix,r))
    elif r=='S':
        a=f[1][1];b=f[1][2][1];c=f[1][2][2]
        req(f==I(I(a,I(b,c)),I(I(a,b),I(a,c))),(ix,r))
    elif r=='MP':
        l,h=ar;req(0<=l<ix and 0<=h<ix,(ix,'acyclic'))
        req(fs[nodes[l]['formula']]==I(fs[nodes[h]['formula']],f),(ix,r));deps=opens[l]|opens[h]
    elif r=='GEN':
        i,h=ar;req(0<=h<ix,(ix,'acyclic'));req(not opens[h],(ix,'GEN with hypotheses'))
        req(f==Q(i,fs[nodes[h]['formula']]),(ix,r))
    elif r=='UW':
        i=f[1][1];body=f[1][2][1];binder=body[1];d=body[2]
        if args.symmetric:
            if not (d[0]=='imp' and d[1][0]=='imp'):raise ValueError('Bad symmetric guard')
            atom=d[1][1]
        else:atom=d
        req(atom[0]=='eq' and atom[1]==i,(ix,r,'bad equality'))
        j=atom[2]
        req(d==(And(D(i,j),D(j,i)) if args.symmetric else D(i,j)),(ix,r,'bad guard'))
        expected_binder=4*((i+j)*(i+j+1)//2+j)+TAG
        req(binder==expected_binder and f==Ex(i,Q(binder,d)),(ix,r,'wrong uniform binder'))
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
        req(not args.symmetric,(ix,'Forbidden primitive symmetry'))
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
for a,b in ((0,1),(1,0),(1,1),(0,0),(2,5)):
    z=code(a,b);w=z+1
    expected[f'exists_e_{a}_{b}']=Ex(a,E(a,b))
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
def kappa(a,b):return 4*((a+b)*(a+b+1)//2+b)+TAG
def rename(f,x,y):
    if f==F:return F
    if f[0]=='rel':return R(*(y if a==x else a for a in f[1:]))
    if f[0]=='imp':return I(rename(f[1],x,y),rename(f[2],x,y))
    raise ValueError('Invalid qf rename')
for x,y in ((0,0),(0,1),(1,0)):
    f=And(I(R(x,1),R(x,kappa(x,y))),I(R(x,kappa(x,y)),R(x,1)))
    expected[f'qf_spec_collision_{x}_{y}']=I(Q(x,f),rename(f,x,y))
for i in (0,1,2):expected[f'serial_{i}']=I(Q(i,F),F)
req(set(expected)==set(raw['roots']),'Root name mismatch')
for name,r in raw['roots'].items():
    req(natural(r) and r<len(nodes),(name,'invalid root reference'))
    req(not opens[r],(name,'open root'))
    req(fs[nodes[r]['formula']]==expected[name],(name,'wrong root'))
report={'valid':True,'proof_nodes':len(nodes),'formulas':len(fs),'closed_roots':len(expected),
        'rules':counts,'max_taut_atoms':max_taut_atoms,
        'scope':'Finite instances of the documented uniform strengthened-rho1 interpretation. TAUT leaves use retained rho8/rho6 classical logic. No old rho1, primitive rho7, Eq-vacuity, alpha conversion, or substitution rule is admitted.', 'kappa_tag':TAG, 'symmetric_witness':args.symmetric, 'sha256':hashlib.sha256(artifact.read_bytes()).hexdigest()}
(PTH/f'{prefix}_tag{TAG}_receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
