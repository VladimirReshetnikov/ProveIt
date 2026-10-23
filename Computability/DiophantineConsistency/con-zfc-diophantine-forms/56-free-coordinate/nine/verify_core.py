#!/usr/bin/env python3
from pathlib import Path
import json,random,hashlib
from math import prod
from functools import reduce

class Poly:
    def __init__(self,d=None):self.d={k:v for k,v in (d or {}).items() if v}
    @classmethod
    def constant(cls,n):return cls({():n})
    @classmethod
    def variable(cls,s):return cls({(s,):1})
    def __add__(self,z):
        if not isinstance(z,Poly):z=Poly.constant(z)
        d=self.d.copy()
        for k,v in z.d.items():d[k]=d.get(k,0)+v
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
    def __sub__(self,z):return self+(-z)
    def __rsub__(self,z):return -self+z
    def __mul__(self,z):
        if not isinstance(z,Poly):z=Poly.constant(z)
        d={}
        for a,x in self.d.items():
            for b,y in z.d.items():
                k=tuple(sorted(a+b));d[k]=d.get(k,0)+x*y
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        r=Poly.constant(1)
        for _ in range(n):r=r*self
        return r
    def __eq__(self,z):return self.d==(z.d if isinstance(z,Poly) else Poly.constant(z).d)

def symbols(s):return [Poly.variable(x) for x in s.split()]
import build as b
from circuit import evaluate
ROOT=Path(__file__).resolve().parent

def require(q,msg):
    if not q: raise RuntimeError(msg)

def fixed_values(body,ports,p):
    out={'base_scale':pow(2,body['base_scale_exponent'],p),'threshold_scale':pow(2,body['threshold_scale_exponent'],p)}
    for rec in body['coefficient_recipes']:
        out[rec['name']]=sum(t['coefficient']*prod(pow(x,e,p) for x,e in zip(ports,t['powers'])) for t in rec['terms'])%p
    return out

# Completely symbolic source row comparison, keeping all35 symbols free.
source=json.loads((ROOT/'upstream/upstream_parent_quartic31.json').read_text())
raw=json.loads((ROOT/'upstream/source60.json').read_text())
syms=symbols(' '.join(source['sparse_term_coordinate_order']))
env=dict(zip(source['sparse_term_coordinate_order'],syms));env0=env.copy()
get=lambda x:Poly.constant(x) if isinstance(x,int) else env[x]
for name,op,aa,bb in raw['source']:
    aa,bb=get(aa),get(bb);env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
symbolic_rows=0
for i,((aa,bb),row) in enumerate(zip(raw['comparisons'],source['equations']),1):
    left=get(aa)-get(bb)
    if i==15:left+=env0['beta']*env0['J']
    right=sum(t['coefficient']*prod(v**e for v,e in zip(syms,t['powers'])) for t in row['terms'])
    require(left-right==0,f'homogeneous original source row {i}')
    symbolic_rows+=1

# Independently reconstruct the shifted weighted source and all isolation tests.
from itertools import combinations_with_replacement
from collections import defaultdict
ports_names=source['constants'];var_names=source['variables'];shifted={name:Poly.variable(name)+1 for name in var_names};shifted.update({name:Poly.variable(name) for name in ports_names})
blocks={}
for row in source['equations']:
    poly=sum(t['coefficient']*prod(shifted[name]**e for name,e in zip(source['sparse_term_coordinate_order'],t['powers'])) for t in row['terms'])
    entries=defaultdict(dict)
    for mon,co in poly.d.items():
        ids=sorted(var_names.index(name)+1 for name in mon if name in var_names)
        require(len(ids)<=2,'source is not quadratic')
        pair=tuple([0]*(2-len(ids))+ids)
        powers=tuple(mon.count(name) for name in ports_names)
        entries[pair][powers]=co*(2 if pair[0]==pair[1] else 1)
    blocks[row['number']]=dict(entries)
require(blocks==b.shifted_source(source),'independent weighted shift differs')
code=json.loads((ROOT/'upstream/code_v1.json').read_text());weights=code['weights'];targets=dict(zip(code['order'],code['targets']));target_set=set(targets.values());pairs=list(combinations_with_replacement(range(32),2));hits=0;checks=0;encodings=[]
for ri,terms in blocks.items():
    for alpha,co in terms.items():
        e=targets[ri]-sum(weights[i] for i in alpha);require(e>=0,'negative code exponent');encodings.append(e)
        for beta in pairs:
            lands=e+sum(weights[i] for i in beta);is_hit=lands in target_set
            require(is_hit==(beta==alpha),'target contamination')
            if is_hit:require(lands==targets[ri],'wrong target row');hits+=1
            checks+=1
require(len(encodings)==136 and len(set(encodings))==136,'coefficient collision')
require(hits==136 and checks==71808,'interaction count')
require(max(encodings)==5190,'leading exponent')
leading=[co for ri,ts in blocks.items() for pair,co in ts.items() if targets[ri]-sum(weights[i] for i in pair)==5190]
require(leading==[{(0,0,0,0):2}],'positive leading code coefficient')

# Generic two-block/popcount identity and exact threshold calibration, including b=1.
carry_cases=0
for u0 in range(1,8):
    L0=1<<u0
    for S0 in range(L0):
        for T0 in range(L0-S0):
            R0=(S0+T0)*L0+L0-1-S0
            loss=S0.bit_count()+T0.bit_count()-(S0+T0).bit_count()
            require(R0.bit_count()==u0+T0.bit_count()-loss,'top-bit-free valuation identity')
            require((R0.bit_count()>=u0+T0.bit_count())==((S0&T0)==0),'carry test')
            carry_cases+=1
for k in range(33):
    v=b.KAPPA+2*k;u=k+5741*v;popT=206*v-31*k-22
    Nexp=(15*b.KAPPA//2-11)+2966*v
    require(u+popT==2*Nexp,'square threshold calibration')

rng=random.Random(20261023);evaluations=0;certificates={}

for absorb in [False,True]:
  for positive in [False,True]:
    main=b.build(positive,False,'calibrated',absorb,'hybrid')
    direct=b.build(positive,False,'calibrated',absorb,'direct')
    cert=b.build(positive,True,'calibrated',absorb,'direct')
    ledger=b.degree_certificate(cert)
    require(ledger['exact_degree']==4686812,'exact degree')
    for p in [101,1009,1000003]:
      for z in range(100):
        ports=[rng.randrange(p) for _ in range(4)]
        vals={v:rng.randrange(p) for v in main['variables']}
        outputs=[];named=[]
        for obj in [main,direct,cert]:
          out,names=evaluate(obj,fixed_values(obj,ports,p),vals,p)
          outputs.append(out);named.append(names)
        require(outputs[0]==outputs[1]==outputs[2],f'full circuit mismatch {absorb} {positive} {p} {z}')
        require(named[0]['Dcode']==named[1]['Dcode']==named[2]['Dcode'],'source evaluator mismatch')
        evaluations+=1
    certificates[f'{absorb}_{positive}']={'degree':ledger['exact_degree'],'operations':main['total_operations'],'leader':ledger['diagonal_leading_coefficient']}

# Independent upper-degree and actual-coefficient leading-form replay.
from materialize import load_ports
actual_ports=load_ports();degree_modular=[]
cert=b.build(True,True,'calibrated',True,'direct')
for p0 in [101,1009,1000003]:
    fixed=fixed_values(cert,[x%p0 for x in actual_ports],p0);degrees=[];heads=[]
    for node in cert['nodes']:
        kind=node['kind']
        if kind=='variable':dg,head=1,1
        elif kind=='literal':dg,head=0,node['value']%p0
        elif kind=='fixed':dg,head=0,fixed[node['name']]
        else:
            l,r=node['left'],node['right'];dl,dr=degrees[l],degrees[r];hl,hr=heads[l],heads[r]
            if kind=='mul':dg,head=dl+dr,hl*hr%p0
            elif dl>dr:dg,head=dl,hl
            elif dr>dl:dg,head=dr,hr if kind=='add' else -hr%p0
            else:dg,head=dl,(hl+hr if kind=='add' else hl-hr)%p0
        degrees.append(dg);heads.append(head)
    a=fixed['base_scale'];cstar=fixed['threshold_scale']
    expected=pow(2,94,p0)*pow(a,2343092,p0)*pow(a+4,104,p0)*pow(cstar,400,p0)%p0
    require(degrees[cert['output']]==4686812,'independent degree upper bound')
    require(heads[cert['output']]==expected and expected!=0,'independent nonzero leading coefficient')
    degree_modular.append({'prime':p0,'degree':degrees[cert['output']],'diagonal_leading_residue':expected})

# Universal norm and Pell approximation identities checked symbolically.
t,D,G,H=symbols('t D G H'); DF=t*t*D**3*(D-1)+D;S=t*(8*D*D-4*D-1)
require(S*S-64*DF-(t*t*(8*D+1)-64*D)==0,'majorant defect')
I=(G*G-1)*H*H+1
require((S*G*H)**2-64*DF*I-((t*t*(8*D+1)-64*D)*(G*H)**2+64*DF*(H*H-1))==0,'radical majorant defect')
E,O,V0,V1,K,dv=symbols('E O V0 V1 K dv')
a0=V0*V0-(K*K-1);a1=V1*V1-dv
raw=(E-O*(V0+V1))**2-O**2*(a0+a1)
resolved=E**2-2*E*O*(V0+V1)+O**2*((K*K-1)+dv+2*V0*V1)
require(raw-resolved==0,'norm leading cancellation')

# Every primary node live and topologically ordered, no hidden input.
for absorb in [False,True]:
 obj=b.build(True,False,'calibrated',absorb,'hybrid');nodes=obj['nodes'];live=set();todo=[obj['output']]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i);n=nodes[i]
  if n['kind'] in ('add','sub','mul'):
   require(n['left']<i and n['right']<i,'non-DAG dependency');todo.extend([n['left'],n['right']])
 require(len(live)==len(nodes),'dead nodes')
 require(sum(n['kind'] in ('add','sub','mul') for n in nodes)==obj['total_operations'],'operation count')
 require({n['name'] for n in nodes if n['kind']=='variable'}==set(b.POSITIVE),'missing or hidden variable')
receipt={'symbolic_source_rows':symbolic_rows,'extraction_interactions':checks,'carry_identity_cases':carry_cases,'threshold_cases':33,'full_modular_evaluations':evaluations,'moduli':[101,1009,1000003],'identities':3,'independent_actual_degree_checks':degree_modular,'circuits':certificates,'scope':'Exact symbolic row and norm identities, exact degree and liveness checks; finite modular replays are diagnostics, not an unbounded solvability proof.'}
(ROOT/'generated/CANDIDATE_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'symbolic_source_rows':symbolic_rows,'extraction_interactions':checks,'carry_identity_cases':carry_cases,'modular_checks':evaluations,'circuits':{k:{'degree':v['degree'],'ops':v['operations']} for k,v in certificates.items()}},indent=2))
