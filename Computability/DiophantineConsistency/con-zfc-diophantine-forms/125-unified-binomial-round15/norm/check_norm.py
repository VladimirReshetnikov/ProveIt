#!/usr/bin/env python3
"""Exact owned norm identity, full byte binding and actual-DAG degree audit."""
import json,hashlib,gzip,itertools
from pathlib import Path
from collections import Counter
import sympy as sp
ROOT=Path(__file__).resolve().parent
OPS=['add','sub','mul'];VARS=['j','C','z','h','r','v','w','T','c','n','s'];PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def need(x,msg):
 if not x:raise ValueError(msg)
def norm_identity():
 z,A,B,G=sp.symbols('z A B G');rs=[A,B,G];acc={0:sp.Integer(1)}
 for signs in itertools.product([-1,1],repeat=3):
  fac={0:z,1:-signs[0],2:-signs[1],4:-signs[2]};out={}
  for i,x in acc.items():
   for j,y in fac.items():
    t=x*y
    for k,r in enumerate(rs):
     if (i&j)&(1<<k):t*=r
    out[i^j]=out.get(i^j,0)+t
  acc={k:sp.expand(v) for k,v in out.items() if sp.expand(v)!=0}
 symmetric=((z*z-A-B-G)**2-4*(A*B+A*G+B*G))**2-64*A*B*G*z*z
 paired=((z*z+A-B-G)**2-4*(A*z*z+B*G))**2-64*(A*z*z)*(B*G)
 need(set(acc)=={0},'all radical basis coefficients vanish')
 need(sp.expand(acc[0]-symmetric)==0,'full sign product matches symmetric norm')
 need(sp.expand(paired-symmetric)==0,'paired equals symmetric polynomial')
 need(len(sp.Poly(sp.expand(paired),z,A,B,G).terms())==35,'all 35 coefficients')
 S,Q,V,W=sp.symbols('S Q V W');delta=Q-1;Cy=Q*V*V-1
 Z=W+S*Q*V;B=S*S*delta*Cy
 omega=W*W+2*S*Q*V*W+S*S*(Q*(V*V+1)-1)
 need(sp.expand(Z*Z-B-omega)==0,'full centering cancellation')
 Budget,Dt,s=sp.symbols('Budget Dt s')
 weighted=(243*Budget-324)*Dt*s*s+81
 ordinary=81*(1+(3*Budget-4)*Dt*s*s)
 need(sp.expand(weighted-ordinary)==0,'full weighted guard identity')
 return dict(full_sign_product=True,paired_symmetric_identity=True,coefficients=35,center_cut=True,weighted_guard_identity=True)
def binding():
 b=json.loads((ROOT/'coefficients/BINDING.json').read_text());out={};vals={}
 for name in PORTS:
  p=b['payloads'][name];blob=(ROOT/'coefficients'/p['file']).read_bytes();raw=gzip.decompress(blob)
  need(hashlib.sha256(raw).hexdigest()==p['raw_sha256'],'full payload hash '+name)
  value=int.from_bytes(raw,'little');need(value.bit_length()==p['bits'],'payload bits '+name);need(len(raw)==p['raw_bytes'],'payload bytes '+name)
  vals[name]=value;out[name]={**p,'compressed_sha256':hashlib.sha256(blob).hexdigest()}
 need(vals['beta']==2**1064921-1,'beta full equality');need(vals['cone_A']==2**1113 and vals['cone_B']==2**666104,'cone full equalities')
 return dict(tuple=b['tuple'],source_commit=b['source_commit'],MF_convention=b['MF_convention'],payloads=out)
def actual_degree(p):
 # Graded lexicographic order, C before all other variables, selects the
 # displayed C^4 endpoint in the top homogeneous form. beta is a coefficient.
 order=['C','z','j','w','v','h','s','r','c','T','n'];beta=sp.Symbol('beta');zero=(0,)*11
 vals=[];degs=[];nm=p['named_registers'];nodes=p['nodes'];override=None
 if p['description']['center']:
  vr=nodes[nm['vnorm']];need(vr[0]=='sub' and vr[2]==nm['G'],'vnorm subtracts G')
  override=vr[1];rr=nodes[override]
  if p['description']['norm_schedule']=='paired':
   need(rr[0]=='sub' and rr[2]==nm['B'],'paired canceled subnode');need(nodes[rr[1]]==['add',min(nm['Z2'],nm['A']),max(nm['Z2'],nm['A'])],'paired canceled addnode')
  else:need(rr==['sub',nm['Z2'],nm['AB']],'symmetric canceled node')
 def times(a,b):return (tuple(x+y for x,y in zip(a[0],b[0])),sp.expand(a[1]*b[1]))
 def key(a):return(sum(a[0]),)+a[0]
 def plus(a,b,sub=False):
  if key(a)>key(b):return a
  if key(a)<key(b):return(b[0],-b[1] if sub else b[1])
  return(a[0],sp.expand(a[1]-b[1] if sub else a[1]+b[1]))
 for i,row in enumerate(nodes):
  if i==override:
   # Exact identity proves Z²-B = W²+2SQVW+S²(Q(V²+1)-1),
   # deg W=35, deg SQV=61, so the unique top degree96 term is
   # -2SQV Ac. A has degree34 and does not affect this value.
   v=times((zero,sp.Integer(-2)),times(times(vals[nm['S']],times(vals[nm['Q']],vals[nm['V']])),vals[nm['Ac']]))
   degree=96;need(sum(v[0])==96,'attained exact degree of canceled node')
  elif row[0]=='variable':
   mon=[0]*11;mon[order.index(row[1])]=1;v=(tuple(mon),sp.Integer(1));degree=1
  elif row[0]=='coefficient':v=(zero,sp.Symbol(row[1]));degree=0
  elif row[0]=='integer':v=(zero,sp.Integer(row[1]));degree=0
  else:
   a,b=vals[row[1]],vals[row[2]];v=times(a,b) if row[0]=='mul' else plus(a,b,row[0]=='sub')
   degree=degs[row[1]]+degs[row[2]] if row[0]=='mul' else max(degs[row[1]],degs[row[2]])
  need(v[1]!=0,'nonzero actual leading coefficient at node '+str(i));need(sum(v[0])==degree,'exact graph degree at node '+str(i))
  vals.append(v);degs.append(degree)
 out=vals[p['output']];degree=degs[p['output']]
 wanted=464 if p['description']['center'] else 488
 need(degree==wanted==p['exact_degree'],'exact declared output degree')
 coeff=sp.factor(out[1]);coefficient={str(k):int(v) for k,v in sp.factorint(int(coeff.subs(beta,1))).items()};beta_power=int(sp.degree(coeff,beta))
 if p['description']['center']:
  need(coeff==2**460*3**326*beta**260,'authentic nonzero coefficient')
  want={'j':260,'w':56,'v':64,'C':4,'s':12,'r':24,'c':32,'h':12};need(dict((n,e) for n,e in zip(order,out[0]) if e)==want,'attaining monomial')
 return dict(exact_degree=degree,monomial=dict((n,e) for n,e in zip(order,out[0]) if e),coefficient_factors={**coefficient,'beta':beta_power},coefficient_nonzero_for_authentic_beta=True,cancellation_node=override,live_nodes=len(nodes),register_degrees={k:degs[i] for k,i in nm.items()})
def topology(p):
 nodes=p['nodes'];live=set();todo=[p['output']]
 for i,r in enumerate(nodes):
  if r[0] in OPS:need(len(r)==3 and all(type(j)==int and 0<=j<i for j in r[1:]),'binary acyclic gate')
  else:need(r[0] in ['integer','variable','coefficient'],'allowed leaf')
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i);r=nodes[i]
  if r[0] in OPS:todo.extend(r[1:])
 need(len(live)==len(nodes),'every node live');need([r[1] for r in nodes if r[0]=='variable']==VARS,'exact signed variable domains');need([r[1] for r in nodes if r[0]=='coefficient']==PORTS,'all six ports')
 counts=dict(Counter(r[0] for r in nodes if r[0] in OPS));need(counts==p['operation_counts'],'operation kinds');need(sum(counts.values())==p['operations'],'operation count')
 return dict(operation_counts=counts,operations=p['operations'],all_nodes_live=True,all_six_ports_bound=True)
if __name__=='__main__':
 result=dict(status='PASS',universal=norm_identity(),binding=binding(),equations=[])
 for name in ['integral_direct_paired','integral_centered_paired']:
  p=json.loads((ROOT/(name+'.json')).read_text());result['equations'].append(dict(name=name,topology=topology(p),degree=actual_degree(p),sha256=hashlib.sha256((ROOT/(name+'.json')).read_bytes()).hexdigest()))
 (ROOT/('CHECK.json' if __debug__ else 'CHECK_OPTIMIZED.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','universal']}));print([(e['name'],e['topology']['operations'],e['degree']['exact_degree']) for e in result['equations']])
