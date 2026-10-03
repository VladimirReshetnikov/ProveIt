#!/usr/bin/env python3
"""Finite saved-source transfer probe only; no partition search or public compiler."""
import argparse,hashlib,json,random
from pathlib import Path
from collections import Counter
from fractions import Fraction
PINS={'complete75_asymmetric_factor_partitions.json': '6d9112e67d18306bb6aa8aaf8660432d7dff2398e198c3018907e1c79c70a42f', 'complete75_asymmetric_factor_partitions.md': '1e54eb9a8b5e704947ed78d69716c79ec2e6e46d187e700960bf1b1b700eebf2', 'complete75_asymmetric_factor_partitions.py': 'b772fc579454b13ce30e5f9feaad25206d35b04af3cb4dffb1d76d1246d4c515', 'complete75_asymmetric_linear_gap_tradeoffs.json': 'dcd2c462e8405bc4535682a624832e8a8ad044a86504fd0b46df6700ab5c0f26', 'complete75_asymmetric_linear_gap_tradeoffs.md': '93aac323a64bf6c7e8946faeddf90de5606d8c133d3bd611a0806269e8f92638', 'complete75_asymmetric_linear_gap_tradeoffs.py': 'a08626905d8a790ec1458bc8e7302b9f28e251b84818695d2fa3c640a8c9dcf2', 'complete75_asymmetric_scale_tradeoffs.json': '47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_asymmetric_scale_tradeoffs.py': 'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660', 'complete86_first_root_partitions.json': '7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5', 'complete86_first_root_partitions.md': '7325cf4fcf88bd5c20bd3d556eef7c8a313f3aee914e637483dc065d2417c2e0', 'complete86_first_root_partitions.py': 'b139097ed009580cfe8fc7707e373ec9ecafdecb886bd2cf037d615a06d35988', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45'}
CONST=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def add(a,b,s=1):
 c=a.copy()
 for m,v in b.items():c[m]=c.get(m,0)+s*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   t=tuple(x+y for x,y in zip(m,n));c[t]=c.get(t,0)+v*w
 return {m:v for m,v in c.items() if v}
def run(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b];e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e

def degree_and_finalizer(rows,out):
 defs={n:(o,a,b) for n,o,a,b in rows};factors=[n for n in FACTORS if n in defs];k=len(factors);zero=(0,)*(k+2)
 unit=lambda i:{tuple(int(j==i) for j in range(k+2)):1}
 const=lambda n:{zero:n} if n else {}
 e={};residuals={};groups=[]
 for n,o,a,b in rows:
  if n in factors:e[n]=unit(factors.index(n));continue
  if (o,a,b)==('-','ic22','R16'):e[n]=unit(k);residuals[n]=('strong',22);continue
  if o=='-' and {a,b}=={'H17','aux_u_rhs'}:e[n]=unit(k+1);residuals[n]=('linear',6);continue
  if not all(type(v)is int or v in e for v in (a,b)):continue
  aa=const(a) if type(a)is int else e[a];bb=const(b) if type(b)is int else e[b]
  e[n]=mul(aa,bb) if o=='*' else add(aa,bb,1 if o=='+' else -1)
  if o=='-' and b==1 and len(aa)==1:
   mon,c=next(iter(aa.items()))
   if c==1 and not any(mon[k:]) and all(v in (0,1) for v in mon[:k]):groups.append(tuple(i for i,v in enumerate(mon[:k]) if v))
 need(out in e,'actual complete finalizer recovered')
 allproduct=tuple([1]*k+[0,0]);pure=add({allproduct:1},const(1),-1)
 if e[out]==pure:
  kind='product_minus_one';groups=[tuple(range(k))];ret=[]
 else:
  # The selected saved forms have no nonempty anchored finalizers.
  need(groups and len(set(groups))==len(groups),'literal SOS group residuals')
  need(sorted(i for g in groups for i in g)==list(range(k)),'all factors once in actual unit groups')
  want={}
  for g in groups:
   t=tuple([int(i in g) for i in range(k)]+[0,0]);r=add({t:1},const(1),-1);want=add(want,mul(r,r))
  ret=[]
  for label,index,deg in [('strong',k,22),('linear',k+1,6)]:
   u=mul(unit(index),unit(index))
   mon=next(iter(u))
   if e[out].get(mon)==1:want=add(want,u);ret.append((label,deg))
  need(want==e[out],'complete actual SOS equals unit groups plus retained comparison squares')
  kind='sum_of_squares'
 normalized=defs.get('strong_difference')==('*','A','ic22')
 firstroot=defs['tau_square']==('*','tau_root','tau_root')
 linearinput=defs['index_product']==('*','delta','a_plus_one')
 gap=defs.get('y_aux')==('+','aux_u_rhs','aux_gap')
 coupled=defs.get('norm_linear')==('+','linear_difference','index_difference')
 allweights=[22 if firstroot else 12,18,20 if linearinput else 32,56 if normalized else 20 if gap else 24,7,2,34 if normalized else 22,7 if coupled else 6]
 weights=[allweights[FACTORS.index(n)] for n in factors];gd=[sum(weights[i] for i in g) for g in groups]
 degree=sum(weights) if kind=='product_minus_one' else 2*max(gd+[d for n,d in ret])
 return dict(factors=factors,factor_degrees=weights,groups=[list(g) for g in groups],group_degrees=gd,retained_residual_degrees=[d for n,d in ret],finalizer=kind,exact_degree=degree,first_root=firstroot,linear_input=linearinput,auxiliary_gap=gap,coupled_linear=coupled)

def dense(rows,values,p):
 def plus(a,b,s):
  c=[((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%p for i in range(max(len(a),len(b)))];
  while len(c)>1 and not c[-1]:c.pop()
  return c
 def times(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
  while len(c)>1 and not c[-1]:c.pop()
  return c
 e=dict(values)
 for n,o,a,b in rows:
  a=[a%p] if type(a)is int else e[a];b=[b%p] if type(b)is int else e[b];e[n]=times(a,b) if o=='*' else plus(a,b,1 if o=='+' else -1)
 return e

def local_identity():
 zero=(0,)*6
 unit=lambda i:{tuple(int(j==i) for j in range(6)):1}
 r,w,K,C,t,U=[unit(i) for i in range(6)]
 q=add(r,{zero:1});z=add(t,mul(w,C))
 left=add(add(mul(add(K,mul(w,q)),C),U),mul(z,r),-1)
 right=add(add(mul(add(K,w),C),U),mul(t,r),-1)
 need(left==right and len(right)==4,'complete local shear coefficient identity')
 return len(right)

def verify(root,shear):
 need(local_identity()==4,'local identity')
 pins={}
 stems=['complete86_first_root_partitions','complete75_asymmetric_factor_partitions','complete75_asymmetric_linear_gap_tradeoffs','complete75_asymmetric_scale_tradeoffs']
 for stem in stems+['complete86_transport_quotient_shear']:
  path=shear if stem=='complete86_transport_quotient_shear' else root
  for ext in ('py','json','md'):
   name=stem+'.'+ext;pins[name]=sha((path/name).read_bytes());need(pins[name]==PINS[name],'authenticated predecessor '+name)
 a=json.loads((root/(stems[0]+'.json')).read_text());b=json.loads((root/(stems[1]+'.json')).read_text());c=json.loads((root/(stems[2]+'.json')).read_text())
 need(len(a['frontier_sources'])==13 and len(a['winner_ledgers'])==101 and len(b['emitted'])==5 and len(c['emitted'])==10 and len(c['direct_transfers'])==11,'bounded saved-source inventory')
 items=[]
 for family,entries in [('first_root_saved',a['frontier_sources']),('older_asymmetric_saved',b['emitted']),('older_linear_gap_saved',c['emitted']),('older_linear_gap_direct',c['direct_transfers'])]:
  for i,f in enumerate(entries):
   rows=f.get('source',f.get('polynomial_source'));olddegree=f.get('exact_degree',f.get('degree_certificate',{}).get('exact_degree'))
   if olddegree is None:
    matching=[d['degree'] for d in c['degree_audit'] if d['mode']=='direct' and d['name']==f['name']];need(matching and len(set(matching))==1,'direct source degree receipt');olddegree=matching[0]
   items.append((family,i,f.get('name',f.get('kind',f.get('base',{}).get('kind'))),rows,f['output'],olddegree))
 forms=[];counts=Counter();rng=random.Random(178134122112108)
 for family,index,label,old,out,olddegree in items:
  d={n:(o,a,b) for n,o,a,b in old}
  required={'repunit':('*','Bm1','Jrep'),'q':('+','repunit',1),'wn2':('*','w','q'),'kinner':('+','Kconstant','wn2'),'innerC':('*','kinner','marked_rhs'),'transport_partial':('+','innerC','q_minus_F'),'local_rhs':('*','zplus','repunit'),'norm_transport':('-','transport_partial','local_rhs'),'q_minus_F':('-','q','F'),'q_minus_FZ':('-','q_minus_F','Z'),'C_after_alpha':('-','q_minus_FZ','alpha'),'scaled_t':('*','twice_cell_bits','x'),'marked_rhs':('-','C_after_alpha','scaled_t')}
  need(all(d.get(n)==v for n,v in required.items()),'literal asymmetric transport and positive-content definitions')
  need([n for n,o,a,b in old if 'zplus' in (a,b)]==['local_rhs'],'sole old quotient consumer')
  need([n for n,o,a,b in old if 'kinner' in (a,b)]==['innerC'],'sole coefficient consumer')
  new=[[n,o,('transport_quotient' if a=='zplus' else a),('w' if n=='kinner' else 'transport_quotient' if b=='zplus' else b)] for n,o,a,b in old]
  defs={n for n,o,a,b in new};free=sorted({v for row in new for v in row[2:] if type(v)is str}-defs);w=[v for v in free if v not in CONST+['x']]
  need(len(w)==19 and set(CONST+['x'])<=set(free),'exact nineteen-witness ordinary-input interface')
  # Recount closure, all source liveness and raw syntactic upper degree.
  seen=set(free);deg={v:0 if v in CONST else 1 for v in free};deps={};M=0
  for n,o,a,b in new:
   need(n not in seen and all(type(v)is int or v in seen for v in (a,b)),'literal closure');ds=[0 if type(v)is int else deg[v] for v in (a,b)];deg[n]=sum(ds) if o=='*' else max(ds);seen.add(n);deps[n]=(a,b);M+=o=='*'
  live=set();todo=[out]
  while todo:
   n=todo.pop()
   if type(n)is int or n in live:continue
   live.add(n);todo.extend(deps.get(n,()))
  need(live==set(deps)|set(free),'all literal gates and supplied ports live')
  # Same proved local shear cut, compare every retained factor and full output.
  ids={}
  def iid(t):
   if t not in ids:ids[t]=len(ids)
   return ids[t]
  def structural(rows):
   env={v:iid(('free',v)) for v in free+['zplus']}
   for n,o,a,b in rows:
    at=lambda v:iid(('int',v)) if type(v)is int else env[v]
    env[n]=iid(('proved_transport_identity',)) if n=='norm_transport' else iid((o,at(a),at(b)))
   return env
  aa=structural(old);bb=structural(new)
  for n in FACTORS:
   if n in d:need(aa[n]==bb[n],'each complete factor cut');counts['unchanged_factor_or_transport_identities']+=1
  need(aa[out]==bb[out],'entire source/finalizer graph identity');counts['complete_graph_identities']+=1
  cert=degree_and_finalizer(new,out);counts['literal_finalizer_unit_proofs']+=1
  oldweights=cert['factor_degrees'][:];oldweights[cert['factors'].index('norm_transport')]=3
  oldgroups=[sum(oldweights[i] for i in g) for g in cert['groups']]
  predictedold=sum(oldweights) if cert['finalizer']=='product_minus_one' else 2*max(oldgroups+cert['retained_residual_degrees'])
  need(olddegree==predictedold,'parent exact degree and actual group identification')
  degree_checks=[]
  for B,prime in [(16,1009),(32,1013)]:
   fixed=dict(Bm1=B-1,Kconstant=3+5*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3)
   for attempt in range(4):
    ev={n:[j+1,(j+2)*(attempt+1)+1] for j,n in enumerate(w+['x'])};ev.update({n:[v] for n,v in fixed.items()});polys=dense(new,ev,prime)
    if len(polys[out])-1==cert['exact_degree'] and all(len(polys[n])-1==dd for n,dd in zip(cert['factors'],cert['factor_degrees'])):break
   else:raise ValueError('attained degree slice not found')
   need(polys[out][-1]!=0,'exact full lower-degree witness')
   degree_checks.append(dict(B=B,prime=prime,affine_substitution=ev,exact_degree=len(polys[out])-1,leading_coefficient=polys[out][-1],full_polynomial_coefficients_sha256=sha(json.dumps(polys[out]).encode())));counts['complete_degree_attainments']+=1
  for i in range(8):
   v={n:rng.randrange(-3,4) for n in free}
   if i>=6:v={n:Fraction(k,3) for n,k in v.items()};counts['rational_cases']+=1
   C=v['Bm1']*v['Jrep']+1-v['F']-v['Z']-v['alpha']-v['twice_cell_bits']*v['x'];pv=v.copy();pv['zplus']=pv.pop('transport_quotient')+v['w']*C
   x=run(old,pv);y=run(new,v);need(x[out]==y[out],'complete numeric pullback');counts['complete_numeric_pullbacks']+=1
  forms.append(dict(family=family,index=index,label=label,source=new,output=out,witnesses=w,fixed_numerals=CONST,ordinary_input='x',operations=len(new),M=M,A=len(new)-M,parent_degree=olddegree,degree=cert['exact_degree'],raw_syntactic_upper_degree=deg[out],degree_proof=cert,degree_checks=degree_checks,parent_complete_source_sha256=sha(json.dumps(old,separators=(',',':')).encode())))
 # Nondominance only of these39 saved schedules, no re-enumeration or new plans.
 points=sorted({(f['operations'],f['degree']) for f in forms});frontier=[p for p in points if not any(q!=p and q[0]<=p[0] and q[1]<=p[1] for q in points)]
 return dict(status='PASS_BOUNDED_SAVED_SOURCE_PROBE',source_sha256=sha(Path(__file__).read_bytes()),observed_pins=pins,counts=dict(counts),forms=forms,saved_schedule_frontier=frontier,scope='Only13 saved first-root frontier circuits,5 older asymmetric grouped circuits,10 older linear/gap grouped circuits and11 asymmetric direct circuits. No101-winner reconstruction, partition census, public compiler or maintained frontier promotion.')
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--shear',type=Path,default=Path('/tmp'));ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.shear)
 if a.expect:need(json.dumps(r,sort_keys=True)==json.dumps(json.loads(a.expect.read_text()),sort_keys=True),'exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts']);print('SAVED FRONTIER',r['saved_schedule_frontier'])
 for f in r['forms']:print(f['family'],f['index'],f['label'],f['operations'],str(f['parent_degree'])+'->'+str(f['degree']))
