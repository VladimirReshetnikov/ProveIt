#!/usr/bin/env python3
"""Literal one-addition time-free-height proposal and complete false-clock proof audit.
Research CLI only; no maintained unsafe compiler API or universal claim.
"""
import argparse,copy,hashlib,json,random,sys
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'native_pell_factored_first_coefficient.json': 'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf',
 'native_pell_factored_first_coefficient.md': 'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528',
 'native_pell_factored_first_coefficient.py': 'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc',
 'residue_affine_packed_history.json': 'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421',
 'residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882',
 'residue_affine_packed_history.py': 'd06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4',
 'three_mass_target_free_height.json': 'a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830',
 'three_mass_target_free_height.md': '61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a',
 'three_mass_target_free_height.py': '7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49',
 'three_mass_unbounded_endpoint_projection.json': 'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457',
 'three_mass_unbounded_endpoint_projection.md': '8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c',
 'three_mass_unbounded_endpoint_projection.py': '96d41f43190547fce121c5271e351af3d2bc99fa2226379e4d24f980bae998dd',
 'three_mass_unbounded_interface.json': 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e',
 'three_mass_unbounded_interface.md': 'd336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45',
 'three_mass_unbounded_interface.py': 'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a'}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def pins(root,manifest):
 out={}
 for n,h in manifest.items():
  b=(Path(root)/n).read_bytes();need(sha(b)==h,'Pinned blob '+n);out[n]=b
 return out
def numeric(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return e

def ledger(rows,free,outputs):
 known=set(free);defs={};degree={x:1 for x in free}
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'fresh exact gate')
  need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'source closure')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0
  degree[n]=da+db if o=='*'else max(da,db);known.add(n);defs[n]=(a,b)
 live=set();stack=list(outputs)
 while stack:
  x=stack.pop()
  if type(x)is int or x in live:continue
  live.add(x);stack.extend(defs.get(x,()))
 need(set(defs)|set(free)<=live,'all paid rows/coordinates live')
 M=sum(r[1]=='*'for r in rows)
 return M,len(rows)-M,max(degree[x]if type(x)is str else 0 for x in outputs)
class RingDAG:
 # Linear combinations of opaque product atoms. Addition normalizes exact
 # coefficients; multiplication extracts scalar signs but never expands sums.
 def __init__(self):self.ids={('one',):0}
 def node(self,key):
  if key not in self.ids:self.ids[key]=len(self.ids)
  return self.ids[key]
 def val(self,x):return ((0,x),)if type(x)is int and x else()if type(x)is int else((self.node(('var',x)),1),)
 def scale(self,e,c):return tuple((k,v*c)for k,v in e)if c else()
 def add(self,a,b,sign=1):
  e=dict(a)
  for n,c in b:e[n]=e.get(n,0)+sign*c
  return tuple(sorted((n,c)for n,c in e.items()if c))
 def mul(self,a,b):
  if not a or not b:return()
  if len(a)==1 and a[0][0]==0:return self.scale(b,a[0][1])
  if len(b)==1 and b[0][0]==0:return self.scale(a,b[0][1])
  sa=-1 if a[0][1]<0 else 1;sb=-1 if b[0][1]<0 else 1
  a=self.scale(a,sa);b=self.scale(b,sb)
  if a>b:a,b=b,a
  return((self.node(('mul',a,b)),sa*sb),)
 def run(self,rows,free,replacements=None):
  e={n:self.val(n)for n in free};e.update(replacements or{})
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.val(a);b=e[b]if type(b)is str else self.val(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else -1)
  return e



def candidate(parent):
 p=copy.deepcopy(parent);rows=parent['source'];d={n:(o,a,b)for n,o,a,b in rows};h=p['interfaces']['height'];tail=p['comparisons'][-1][1]
 need(d[h]==('+','bridge_height_without_time','T')and d['bridge_height_without_time']==('+','bridge_input','height_slack'),'actual paid height')
 users=lambda name:[r[0]for r in rows if name in r[2:]]
 need(users('bridge_height_without_time')==[h]and all('bridge_height_without_time' not in pair for pair in p['comparisons']),'private first height addition')
 need(users('T')==[h,tail]and all('T' not in pair for pair in p['comparisons']),'only actual time consumers')
 prod=d[tail][1];need(d[tail]==('+',prod,'T')and d[prod][0]=='*','literal clock RHS')
 modulus,quot=d[prod][1:];need(d[quot]==('-','clock_quotient_hat',1)and users('clock_quotient_hat')==[quot]and users(quot)==[prod]and users(prod)==[tail],'private clock quotient chain')
 radix=d[modulus][1];need(d[modulus]==('-',radix,1),'actual B minus one')
 child=[]
 for n,o,a,b in rows:
  if n=='bridge_height_without_time':continue
  child.append([n,'+','bridge_input','height_slack']if n==h else[n,o,a,b])
 p['source']=child;p['polynomial_source']=child+copy.deepcopy(parent['polynomial_source'][len(rows):]);p['scope']='Syntactic proposal only: incdec has a complete positive false-time fiber.'
 # Do not retain obsolete parent projection or ledger claims in this proposal.
 for key in('projection','certificate_ledger','polynomial_ledger'):p.pop(key)
 p['deleted_register']='bridge_height_without_time';p['clock_ports']={'rhs':tail,'product':prod,'quotient':quot,'modulus':modulus,'radix':radix}
 return p

def clock_polynomial_identity():
 # Independent exact coefficients in free atoms d,Q,T.
 def add(a,b):
  z=a.copy()
  for k,v in b.items():z[k]=z.get(k,0)+v
  return{k:v for k,v in z.items()if v}
 def mul(a,b):
  z={}
  for m,c in a.items():
   for n,d in b.items():
    k=tuple(x+y for x,y in zip(m,n));z[k]=z.get(k,0)+c*d
  return{k:v for k,v in z.items()if v}
 D={(1,0,0):1};Q={(0,1,0):1};T={(0,0,1):1}
 old=add(mul(D,add(Q,{(0,0,0):-1})),T)
 new=add(mul(D,add(Q,{(0,0,0):-2})),add(T,D))
 need(old==new,'all-value clock compensation')
 return[[list(k),v]for k,v in sorted(old.items())]

def outer_fixture(p,T=616,clock_hat=309):
 # Actual inc2;dec2 path: mass1/state1 -> mass2/state2 -> mass1/halt3.
 mp=p['mapping'];need(mp['K']==5 and mp['initial']==1 and mp['halt']==3 and mp['modulus']==30,'literal chosen fixed program')
 path=[1,7,3];ticks=[];res=[];qs=[]
 for cur,nxt in zip(path,path[1:]):
  q,r=divmod(cur-1,30);a,d=mp['table'][r];c,b=mp['clocks'][r]
  need(a*q+d==nxt and c*q+b==308,'exact literal two macro steps/ticks');ticks.append(308);qs.append(q);res.append(r)
 h=1024;eta=1023;C=next(r[2]for r in p['source']if r[1]=='*'and r[3]=='bridge_height_square');B=C*h*h;J=1+B;P=B*B
 need(C==131072 and B==2**37 and qs==[0,0]and res==[0,6],'actual dyadic geometry')
 E=[int(res[0]==s)+B*int(res[1]==s)for s in range(30)];a0=min(a for a,b in mp['table']);classes=sorted({a for a,b in mp['table']}-{a0});Z=[0]*len(classes)
 v={n:1 for n in p['auxiliaries']};v.update(x=0,y=1,T=T,height_slack=eta,quotient_hat=1,global_slack=P-J-1-len(Z),clock_quotient_hat=clock_hat)
 v.update({f'edge{s}_hat':e+1 for s,e in enumerate(E)});v.update({f'product{s}_hat':1 for s in range(len(Z))})
 need(all(v[n]>0 for n in p['auxiliaries']),'all outer positive coordinates')
 allowed={'native__q','native__scaled_A','native__padded_A','native__scaled_B','native__padded_B','native__scaled_Z','native__F3'}
 rows=[r for r in p['source']if not r[0].startswith('native__')or r[0]in allowed];e=numeric(rows,v)
 for a,b in(p['comparisons'][0],p['comparisons'][1],p['comparisons'][-1]):need(e[a]==e[b],'actual three outer equations')
 H=(e['native__padded_A']-12)//16;M=(e['native__padded_B']-10)//16;A=(e['native__F3']-8)//16
 need(H&M==A and e[p['interfaces']['height']]==h and e['bridge_target']==3,'actual native AND and endpoints')
 need(e[p['comparisons'][-1][0]]==308*(1+B),'actual paid clock word')
 return v,e,{'x':0,'y':1,'true_time':616,'requested_time':T,'height':h,'height_slack':eta,'radix':B,'clock_quotient_hat':clock_hat,'positive_global_slack':v['global_slack'],'native_witnesses_materialized':False}

def verify(root):
 blobs=pins(root,PINS);saved=json.loads(blobs['three_mass_target_free_height.json']);need(saved['source_sha256']==PINS['three_mass_target_free_height.py'],'actual maintained source/receipt')
 parents=[f['packet']for f in saved['forms']];need([p['variant']for p in parents]==['clock_incdec','clock_zero3','clock_nop','clock_positive3'],'four exact parent forms')
 coefficients=clock_polynomial_identity();forms=[];counts={'complete_signed_height_graphs':0,'complete_clock_shift_graphs':0,'retained_comparisons':0,'paid_live_gates':0,'exact_numeric_identities':0,'rational_cases':0,'actual_outer_fiber_points':0}
 rng=random.Random(6161024309)
 for parent,expected in zip(parents,(591,466,464,467)):
  p=candidate(parent);free=p['parameters']+p['auxiliaries'];M,A,degree=ledger(p['polynomial_source'],free,[p['output']]);om,oa,_=ledger(parent['polynomial_source'],free,[parent['output']]);need(M+A==expected and(M,A)==(om,oa-1),'fully paid one-addition proposal')
  cm,ca,cd=ledger(p['source'],free,[v for pair in p['comparisons']for v in pair]);need((M-cm,A-ca)==(19,37),'unchanged complete SOS')
  p['candidate_ledger']={'M':M,'A':A,'operations':M+A,'positive_witnesses':len(p['auxiliaries']),'comparisons':19,'degree_upper_bound':degree,'all_gates_live':True}
  ring=RingDAG();eta=ring.add(ring.val('height_slack'),ring.val('T'),-1);before=ring.run(parent['polynomial_source'],free,{'height_slack':eta});after=ring.run(p['polynomial_source'],free)
  need(before[parent['output']]==after[p['output']],'complete signed height pullback');counts['complete_signed_height_graphs']+=1
  for a,b in p['comparisons']:need(before[a]==after[a]and before[b]==after[b],'all retained operands');counts['retained_comparisons']+=1
  cp=p['clock_ports'];shift={'T':ring.add(ring.val('T'),after[cp['modulus']]),'clock_quotient_hat':ring.add(ring.val('clock_quotient_hat'),ring.val(1),-1)}
  # The exact d,Q,T coefficient expansion above proves the sole changed RHS.
  env={n:ring.val(n)for n in free};env.update(shift)
  for n,o,a,b in p['polynomial_source']:
   aa=env[a]if type(a)is str else ring.val(a);bb=env[b]if type(b)is str else ring.val(b)
   env[n]=after[n]if n==cp['rhs'] else ring.mul(aa,bb)if o=='*'else ring.add(aa,bb,1 if o=='+'else -1)
   if n not in(cp['quotient'],cp['product']):need(env[n]==after[n],'unchanged entire graph after proved clock cut')
  need(env[p['output']]==after[p['output']],'complete clock-shift polynomial identity');counts['complete_clock_shift_graphs']+=1
  for case in range(8):
   v={n:rng.randrange(-2,4)for n in free}
   if case>=6:v={n:Fraction(vv,3)for n,vv in v.items()};counts['rational_cases']+=1
   a=numeric(p['polynomial_source'],v);u=dict(v);u['T']+=a[cp['modulus']];u['clock_quotient_hat']-=1;b=numeric(p['polynomial_source'],u)
   old=dict(v);old['height_slack']-=v['T'];c=numeric(parent['polynomial_source'],old)
   need(a[p['output']]==b[p['output']]==c[parent['output']],'full exact numeric shift and parent pullback');counts['exact_numeric_identities']+=2
  counts['paid_live_gates']+=M+A;forms.append(p)
 p=forms[0];base,e,record=outer_fixture(p);B=record['radix'];fiber=[]
 for k in(0,1,2,307,308):
  v,z,r=outer_fixture(p,616+k*(B-1),309-k)
  need(all(z[name]==e[name]for name in z if name.startswith('native__')),'same complete actual native inputs')
  for name in p['auxiliaries']:
   if name!='clock_quotient_hat':need(v[name]==base[name],'unchanged nonclock witnesses')
  fiber.append(r);counts['actual_outer_fiber_points']+=1
 # The seed is also an actual maintained outer zero at its positive old slack407.
 parent=parents[0];v=dict(base,height_slack=407);allow={'native__q','native__scaled_A','native__padded_A','native__scaled_B','native__padded_B','native__scaled_Z','native__F3'}
 pe=numeric([r for r in parent['source']if not r[0].startswith('native__')or r[0]in allow],v)
 for a,b in(parent['comparisons'][0],parent['comparisons'][1],parent['comparisons'][-1]):need(pe[a]==pe[b],'maintained positive seed outer constraints')
 need(pe[parent['interfaces']['height']]==1024 and 1024>1+616 and all(pe[name]==e[name]for name in pe if name.startswith('native__')),'prescribed seed height/native inputs')
 return {'status':'PASS_SPECIFIC_TIME_FREE_HEIGHT_OBSTRUCTION','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'counts':counts,'local_clock_coefficients':coefficients,'forms':forms,'incdec_outer_fiber':fiber,'full_zero_proof_scope':'The seed native extension is supplied by the pinned maintained prescribed-height completeness theorem; all its native coordinates are unchanged by the exact clock shift. The supplied natural T=137438954087 is false for this fixed incdec source at x0,y1. No huge native witnesses materialized; no universal operation bound.','other_variants':'Their accepted trajectories have one step. The displayed incdec positive-fiber obstruction is not claimed for them; the separate one-step proof is in the note.'}
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
