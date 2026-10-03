#!/usr/bin/env python3
"""Independent bounded literal-source review of three one-step height proposals."""
import argparse,copy,hashlib,json,random,types
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
AUTHOR={'three_mass_one_step_height.json': '60019db77c7045f4e34dd8bcd335965d943cc4f475e5c0f53b8236771179a258',
 'three_mass_one_step_height.md': '13640b9c38960d3c7d74e7d9e5ca916d6965ae792ec7b9dc079a37f0baa480d0',
 'three_mass_one_step_height.py': 'a4420e122bf9134362aa08026237c3d411b9c1f72996477e1665fd8c7c983271'}
VARIANTS=('clock_zero3','clock_nop','clock_positive3')
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



def affine_table_step(mp,variant,n):
 # Handwritten source macros including the rejecting totalization.
 K=mp['K'];state=(n-1)%K+1;mass=(n-1)//K+1;target=mp['trap'];newmass=mass;ticks=192*mass+8
 if variant=='clock_incdec':
  if state==mp['initial']:target=mp['codes']['a'];newmass=2*mass;ticks=300*mass+8
  elif state==mp['codes']['a']and mass%2==0:target=mp['halt'];newmass=mass//2;ticks=300*(mass//2)+8
 elif state==mp['initial']:
  succeeds=variant=='clock_nop'or variant=='clock_zero3'and mass%3!=0 or variant=='clock_positive3'and mass%3==0
  if succeeds:target=mp['halt']
 return K*(newmass-1)+target,ticks

def finite_outer(p,x):
 mp=p['mapping'];K=mp['K'];m=mp['modulus'];mass=x+1
 accepts=p['variant']in('clock_incdec','clock_nop')or p['variant']=='clock_zero3'and mass%3!=0 or p['variant']=='clock_positive3'and mass%3==0
 if not accepts:return None
 n0=K*x+mp['initial'];path=[n0];qs=[];residues=[];ticks=[]
 for _ in range(2 if p['variant']=='clock_incdec'else 1):
  q,r=divmod(path[-1]-1,m);r+=1;qs.append(q);residues.append(r)
  nxt,tick=affine_table_step(mp,p['variant'],path[-1]);a,d=mp['table'][r-1];c,b=mp['clocks'][r-1]
  need((nxt,tick)==(a*q+d,c*q+b),'actual residue/tick rows');path.append(nxt);ticks.append(tick)
 need((path[-1]-1)%K+1==mp['halt'],'exact first halt');y=(path[-1]-mp['halt'])//K+1;T=sum(ticks)
 need(y==mass and T==(600*mass+16 if p['variant']=='clock_incdec'else 192*mass+8),'independent closed-form triple')
 h=1
 while h<=n0 or h<=max(qs):h*=2
 radix=next(r for r in p['source']if r[1]=='*'and r[3]=='bridge_height_square');C=radix[2];B=C*h*h;t=len(qs);P=B**t;J=(P-1)//(B-1)
 pack=lambda xs:sum(v*B**i for i,v in enumerate(xs));E=[pack([int(r==s)for r in residues])for s in range(1,m+1)];W=pack(qs)
 a0=min(a for a,d in mp['table']);classes=sorted({a for a,d in mp['table']}-{a0});Z=[pack([q if mp['table'][r-1][0]==a else 0 for q,r in zip(qs,residues)])for a in classes]
 v={n:1 for n in p['auxiliaries']};v.update(x=x,y=y,T=T,height_slack=h-n0,quotient_hat=W+1,global_slack=P-J-W-1-sum(Z)-len(Z),clock_quotient_hat=1+(pack(ticks)-T)//(B-1))
 v.update({f'edge{s}_hat':e+1 for s,e in enumerate(E)});v.update({f'product{s}_hat':z+1 for s,z in enumerate(Z)})
 need(min(v[n]for n in p['auxiliaries'])>0,'strict positive outer hats/slacks')
 # Execute only actual outer rows and the literal paid native padding interfaces.
 allowed={'native__q','native__scaled_A','native__padded_A','native__scaled_B','native__padded_B','native__scaled_Z','native__F3'}
 rows=[r for r in p['source']if not r[0].startswith('native__')or r[0]in allowed];env=numeric(rows,v)
 for a,b in(p['comparisons'][0],p['comparisons'][1],p['comparisons'][-1]):need(env[a]==env[b],'three literal outer equalities')
 H=(env['native__padded_A']-12)//16;M=(env['native__padded_B']-10)//16;A=(env['native__F3']-8)//16
 need(H&M==A and env[p['interfaces']['height']]==h and env['bridge_target']==path[-1],'joined AND and exact actual endpoints')
 need(T<B-1 and t==1 and v['clock_quotient_hat']==1 and len(qs)<=m*h and len(set(path[:-1]))==len(qs),'clock no-wrap bounds')
 return dict(x=x,y=y,T=T,steps=t,height=h,height_slack=v['height_slack'],signed_parent_slack=v['height_slack']-T,native_witnesses_materialized=False)

def verify(root,artifacts):
 need(len(AUTHOR)==3,'final three author pins required');raw=pins(root,PINS);ab=pins(artifacts,AUTHOR);saved=json.loads(ab['three_mass_one_step_height.json']);parent=json.loads(raw['three_mass_target_free_height.json']);olds={f['packet']['variant']:f['packet']for f in parent['forms']}
 need(saved['source_sha256']==AUTHOR['three_mass_one_step_height.py'],'author receipt/source pin')
 path=Path(artifacts)/'three_mass_one_step_height.py';mod=types.ModuleType('_pinned_one_step_probe');mod.__file__=str(path);exec(compile(ab[path.name],str(path),'exec'),mod.__dict__)
 need(tuple(mod.VARIANTS)==VARIANTS,'exact three variants with incdec excluded')
 forms=[];counts=dict(complete_literal_sources=0,whole_graph_identities=0,retained_operand_identities=0,paid_live_gates=0,actual_residue_rows=0,literal_clock_expansions=0,numeric_graph_identities=0,rational_cases=0,positive_embeddings=0,outer_histories=0,height_margins=0,incdec_rejections=0)
 children={f['packet']['variant']:f['packet']for f in saved['forms']};need(len(saved['forms'])==3 and tuple(children)==VARIANTS,'three saved full source forms')
 rng=random.Random(466464467)
 for variant,want in zip(VARIANTS,((466,180,286),(464,178,286),(467,185,282))):
  p=mod.build(variant,root=root);old=olds[variant];need(exact(p,children[variant])and exact(mod.canonical_parent(variant,root=root),old),'actual saved and authenticated canonical packets')
  rows=old['source'];defs={n:(o,a,b)for n,o,a,b in rows};h=p['interfaces']['height'];users=lambda name:[r[0]for r in rows if name in r[2:]]
  need(defs['bridge_height_without_time']==('+','bridge_input','height_slack')and defs[h]==('+','bridge_height_without_time','T')and users('bridge_height_without_time')==[h]and users('height_slack')==['bridge_height_without_time'],'literal private two-addition parent height')
  need(all(x not in pair for pair in old['comparisons']for x in('bridge_height_without_time','height_slack')),'no private comparison consumers')
  new=[[n,'+','bridge_input','height_slack']if n==h else[n,o,a,b]for n,o,a,b in rows if n!='bridge_height_without_time'];poly=new+copy.deepcopy(old['polynomial_source'][len(rows):])
  need(exact(p['source'],new)and exact(p['polynomial_source'],poly)and exact(p['comparisons'],old['comparisons'])and p['output']==old['output'],'complete literal source and retained finalizer')
  need(exact(p['parameters'],old['parameters'])and p['parameters']==['x','y','T']and exact(p['auxiliaries'],old['auxiliaries'])and len(p['auxiliaries'])==56 and p['domains']==dict(parameters='natural',auxiliaries='positive'),'unchanged complete interface')
  free=p['parameters']+p['auxiliaries'];M,A,d=ledger(poly,free,[p['output']]);cm,ca,cd=ledger(new,free,[v for pair in p['comparisons']for v in pair]);om,oa,_=ledger(old['polynomial_source'],free,[old['output']])
  need((M+A,M,A)==want and(M,A)==(om,oa-1)and(M-cm,A-ca)==(19,37)and d==1192 and p['degree']['exact_degree']is None,'full paid counts/finalizer and upper degree')
  def stated(m,a,deg,eq):return dict(operations=m+a,M=m,A=a,positive_witnesses=56,equations=eq,degree_upper_bound=deg,all_gates_live=True)
  need(exact(p['polynomial_ledger'],stated(M,A,d,None))and exact(p['certificate_ledger'],stated(cm,ca,cd,19))and exact(p['parent_pins'],PINS),'current declared ledger and lineage')
  need(exact(p['mapping'],old['mapping'])and exact(p['historical_target_free_projection'],old['projection']),'actual fixed map and provenance only')
  pr=p['projection'];need(pr['signed_parent_pullback']=={'height_slack':'height_slack-T'}and pr['positive_parent_embedding']=={'height_slack':'height_slack+T'}and pr['unconditional_positive_pullback']is False and pr['full_natural_zero_bijection_claimed']is False and pr['clock_quotient_arithmetic_retained']is True,'precise map/domain metadata')
  mp=p['mapping'];K=mp['K'];need((K,mp['modulus'],mp['initial'],mp['halt'],mp['trap'])==(5,30,1,2,3),'fixed one-step state coding')
  edges=[]
  for r,((a,b),(c,e))in enumerate(zip(mp['table'],mp['clocks']),1):
   block,state=divmod(r-1,K);state+=1;mass=block+1
   accept=state==1 and(variant=='clock_nop'or variant=='clock_zero3'and mass%3!=0 or variant=='clock_positive3'and mass%3==0)
   target=2 if accept else 3
   need((a,b,c,e)==(30,5*block+target,1152,192*mass+8),'independent literal unchanged-payload macro/tick row')
   edges.append([r,state,target]);counts['actual_residue_rows']+=1
  need(exact(p['one_step_control_proof']['residue_control_edges'],edges)and p['one_step_control_proof']['accepted_duration']==1 and p['one_step_control_proof']['incdec_excluded']is True,'current actual control proof data')
  ring=RingDAG();before=ring.run(old['polynomial_source'],free,{'height_slack':ring.add(ring.val('height_slack'),ring.val('T'),-1)});after=ring.run(poly,free)
  expected=ring.add(ring.add(ring.scale(ring.val('x'),5),ring.val(1)),ring.val('height_slack'))
  need(before[h]==after[h]==expected and before[old['output']]==after[p['output']],'direct complete ring graph identity without author cut');counts['whole_graph_identities']+=1
  for a,b in p['comparisons']:need(before[a]==after[a]and before[b]==after[b],'literal retained operands');counts['retained_operand_identities']+=2
  clock_lhs,clock_rhs=p['comparisons'][-1];wantclock=ring.scale(ring.add(ring.val('quotient_hat'),ring.val(1),-1),1152)
  for r,(c,br)in enumerate(mp['clocks']):wantclock=ring.add(wantclock,ring.scale(ring.add(ring.val(f'edge{r}_hat'),ring.val(1),-1),br))
  need(after[clock_lhs]==wantclock,'independent complete paid clock-word coefficient expansion')
  defsnew={n:(o,a,b)for n,o,a,b in new};op,prod,tt=defsnew[clock_rhs];need((op,tt)==('+','T'),'literal retained clock RHS')
  op,bm,quot=defsnew[prod];need(op=='*'and defsnew[quot]==('-','clock_quotient_hat',1)and defsnew[bm][0]=='-'and defsnew[bm][2]==1,'retained clock quotient and modulus gates')
  need([r[0]for r in new if 'T'in r[2:]]==[clock_rhs]and [r[0]for r in new if 'clock_quotient_hat'in r[2:]]==[quot],'only literal time and clock-hat consumers')
  wantclockrhs=ring.add(ring.mul(after[bm],ring.add(ring.val('clock_quotient_hat'),ring.val(1),-1)),ring.val('T'))
  need(after[clock_rhs]==wantclockrhs,'independent actual clock equation');counts['literal_clock_expansions']+=1
  for case in range(16):
   v={n:rng.randrange(1,4)for n in free}
   if case<4:v.update({n:rng.randrange(4)for n in p['parameters']})
   else:v={n:rng.randrange(-2,4)for n in free}
   if case>=12:v={n:Fraction(vv,3)for n,vv in v.items()};counts['rational_cases']+=1
   pv=dict(v);pv['height_slack']-=v['T'];a=numeric(old['polynomial_source'],pv);b=numeric(poly,v)
   need(a[old['output']]==b[p['output']],'exact complete numeric pullback');counts['numeric_graph_identities']+=1
   if case<12:need(mod.evaluate(p,v,signed=case>=4,root=root)==b[p['output']]and exact(mod.integer_pullback(p,v,root=root),pv),'bounded public integer interfaces')
   if case<4:
    emb=dict(v);emb['height_slack']+=v['T'];need(min(emb[n]for n in p['auxiliaries'])>0 and exact(mod.embed_parent_assignment(p,v,root=root),emb),'unconditional natural positive embedding')
    need(numeric(old['polynomial_source'],v)[old['output']]==numeric(poly,emb)[p['output']],'entire positive embedding identity');counts['positive_embeddings']+=1
  C=next(r[2]for r in new if r[1]=='*'and r[3]=='bridge_height_square')
  need(C==131072,'actual fixed radix multiplier')
  for hh in range(2,34):need(1152*hh+8<C*hh*hh-1,'one-step tick range from h2 without T bound');counts['height_margins']+=1
  fixtures=[]
  for x in list(range(18))+[40]:
   f=finite_outer(p,x)
   if f is not None:fixtures.append(f);counts['outer_histories']+=1
  forms.append(dict(variant=variant,operations=M+A,M=M,A=A,positive_witnesses=56,comparisons=19,degree_upper_bound=d,exact_degree=None,outer_histories=fixtures));counts['complete_literal_sources']+=1;counts['paid_live_gates']+=M+A
 for fn in(lambda:mod.build('clock_incdec',root=root),lambda:mod.canonical_parent('clock_incdec',root=root),lambda:mod.rewrite(olds['clock_incdec'],root=root),lambda:mod.checked(olds['clock_incdec'],root=root)):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['incdec_rejections']+=1
  else:raise ValueError('incdec was accepted by one-step interface')
 neg=next(f for p in forms if p['variant']=='clock_nop'for f in p['outer_histories']if f['x']==0)
 need((neg['y'],neg['T'],neg['height'],neg['height_slack'],neg['signed_parent_slack'])==(1,200,2,1,-199),'actual height2 genuine one-step negative parent slack')
 return dict(status='PASS_BOUNDED_ONE_STEP_HEIGHT_REVIEW',review_source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PINS,author_pins=AUTHOR,counts=counts,forms=forms,negative_inverse_outer_fixture=neg,scope='Bounded three complete actual-source/proof probe, not an exhaustive maintained hostile-API audit. Exact one-step table proof, all-value signed graph identity and one-way positive embedding. Upper degrees only; incdec excluded; native witnesses supplied by inherited theorem, not materialized.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.artifacts)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed review receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
