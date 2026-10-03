#!/usr/bin/env python3
"""Independent literal source/API/domain review of target-free mass heights."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PARENT={'native_pell_factored_first_coefficient.json': 'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf',
 'native_pell_factored_first_coefficient.md': 'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528',
 'native_pell_factored_first_coefficient.py': 'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc',
 'residue_affine_packed_history.json': 'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421',
 'residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882',
 'residue_affine_packed_history.py': 'd06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4',
 'three_mass_unbounded_endpoint_projection.json': 'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457',
 'three_mass_unbounded_endpoint_projection.md': '8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c',
 'three_mass_unbounded_endpoint_projection.py': '96d41f43190547fce121c5271e351af3d2bc99fa2226379e4d24f980bae998dd',
 'three_mass_unbounded_interface.json': 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e',
 'three_mass_unbounded_interface.md': 'd336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45',
 'three_mass_unbounded_interface.py': 'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a'}
AUTHOR={'three_mass_target_free_height.json': 'a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830',
 'three_mass_target_free_height.md': '61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a',
 'three_mass_target_free_height.py': '7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49'}
VARIANTS=('clock_incdec','clock_zero3','clock_nop','clock_positive3')
EXPECTED=((592,235,357,58,2344),(467,180,287,56,1192),(465,178,287,56,1192),(468,185,283,56,1192))
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



def literal(parent):
 rows=parent['source'];defs={n:(o,a,b)for n,o,a,b in rows};K=parent['mapping']['K'];qh=parent['mapping']['halt'];h=parent['interfaces']['height']
 low=defs['bridge_height_without_time'][1]
 need(defs[low]==('+','bridge_input','bridge_target'),'literal endpoint sum')
 need(defs['bridge_height_without_time']==('+',low,'height_slack')and defs['endpoint_raised_height']==('+','bridge_height_without_time',K)and defs[h]==('+','endpoint_raised_height','T'),'four literal height additions')
 for name,users in((low,['bridge_height_without_time']),('bridge_height_without_time',['endpoint_raised_height']),('endpoint_raised_height',[h]),('height_slack',['bridge_height_without_time'])):
  need([r[0]for r in rows if name in r[2:]]==users and all(name not in pair for pair in parent['comparisons']),'private height source and comparison consumers')
 need(defs['bridge_input_scaled']==('*',K,'x')and defs['bridge_input']==('+','bridge_input_scaled',parent['mapping']['initial']),'literal initial affine map')
 need(defs['bridge_final_scaled']==('*',K,'y')and defs['bridge_target']==('+','bridge_final_scaled',qh-K),'literal target affine map')
 need([r[0]for r in rows if 'bridge_target' in r[2:]]==[low,next(r[0]for r in rows if r[1]=='*'and r[3]=='bridge_target')],'target private height/transport uses')
 child=[]
 for n,o,a,b in rows:
  if n in(low,'endpoint_raised_height'):continue
  if n=='bridge_height_without_time':child.append([n,'+','bridge_input','height_slack'])
  elif n==h:child.append([n,'+','bridge_height_without_time','T'])
  else:child.append([n,o,a,b])
 pairs=copy.deepcopy(parent['comparisons']);poly=copy.deepcopy(child)
 for i,(a,b)in enumerate(pairs):poly.extend([[f'ep_res{i}','-',a,b],[f'ep_sq{i}','*',f'ep_res{i}',f'ep_res{i}']])
 out='ep_sq0'
 for i in range(1,len(pairs)):n=f'ep_sum{i}';poly.append([n,'+',out,f'ep_sq{i}']);out=n
 need(poly[len(child):]==parent['polynomial_source'][len(rows):],'literal finalizer retained with no folding')
 return child,pairs,poly,out,h,low

def pullback(p,v):
 e=dict(v);e['height_slack']-=p['mapping']['K']*v['y']+p['mapping']['halt'];return e

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
 while h<=n0+T or h<=max(qs):h*=2
 radix=next(r for r in p['source']if r[1]=='*'and r[3]=='bridge_height_square');C=radix[2];B=C*h*h;t=len(qs);P=B**t;J=(P-1)//(B-1)
 pack=lambda xs:sum(v*B**i for i,v in enumerate(xs));E=[pack([int(r==s)for r in residues])for s in range(1,m+1)];W=pack(qs)
 a0=min(a for a,d in mp['table']);classes=sorted({a for a,d in mp['table']}-{a0});Z=[pack([q if mp['table'][r-1][0]==a else 0 for q,r in zip(qs,residues)])for a in classes]
 v={n:1 for n in p['auxiliaries']};v.update(x=x,y=y,T=T,height_slack=h-n0-T,quotient_hat=W+1,global_slack=P-J-W-1-sum(Z)-len(Z),clock_quotient_hat=1+(pack(ticks)-T)//(B-1))
 v.update({f'edge{s}_hat':e+1 for s,e in enumerate(E)});v.update({f'product{s}_hat':z+1 for s,z in enumerate(Z)})
 need(min(v[n]for n in p['auxiliaries'])>0,'strict positive outer hats/slacks')
 # Execute only actual outer rows and the literal paid native padding interfaces.
 allowed={'native__q','native__scaled_A','native__padded_A','native__scaled_B','native__padded_B','native__scaled_Z','native__F3'}
 rows=[r for r in p['source']if not r[0].startswith('native__')or r[0]in allowed];env=numeric(rows,v)
 for a,b in(p['comparisons'][0],p['comparisons'][1],p['comparisons'][-1]):need(env[a]==env[b],'three literal outer equalities')
 H=(env['native__padded_A']-12)//16;M=(env['native__padded_B']-10)//16;A=(env['native__F3']-8)//16
 need(H&M==A and env[p['interfaces']['height']]==h and env['bridge_target']==path[-1],'joined AND and exact actual endpoints')
 need(T<B-1 and T<h and len(qs)<=m*h and len(set(path[:-1]))==len(qs),'clock no-wrap bounds')
 return dict(x=x,y=y,T=T,steps=t,height=h,height_slack=v['height_slack'],signed_endpoint_slack=v['height_slack']-K*y-mp['halt'],signed_coefficient_slack=v['height_slack']-path[-1],native_witnesses_materialized=False)

def verify(root,artifacts):
 raw=pins(root,PARENT);ab=pins(artifacts,AUTHOR)
 saved=json.loads(ab['three_mass_target_free_height.json']);parents=json.loads(raw['three_mass_unbounded_endpoint_projection.json']);coeff=json.loads(raw['native_pell_factored_first_coefficient.json'])
 need(saved['source_sha256']==AUTHOR['three_mass_target_free_height.py']and exact(saved['parent_pins'],PARENT),'pinned complete author lineage')
 olds={f['packet']['variant']:f['packet']for f in parents['forms']};children={f['packet']['variant']:f['packet']for f in saved['forms']};older={f['packet']['variant']:f['packet']for f in coeff['forms']if f['variant'].startswith('clock_')}
 need(len(saved['forms'])==len(olds)==len(older)==4 and set(children)==set(olds)==set(older)==set(VARIANTS),'exact four complete variants')
 path=Path(artifacts)/'three_mass_target_free_height.py';mod=types.ModuleType('_authenticated_target_free_author');mod.__file__=str(path);exec(compile(ab[path.name],str(path),'exec'),mod.__dict__)
 counts=dict(literal_complete_sources=0,endpoint_graph_identities=0,coefficient_graph_identities=0,retained_operands=0,retained_residuals=0,paid_live_gates=0,degree_upper_bounds=0,numeric_identities=0,rational_identities=0,numeric_residuals=0,source_table_checks=0,outer_histories=0,height_two_boundaries=0,height_margin_checks=0,guards=0,copies=0,warm_pins=0)
 forms=[];rng=random.Random(5924652026)
 for variant,want in zip(VARIANTS,EXPECTED):
  old=olds[variant];p=mod.build(variant,root=root)
  need(exact(p,children[variant])and exact(mod.canonical_parent(variant,root=root),old)and exact(mod.rewrite(old,root=root),p)and exact(mod.checked(p,root=root),p),'saved/canonical public forms')
  rows,pairs,poly,out,h,low=literal(old)
  need(exact(p['source'],rows)and exact(p['comparisons'],pairs)and exact(p['polynomial_source'],poly)and p['output']==out,'all literal independent schedules and outputs')
  need(p['parameters']==old['parameters']==['x','y','T']and exact(p['auxiliaries'],old['auxiliaries'])and p['domains']==dict(parameters='natural',auxiliaries='positive'),'unchanged declared domains and coordinates')
  free=p['parameters']+p['auxiliaries'];M,A,d=ledger(poly,free,[out]);cm,ca,cd=ledger(rows,free,[v for pair in pairs for v in pair]);om,oa,od=ledger(old['polynomial_source'],free,[old['output']]);ocm,oca,ocd=ledger(old['source'],free,[v for pair in pairs for v in pair])
  need((M+A,M,A,len(p['auxiliaries']),d)==want and(om-M,oa-A)==(0,2)and(ocm-cm,oca-ca)==(0,2)and(M-cm,A-ca)==(19,37),'whole paid source and exact finalizer cost')
  def stated(m,a,deg,eq):return dict(operations=m+a,M=m,A=a,positive_witnesses=len(p['auxiliaries']),equations=eq,degree_upper_bound=deg,all_gates_live=True)
  need(exact(p['polynomial_ledger'],stated(M,A,d,None))and exact(p['certificate_ledger'],stated(cm,ca,cd,19)),'current source-ledger metadata')
  need(p['degree']['upper_bound']==d==od and p['degree']['exact_degree']is None and cd==ocd,'upper-only complete degree')
  need(exact(p['parent_pins'],PARENT)and exact(p['mapping'],old['mapping'])and exact(p['interfaces'],old['interfaces'])and exact(p['coefficient_transfer'],old['coefficient_transfer']),'active full interfaces and coefficient-local provenance')
  mp=p['mapping'];K=mp['K'];qh=mp['halt'];proj=p['projection']
  need(exact(p['historical_endpoint_projection'],old['projection'])and 'not a map for the current packet' in p['historical_endpoint_projection_role'],'historical slice is not active')
  need(proj['same_supplied_coordinates']is True and proj['same_coordinate_polynomial_identity']is False and proj['full_polynomial_identity_under_signed_pullback']is True and proj['unconditional_positive_pullback']is False and proj['full_natural_zero_bijection_claimed']is False,'precise signed versus positive map flags')
  need(proj['signed_parent_pullback']=={'height_slack':f'height_slack-{K}*y-{qh}'}and proj['removed_registers']==[low,'endpoint_raised_height']and proj['height_formula']=='bridge_input+T+height_slack'and proj['height_minimum_on_domain']==2,'literal map metadata')
  ring=RingDAG();eta=ring.val('height_slack');y=ring.val('y');target=ring.add(ring.scale(y,K),ring.val(qh-K));etaold=ring.add(ring.add(eta,ring.scale(y,K),-1),ring.val(qh),-1)
  bef=ring.run(old['polynomial_source'],free,{'height_slack':etaold});aft=ring.run(poly,free)
  height=ring.add(ring.add(ring.add(ring.scale(ring.val('x'),K),ring.val(mp['initial'])),ring.val('T')),eta)
  need(bef[h]==aft[h]==height and bef['bridge_target']==aft['bridge_target']==target,'exact full height/target coefficients')
  need(bef[old['output']]==aft[out],'direct full endpoint polynomial identity without supplied cuts');counts['endpoint_graph_identities']+=1
  for a,b in pairs:
   need(bef[a]==aft[a]and bef[b]==aft[b],'both retained operands');counts['retained_operands']+=2
   need(ring.add(bef[a],bef[b],-1)==ring.add(aft[a],aft[b],-1),'retained difference');counts['retained_residuals']+=1
  co=older[variant];ce=ring.run(co['polynomial_source'],co['parameters']+co['auxiliaries'],{'final_positive':y,'height_slack':ring.add(eta,target,-1)})
  need(ce[co['output']]==aft[out],'complete composed coefficient-parent graph identity');counts['coefficient_graph_identities']+=1
  counts['literal_complete_sources']+=1;counts['paid_live_gates']+=M+A;counts['degree_upper_bounds']+=1
  C=next(r[2]for r in rows if r[1]=='*'and r[3]=='bridge_height_square');m=mp['modulus'];g=len({a for a,b in mp['table']})-1
  need(type(C)is int and C>0 and C&(C-1)==0 and C>=max(4,m+1,1+max(a+b for a,b in mp['table']),2384*m+2),'actual dyadic radix and clock margin')
  need(len(mp['table'])==len(mp['clocks'])==m and all(a>=0 and b>0 for a,b in mp['table'])and mp['initial']!=qh and 1<=qh<=K,'literal total positive map premises')
  for s in range(1,m+1):
   for q in(0,1,5):
    a,b=mp['table'][s-1];c,e=mp['clocks'][s-1];need(affine_table_step(mp,variant,m*q+s)==(a*q+b,c*q+e),'independent machine macro and tick table');counts['source_table_checks']+=1
  for hh in range(2,34):
   B=C*hh*hh
   need(m*hh<B and all(a*(hh-1)+b<B for a,b in mp['table'])and B-2*hh-g>=4*m-g>0 and B-1-2384*m*hh*hh>=7,'h2-up digit/global/clock inequalities');counts['height_margin_checks']+=1
  for case in range(20):
   v={n:rng.randrange(1,4)for n in free}
   if case<5:v.update({n:rng.randrange(4)for n in p['parameters']})
   else:v={n:rng.randrange(-2,4)for n in free}
   if case>=16:v={n:Fraction(vv,3)for n,vv in v.items()};counts['rational_identities']+=1
   a=numeric(old['polynomial_source'],pullback(p,v));b=numeric(poly,v);need(a[old['output']]==b[out],'complete exact numeric pullback');counts['numeric_identities']+=1
   for l,r in pairs:need(a[l]-a[r]==b[l]-b[r],'every numeric difference');counts['numeric_residuals']+=1
   if case<16:need(mod.evaluate(p,v,signed=case>=5,root=root)==b[out]and exact(mod.integer_pullback(p,v,root=root),pullback(p,v)),'public strict integer algebra')
  v={n:1 for n in free};v.update(x=0,y=0,T=0);e=numeric(rows,v)
  need(e[h]==2 and e['bridge_target']==qh-K<=0 and all(e[n]>0 for n in ('native__q','native__padded_A','native__padded_B','native__F3')),'actual height2 and nonpositive target/native positivity boundary')
  need(mod.evaluate(p,v,root=root)==numeric(poly,v)[out]and mod.integer_pullback(p,v,root=root)['height_slack']==1-qh<0,'natural y0 admitted; pullback honestly signed');counts['height_two_boundaries']+=1
  fixtures=[]
  for x in list(range(18))+[40]:
   f=finite_outer(p,x)
   if f is not None:fixtures.append(f);counts['outer_histories']+=1
  forms.append(dict(variant=variant,M=M,A=A,operations=M+A,positive_witnesses=len(p['auxiliaries']),comparisons=19,degree_upper_bound=d,exact_degree=None,outer_histories=fixtures))
 neg=next(f for form in forms if form['variant']=='clock_nop'for f in form['outer_histories']if f['x']==40)
 need((neg['y'],neg['T'],neg['height'],neg['height_slack'],neg['signed_endpoint_slack'],neg['signed_coefficient_slack'])==(41,7880,8192,111,-96,-91),'independently generated negative inverse fixture')
 counts['negative_inverse_outer_fixtures']=1
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise ValueError('Malformed canonical API accepted')
 for variant in(None,True,0,'bad'):
  for fn in(mod.build,mod.canonical_parent):reject(lambda fn=fn,variant=variant:fn(variant,root=root))
 for packet in(None,[],{},dict(variant=True),dict(variant='bad')):
  reject(lambda packet=packet:mod.checked(packet,root=root));reject(lambda packet=packet:mod.rewrite(packet,root=root))
 p=mod.build(root=root);old=olds['clock_incdec'];v={n:1 for n in p['parameters']+p['auxiliaries']};v.update(x=0,y=0,T=0)
 for key in p:
  q=copy.deepcopy(p);del q[key];reject(lambda q=q:mod.checked(q,root=root))
 for key in old:
  q=copy.deepcopy(old);del q[key];reject(lambda q=q:mod.rewrite(q,root=root))
 for key in('source','polynomial_source','comparisons','parameters','auxiliaries'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 for key in('unconditional_positive_pullback','full_natural_zero_bijection_claimed','same_coordinate_polynomial_identity'):
  q=copy.deepcopy(p);q['projection'][key]=True;reject(lambda q=q:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['historical_endpoint_projection']['natural_zero_image']='all zeros';reject(lambda:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['degree']['exact_degree']=2344;reject(lambda:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['polynomial_ledger']['M']=float(q['polynomial_ledger']['M']);reject(lambda:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['polynomial_source'][-1][1]='-';reject(lambda:mod.checked(q,root=root))
 for val in(True,1.0,Fraction(1),None):
  bad=dict(v,x=val)
  for fn in(mod.evaluate,mod.integer_pullback):reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
 for name in p['parameters']:
  bad=dict(v);bad[name]=-1;reject(lambda bad=bad:mod.evaluate(p,bad,root=root))
 for name in p['auxiliaries']:
  bad=dict(v);bad[name]=0;reject(lambda bad=bad:mod.evaluate(p,bad,root=root))
 for flag in(0,1,None):reject(lambda flag=flag:mod.evaluate(p,v,signed=flag,root=root))
 for bad in({},dict(v,extra=0),list(v)):
  for fn in(mod.evaluate,mod.integer_pullback):reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
 for key,val in p.items():
  if type(val)in(dict,list):
   q=mod.build(root=root);q[key].clear();need(exact(mod.build(root=root),p),'independent mutable child metadata');counts['copies']+=1
 for fn in(lambda:mod.canonical_parent(root=root),lambda:mod.rewrite(old,root=root),lambda:mod.checked(p,root=root)):
  q=fn();q['source'].clear();need(exact(mod.build(root=root),p)and exact(mod.canonical_parent(root=root),old),'isolated canonical accessor');counts['copies']+=1
 q=mod.polynomial_source(p,root=root);q[0][2]=999;need(exact(mod.polynomial_source(p,root=root),p['polynomial_source']),'source rows isolated');counts['copies']+=1
 q=mod.integer_pullback(p,v,root=root);q['x']=999;need(v['x']==0 and mod.integer_pullback(p,v,root=root)['x']==0,'pullback copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='target_free_review_pins_')as tmp:
  tmp=Path(tmp)
  for n,b in raw.items():(tmp/n).write_bytes(b)
  calls=[lambda:mod.build(root=tmp),lambda:mod.canonical_parent(root=tmp),lambda:mod.checked(p,root=tmp),lambda:mod.rewrite(old,root=tmp),lambda:mod.polynomial_source(p,root=tmp),lambda:mod.evaluate(p,v,root=tmp),lambda:mod.integer_pullback(p,v,root=tmp)]
  for fn in calls:fn()
  for n,b in raw.items():
   (tmp/n).write_bytes(b+b'\n')
   for fn in calls:reject(fn);counts['warm_pins']+=1
   (tmp/n).write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(path),'--help'],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'optimized reject');counts['optimized_rejections']=1
 return dict(status='PASS_INDEPENDENT_TARGET_FREE_MASS_HEIGHT',review_source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PARENT,author_pins=AUTHOR,counts=counts,forms=forms,negative_inverse_fixture=neg,scope='Four complete literal graphs and APIs; signed graph identity to endpoint and coefficient parents; direct natural/positive soundness and separate fresh-height completeness. Upper degrees only. No parent positive-zero bijection, author verifier, historical suites, or native Pell materialization.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root,a.artifacts)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'exact complete review receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts'])
if __name__=='__main__':main()
