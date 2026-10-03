#!/usr/bin/env python3
"""Independent complete-source and endpoint-domain review for four mass clocks."""
import argparse,copy,hashlib,itertools,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PARENT={'native_pell_factored_first_coefficient.json': 'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf',
 'native_pell_factored_first_coefficient.md': 'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528',
 'native_pell_factored_first_coefficient.py': 'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc',
 'residue_affine_packed_history.json': 'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421',
 'residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882',
 'residue_affine_packed_history.py': 'd06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4',
 'three_mass_unbounded_interface.json': 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e',
 'three_mass_unbounded_interface.md': 'd336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45',
 'three_mass_unbounded_interface.py': 'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a'}
AUTHOR={
 'three_mass_unbounded_endpoint_projection.py':'96d41f43190547fce121c5271e351af3d2bc99fa2226379e4d24f980bae998dd',
 'three_mass_unbounded_endpoint_projection.json':'a7856463c879e8c479facf713a66c0756705d84f0dd74639f28395227ebc2457',
 'three_mass_unbounded_endpoint_projection.md':'8a17b626dc4c2b3498614c0c2e8511c9adbd9765c4b3fd157f77a06d8174bd6c',
}
VARIANTS=('clock_incdec','clock_zero3','clock_nop','clock_positive3')
EXPECTED=((594,235,359,58,2344),(469,180,289,56,1192),(467,178,289,56,1192),(470,185,285,56,1192))
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
def diagonal(rows,free):
 def add(a,b,s=1):
  c=[0]*max(len(a),len(b))
  for i,x in enumerate(a):c[i]+=x
  for i,x in enumerate(b):c[i]+=s*x
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 def mul(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]+=x*y
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 e={x:[0,1]for x in free}
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else[a];b=e[b]if type(b)is str else[b];e[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else -1)
 return e

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



def literal(old):
 K=old['parent_metadata']['mapping']['K'];halt=old['parent_metadata']['mapping']['halt'];defs={n:(o,a,b)for n,o,a,b in old['source']}
 need(old['comparisons'][-1]==['final_positive','y']and len(old['comparisons'])==20,'last endpoint equality')
 need(defs['bridge_final_minus_one']==('-','final_positive',1)and defs['bridge_final_scaled']==('*',K,'bridge_final_minus_one')and defs['bridge_target']==('+','bridge_final_scaled',halt),'actual old endpoint cone')
 consumers=lambda name:[r[0]for r in old['source']if name in r[2:]]
 need(consumers('final_positive')==['bridge_final_minus_one']and consumers('bridge_final_minus_one')==['bridge_final_scaled']and consumers('bridge_final_scaled')==['bridge_target'],'private endpoint chain')
 need(consumers('height_slack')==['bridge_height_without_time'],'private height slack')
 hs=consumers('bridge_height_without_time');need(len(hs)==1,'one final height consumer');height=hs[0];need(defs[height]==('+','bridge_height_without_time','T'),'literal final height addition')
 need(not any(x in pair for pair in old['comparisons'][:-1]for x in('final_positive','bridge_final_minus_one','bridge_final_scaled','height_slack','bridge_height_without_time')),'no hidden comparison consumer')
 rows=[]
 for n,o,a,b in old['source']:
  if n=='bridge_final_minus_one':continue
  if n=='bridge_final_scaled':rows.append([n,'*',K,'y'])
  elif n=='bridge_target':rows.append([n,'+','bridge_final_scaled',halt-K])
  elif n==height:rows.extend([['endpoint_raised_height','+','bridge_height_without_time',K],[n,'+','endpoint_raised_height','T']])
  else:rows.append([n,o,a,b])
 pairs=copy.deepcopy(old['comparisons'][:-1]);poly=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):poly.extend([[f'ep_res{i}','-',a,b],[f'ep_sq{i}','*',f'ep_res{i}',f'ep_res{i}']])
 out='ep_sq0'
 for i in range(1,len(pairs)):n=f'ep_sum{i}';poly.append([n,'+',out,f'ep_sq{i}']);out=n
 return rows,pairs,poly,out,height

def pullback(p,v):
 e=dict(v);e['final_positive']=v['y'];e['height_slack']=v['height_slack']+p['mapping']['K'];return e

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
 while h<=n0+path[-1]+T+K or h<=max(qs):h*=2
 radix=next(r for r in p['source']if r[1]=='*'and r[3]=='bridge_height_square');C=radix[2];B=C*h*h;t=len(qs);P=B**t;J=(P-1)//(B-1)
 pack=lambda xs:sum(v*B**i for i,v in enumerate(xs));E=[pack([int(r==s)for r in residues])for s in range(1,m+1)];W=pack(qs)
 a0=min(a for a,d in mp['table']);classes=sorted({a for a,d in mp['table']}-{a0});Z=[pack([q if mp['table'][r-1][0]==a else 0 for q,r in zip(qs,residues)])for a in classes]
 v={n:1 for n in p['auxiliaries']};v.update(x=x,y=y,T=T,height_slack=h-n0-path[-1]-T-K,quotient_hat=W+1,global_slack=P-J-W-1-sum(Z)-len(Z),clock_quotient_hat=1+(pack(ticks)-T)//(B-1))
 v.update({f'edge{s}_hat':e+1 for s,e in enumerate(E)});v.update({f'product{s}_hat':z+1 for s,z in enumerate(Z)})
 need(min(v[n]for n in p['auxiliaries'])>0,'strict positive outer hats/slacks')
 # Execute only actual outer rows and the literal paid native padding interfaces.
 allowed={'native__q','native__scaled_A','native__padded_A','native__scaled_B','native__padded_B','native__scaled_Z','native__F3'}
 rows=[r for r in p['source']if not r[0].startswith('native__')or r[0]in allowed];env=numeric(rows,v)
 for a,b in(p['comparisons'][0],p['comparisons'][1],p['comparisons'][-1]):need(env[a]==env[b],'three literal outer equalities')
 H=(env['native__padded_A']-12)//16;M=(env['native__padded_B']-10)//16;A=(env['native__F3']-8)//16
 need(H&M==A and env[p['interfaces']['height']]==h and env['bridge_target']==path[-1],'joined AND and exact actual endpoints')
 need(T<B-1 and T<h and len(qs)<=m*h and len(set(path[:-1]))==len(qs),'clock no-wrap bounds')
 return dict(x=x,y=y,T=T,steps=t,height=h,height_slack=v['height_slack'],parent_height_slack=v['height_slack']+K,native_witnesses_materialized=False)

def verify(root,artifacts):
 raw=pins(root,PARENT);ab=pins(artifacts,AUTHOR);saved=json.loads(ab['three_mass_unbounded_endpoint_projection.json']);parent_receipt=json.loads(raw['native_pell_factored_first_coefficient.json'])
 need(saved['source_sha256']==AUTHOR['three_mass_unbounded_endpoint_projection.py']and exact(saved['parent_pins'],PARENT),'author source/receipt lineage')
 olds={f['packet']['variant']:f['packet']for f in parent_receipt['forms']if f['variant'].startswith('clock_')};children={f['packet']['variant']:f['packet']for f in saved['forms']}
 need(len(saved['forms'])==len(olds)==4 and set(children)==set(olds)==set(VARIANTS),'four complete source variants')
 path=Path(artifacts)/'three_mass_unbounded_endpoint_projection.py';mod=types.ModuleType('_authenticated_endpoint_author');mod.__file__=str(path);exec(compile(ab[path.name],str(path),'exec'),mod.__dict__)
 counts=dict(literal_complete_sources=0,complete_graph_identities=0,retained_operand_identities=0,retained_residual_identities=0,deleted_endpoint_zeros=0,paid_live_gates=0,degree_upper_bounds=0,numeric_identities=0,rational_identities=0,numeric_residuals=0,source_table_checks=0,outer_histories=0,y_zero_boundary=0,integer_chronology_cases=0,guards=0,copies=0,warm_pins=0)
 rng=random.Random(714593);forms=[]
 for variant,expected in zip(VARIANTS,EXPECTED):
  old=olds[variant];p=mod.build(variant,root=root);need(exact(p,children[variant])and exact(mod.canonical_parent(variant,root=root),old),'full saved canonical packets')
  need(exact(mod.rewrite(old,root=root),p)and exact(mod.checked(p,root=root),p),'canonical rewrite and check')
  rows,pairs,poly,out,height=literal(old);need(exact(p['source'],rows)and exact(p['comparisons'],pairs)and exact(p['polynomial_source'],poly)and p['output']==out,'whole independently rebuilt schedules')
  need(p['parameters']==['x','y','T']and p['auxiliaries']==[n for n in old['auxiliaries']if n!='final_positive']and p['domains']==dict(parameters='natural',auxiliaries='positive'),'precise full supplied domains')
  free=p['parameters']+p['auxiliaries'];need(len(free)==len(set(free)),'disjoint exact coordinates');M,A,d=ledger(poly,free,[out]);cm,ca,cd=ledger(rows,free,[v for pair in pairs for v in pair]);om,oa,_=ledger(old['polynomial_source'],old['parameters']+old['auxiliaries'],[old['output']]);ocm,oca,_=ledger(old['source'],old['parameters']+old['auxiliaries'],[v for pair in old['comparisons']for v in pair])
  need((M+A,M,A,len(p['auxiliaries']),d)==expected and(om-M,oa-A)==(1,2)and(ocm,oca)==(cm,ca),'entire paid count and unchanged certificate cost')
  def stated(m,a,deg,eq):return dict(operations=m+a,M=m,A=a,positive_witnesses=len(p['auxiliaries']),equations=eq,degree_upper_bound=deg,all_gates_live=True)
  need(exact(p['polynomial_ledger'],stated(M,A,d,None))and exact(p['certificate_ledger'],stated(cm,ca,cd,19)),'current certificate/full metadata')
  need(p['degree']['upper_bound']==d and p['degree']['exact_degree']is None,'upper-only degree statement');counts['degree_upper_bounds']+=1
  K=p['mapping']['K'];halt=p['mapping']['halt'];mp=p['mapping'];need(exact(mp,old['parent_metadata']['mapping'])and mp['initial']!=halt and 1<=mp['initial']<=K and 1<=halt<=K,'unchanged fixed program interface')
  need(exact(p['interfaces'],dict(height=height,input='bridge_input',target='bridge_target'))and exact(p['parent_pins'],PARENT)and exact(p['coefficient_transfer'],old['transfer']),'current ports and inherited local coefficient provenance')
  need(p['projection']['integer_pullback']==dict(final_positive='y',height_slack=f'height_slack+{K}')and p['projection']['full_polynomial_identity_under_pullback']is True and p['projection']['same_coordinate_polynomial_identity']is False and p['projection']['natural_zero_image']==f'Parent zeros with height_slack>{K}','exact graph and slice metadata')
  ring=RingDAG();before=ring.run(old['polynomial_source'],old['parameters']+old['auxiliaries'],dict(final_positive=ring.val('y'),height_slack=ring.add(ring.val('height_slack'),ring.val(K))));after=ring.run(poly,free)
  # Independent direct coefficient normalization proves the affine fronts and
  # every downstream expression, without author-provided cut equalities.
  target=ring.add(ring.scale(ring.val('y'),K),ring.val(halt-K));wantheight=ring.add(ring.add(ring.add(ring.scale(ring.val('x'),K),ring.scale(ring.val('y'),K)),ring.val(mp['initial']+halt)),ring.add(ring.val('T'),ring.val('height_slack')))
  need(after['bridge_target']==before['bridge_target']==target and after[height]==before[height]==wantheight,'literal affine height and target identities')
  need(before[old['output']]==after[out],'entire exact polynomial graph identity, no cuts');counts['complete_graph_identities']+=1
  for a,b in pairs:
   need(before[a]==after[a]and before[b]==after[b],'complete retained comparison operands');counts['retained_operand_identities']+=2
   need(ring.add(before[a],before[b],-1)==ring.add(after[a],after[b],-1),'complete residual');counts['retained_residual_identities']+=1
  need(ring.add(before['final_positive'],before['y'],-1)==(),'deleted output comparison zero');counts['deleted_endpoint_zeros']+=1
  counts['literal_complete_sources']+=1;counts['paid_live_gates']+=M+A
  radix=next(r for r in rows if r[1]=='*'and r[3]=='bridge_height_square');C=radix[2];need(type(C)is int and C>0 and C&(C-1)==0 and C>=max(4,mp['modulus']+1,1+max(a+b for a,b in mp['table']),2384*mp['modulus']+2),'actual safe dyadic radix multiplier')
  need(len(mp['table'])==len(mp['clocks'])==mp['modulus']and all(a>=0 and b>0 for a,b in mp['table']),'total positive map premises')
  for s in range(1,mp['modulus']+1):
   for q in(0,1,5):
    n=mp['modulus']*q+s;a,b=mp['table'][s-1];c,e=mp['clocks'][s-1]
    need(affine_table_step(mp,variant,n)==(a*q+b,c*q+e),'independent literal source and clock macro');counts['source_table_checks']+=1
  for case in range(20):
   v={n:rng.randrange(1,4)for n in free}
   if case<5:v.update({n:rng.randrange(4)for n in p['parameters']})
   elif case>=5:v={n:rng.randrange(-2,4)for n in free}
   if case>=16:v={n:Fraction(x,3)for n,x in v.items()};counts['rational_identities']+=1
   a=numeric(old['polynomial_source'],pullback(p,v));b=numeric(poly,v);need(a[old['output']]==b[out],'entire numeric pullback');counts['numeric_identities']+=1
   for l,r in pairs:need(a[l]-a[r]==b[l]-b[r],'every evaluated residual');counts['numeric_residuals']+=1
   if case<16:need(mod.evaluate(p,v,signed=case>=5,root=root)==b[out]and exact(mod.integer_pullback(p,v,root=root),pullback(p,v)),'public integer algebra')
  v={n:1 for n in free};v.update(x=0,y=0,T=0);e=numeric(rows,v)
  need(e[height]==mp['initial']+halt+1>0 and e['bridge_target']==halt-K<=0 and mod.integer_pullback(p,v,root=root)['final_positive']==0,'y0 remains natural but old positive coordinate fails off zeros')
  need(mod.evaluate(p,v,root=root)==numeric(poly,v)[out],'y0 is not domain-rejected');counts['y_zero_boundary']+=1
  fixtures=[]
  for x in range(18):
   f=finite_outer(p,x)
   if f is not None:fixtures.append(f);counts['outer_histories']+=1
  forms.append(dict(variant=variant,M=M,A=A,operations=M+A,positive_witnesses=len(p['auxiliaries']),comparisons=19,degree_upper_bound=d,exact_degree=None,radix_multiplier=C,outer_histories=fixtures))
 # Direct finite verification of the arbitrary-INTEGER-target chronology lemma.
 for B in(2,3,4):
  for t in(1,2,3):
   for curr in itertools.product(range(1,B),repeat=t):
    for nxt in itertools.product(range(1,B),repeat=t):
     cw=sum(c*B**i for i,c in enumerate(curr));nw=sum(n*B**i for i,n in enumerate(nxt))
     for initial in range(1,B):
      for target in range(-3,B+2):
       need((B*nw+initial==cw+B**t*target)==(initial==curr[0]and all(nxt[i]==curr[i+1]for i in range(t-1))and target==nxt[-1]),'integer chronology including nonpositive/unbounded trial target');counts['integer_chronology_cases']+=1
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise ValueError('Malformed canonical API accepted')
 for variant in(None,True,0,'bad'):
  for fn in(mod.build,mod.canonical_parent):reject(lambda fn=fn,variant=variant:fn(variant,root=root))
 p=mod.build(root=root);old=olds['clock_incdec'];v={n:1 for n in p['parameters']+p['auxiliaries']};v.update(x=0,y=0,T=0)
 for key in p:
  q=copy.deepcopy(p);del q[key];reject(lambda q=q:mod.checked(q,root=root))
 for key in old:
  q=copy.deepcopy(old);del q[key];reject(lambda q=q:mod.rewrite(q,root=root))
 for key in('source','comparisons','parameters','auxiliaries'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['polynomial_ledger']['M']=float(q['polynomial_ledger']['M']);reject(lambda:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['degree']['exact_degree']=2344;reject(lambda:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['projection']['same_coordinate_polynomial_identity']=True;reject(lambda:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['polynomial_source'][-1][1]='-';reject(lambda:mod.checked(q,root=root))
 for val in(True,1.0,Fraction(1)):
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
   q=mod.build(root=root);q[key].clear();need(exact(mod.build(root=root),p),'independent mutable packet field');counts['copies']+=1
 for fn in(lambda:mod.canonical_parent(root=root),lambda:mod.rewrite(old,root=root),lambda:mod.checked(p,root=root)):
  q=fn();q['source'].clear();need(exact(mod.build(root=root),p)and exact(mod.canonical_parent(root=root),old),'fresh canonical accessor');counts['copies']+=1
 q=mod.polynomial_source(p,root=root);q.clear();need(exact(mod.polynomial_source(p,root=root),p['polynomial_source']),'source accessor isolated');counts['copies']+=1
 q=mod.integer_pullback(p,v,root=root);q['height_slack']=0;need(v['height_slack']==1,'pullback assignment copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='endpoint_review_pins_')as tmp:
  tmp=Path(tmp)
  for n,b in raw.items():(tmp/n).write_bytes(b)
  mod.build(root=tmp)
  for n,b in raw.items():
   (tmp/n).write_bytes(b+b'\n')
   for fn in(lambda:mod.build(root=tmp),lambda:mod.canonical_parent(root=tmp),lambda:mod.checked(p,root=tmp),lambda:mod.evaluate(p,v,root=tmp),lambda:mod.integer_pullback(p,v,root=tmp)):reject(fn);counts['warm_pins']+=1
   (tmp/n).write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(path)],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'optimized reject');counts['optimized_rejections']=1
 return dict(status='PASS_INDEPENDENT_MASS_UNBOUNDED_ENDPOINT_PROJECTION',review_source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PARENT,author_pins=AUTHOR,counts=counts,forms=forms,scope='Four complete whole-source graph identities and mixed natural/positive endpoint theorem, parent zero slice eta_old>K, and separate fresh-height completeness. Native theorem inherited; no huge Pell witnesses or historical suites executed.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root,a.artifacts)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'exact complete review receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts'])
if __name__=='__main__':main()
