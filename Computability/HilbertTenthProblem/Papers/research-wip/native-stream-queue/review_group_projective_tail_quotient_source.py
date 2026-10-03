#!/usr/bin/env python3
"""Independent complete-source/degree/API review of one projective-tail quotient shift.
Uses no author verifier or historical compiler execution. Standard library only.
"""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
 '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90',
 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7',
 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e',
 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb',
 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb',
 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b',
 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952',
 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7',
 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39',
 'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965',
 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00',
 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605',
 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c'}
AUTHOR={'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27',
 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a',
 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610'}
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



FACTORS=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit']
EXPECTED_DEGREES=[391,698,500,308,308,616,2]
def expected_parent(saved):
 rows=saved['source'];nodes={r[0]for r in rows};free=sorted({v for r in rows for v in r[2:]if type(v)is str and v not in nodes})
 pairs=[[f'history__left{i}',f'history__right{i}']for i in range(4)]+[['eight_units',1],['controller__flow_left','controller__flow_right']]
 return dict(source=rows,output='joint_outer_output',comparisons=pairs,parameters=['x'],auxiliaries=[n for n in free if n!='x'],domains={'parameters':'positive','auxiliaries':'positive'},historical_parent_ledger=saved['default_ledger'])

def expected_finalizer():
 rows=[];pairs=[[f'history__left{i}',f'history__right{i}']for i in range(4)]+[['controller__flow_left','controller__flow_right']]
 for i,(a,b)in zip([0,1,2,3,5],pairs):rows.extend([[f'joint_outer_residual{i}','-',a,b],[f'joint_outer_square{i}','*',f'joint_outer_residual{i}',f'joint_outer_residual{i}']])
 prev='joint_outer_square0'
 for i,sq in enumerate(['joint_outer_square1','joint_outer_square2','joint_outer_square3','joint_outer_square5'],1):
  name=f'joint_outer_sum{i}';rows.append([name,'+',prev,sq]);prev=name
 rows.extend([['joint_outer_positive','+',prev,1],['joint_outer_product','*','eight_units','joint_outer_positive'],['joint_outer_output','-','joint_outer_product',1]])
 return rows

def parent_and_child(p,q):
 rows=p['source'];d={n:(o,a,b)for n,o,a,b in rows};free=p['parameters']+p['auxiliaries']
 need(rows[227:]==expected_finalizer(),'literal finalizer U*(1+five squares)-1')
 need(d['shifted_native_quotient']==('+','selection__w','packed_top_sum')and d['selection__wn2']==('*','shifted_native_quotient','selection__q'),'literal native quotient and X')
 expected={'packed_z_product':('*','packed_q_minus','selection__F3'),'packed_q_minus':('-','selection__q',1),'packed_q_plus':('+','selection__q',1),'packed_middle_sum':('+','selection__padded_B','packed_z_product'),'packed_middle_product':('*','packed_q_plus','packed_middle_sum'),'packed_top_sum':('+','selection__padded_A','packed_middle_product'),'selection__bs_packed':('*','packed_q_minus','packed_top_sum'),'selection__padded_A':('+','selection__scaled_A',13),'selection__padded_B':('+','selection__scaled_B',10),'selection__F3':('+','selection__scaled_Z',8),'selection__scaled_A':('*',16,'range_H'),'selection__scaled_B':('*',16,'range_M'),'selection__scaled_Z':('*',16,'range_Z')}
 need(all(d[n]==v for n,v in expected.items()),'literal S/Z0 and positive folded padding interfaces')
 need([n for n,o,a,b in rows if 'selection__w'in(a,b)]==['shifted_native_quotient']and [n for n,o,a,b in rows if 'shifted_native_quotient'in(a,b)]==['selection__wn2'],'all supplied quotient consumers')
 deps={n:{n}for n in free}
 for n,o,a,b in rows:deps[n]=(deps[a]if type(a)is str else set())|(deps[b]if type(b)is str else set())
 need('selection__w'not in deps['packed_top_sum']|deps['packed_z_product'],'actual complete offset dependency independence')
 child=copy.deepcopy(rows);idx=next(i for i,r in enumerate(rows)if r[0]=='shifted_native_quotient');child[idx]=['shifted_native_quotient','+','selection__w','packed_z_product']
 need(q['source']==child and q['source'][227:]==rows[227:]and q['comparisons']==p['comparisons'],'exact one-operand edit; all finalizers and six comparisons retained')
 need(all(q[k]==p[k]for k in('output','parameters','auxiliaries','domains','historical_parent_ledger')),'complete interface and historical metadata')
 # No quotient cut: execute the real prefix to construct the affine pullback,
 # then directly normalize both entire literal ring DAGs.
 ring=RingDAG();ne=ring.run(child,free);pull=ring.add(ring.add(ring.val('selection__w'),ne['packed_z_product']),ne['packed_top_sum'],-1)
 oe=ring.run(rows,free,{'selection__w':pull})
 need(all(oe[n]==ne[n]for n,o,a,b in child),'all244 literal gates under direct signed pullback')
 for a,b in p['comparisons']:
  val=lambda e,x:e[x]if type(x)is str else ring.val(x)
  need(ring.add(val(oe,a),val(oe,b),-1)==ring.add(val(ne,a),val(ne,b),-1),'all six complete residuals')
 need(oe[p['output']]==ne[q['output']],'direct complete polynomial identity')
 need(d['history__input_product']==('*',24,'x')and d['history__u']==('+','history__input_product',13)and d['D']==('+','history__u','height_slack'),'fully paid ordinary input alpha24 beta12')
 return idx

# Tiny independent exact polynomial expansion for the alternative main-norm
# factorization, in atoms X,a,c,gamma. H=4a+3 is also expanded here.
def smadd(a,b,s=1):
 r=dict(a)
 for k,v in b.items():r[k]=r.get(k,0)+s*v
 return{k:v for k,v in r.items()if v}
def smmul(a,b):
 r={}
 for u,x in a.items():
  for v,y in b.items():
   k=tuple(i+j for i,j in zip(u,v));r[k]=r.get(k,0)+x*y
 return{k:v for k,v in r.items()if v}
def scalar(n):return{(0,0,0,0):n}if n else{}
def main_identity():
 X,a,c,g=[{tuple(int(j==i)for j in range(4)):1}for i in range(4)];ac=smmul(a,c);H=smadd(smmul(scalar(4),a),scalar(3));Delta=smadd(smmul(a,a),H);d=smadd(smadd(X,ac),g)
 original=smadd(smmul(d,d),smmul(Delta,smmul(c,c)),-1);u=smadd(X,g);new=smadd(smmul(u,smadd(smmul(scalar(2),ac),u)),smmul(H,smmul(c,c)),-1)
 need(original==new,'independent exact main factorization (X+gamma)*(2ac+X+gamma)-Hc²')
 return len(original)

def upper_bound(p):
 rows=p['source'];actual={n:(o,a,b)for n,o,a,b in rows};X,a,c,g,H='selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5'
 expected={'selection__cam2':('*',c,a),'selection__D1':('+',X,'selection__cam2'),'selection__R14':('+','selection__D1',g),'selection__L15':('*','selection__R14','selection__R14'),'selection__a_square':('*',a,a),H:('+','selection__a4',3),'selection__a4':('*',4,a),g:('*','selection__ga',H),'selection__A':('+','selection__a_square',H),'selection__c2':('*',c,c),'selection__Ac2':('*','selection__A','selection__c2'),'selection__R15':('-','selection__L15','selection__Ac2')}
 need(all(actual[n]==v for n,v in expected.items()),'actual complete main factorization cone')
 d={n:1 for n in p['parameters']+p['auxiliaries']}
 for n,o,l,r in rows:
  dl=d[l]if type(l)is str else 0;dr=d[r]if type(r)is str else 0
  if n=='selection__R15':du=max(d[X],d[g]);d[n]=max(du+max(d[a]+d[c],du),d[H]+2*d[c])
  else:d[n]=dl+dr if o=='*'else max(dl,dr)
 need(d[p['output']]==2829 and [d[n]for n in FACTORS]==EXPECTED_DEGREES,'independent all-gate upper-degree argument')
 return d

# Whole dense univariate polynomial arithmetic. Each free coordinate is its
# weight times t. No leading-term cuts or author degree routine are used.
def full_coefficients(p,weights,prime):
 def trim(v):
  while len(v)>1 and v[-1]==0:v.pop()
  return v
 def add(a,b,sgn=1):
  n=max(len(a),len(b));r=[0]*n
  for i,v in enumerate(a):r[i]=v
  for i,v in enumerate(b):r[i]=(r[i]+sgn*v)%prime
  return trim(r)
 def mul(a,b):
  if len(a)>len(b):a,b=b,a
  r=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   if x:
    for j,y in enumerate(b):r[i+j]+=x*y
  return trim([x%prime for x in r])
 e={n:[0,w%prime]for n,w in weights.items()}
 for n,o,a,b in p['source']:
  a=e[a]if type(a)is str else[a%prime];b=e[b]if type(b)is str else[b%prime];e[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else -1)
 return e

def verify(root,artifacts):
 parents=pins(root,PINS);author=pins(artifacts,AUTHOR);saved=json.loads(author['group_projective_tail_quotient_shift.json']);old=expected_parent(json.loads(parents['group_projective_product_radix_scale.json']));p=saved['packet']
 need(saved['source_sha256']==AUTHOR['group_projective_tail_quotient_shift.py']and exact(saved['pins'],PINS)and exact(p['parent_pins'],PINS),'independent authenticated entire inventory')
 idx=parent_and_child(old,p);counts={'whole_gate_identities':244,'comparison_identities':6,'whole_polynomial_identities':1,'main_expansion_terms':main_identity()};free=p['parameters']+p['auxiliaries']
 M,A,_=ledger(p['source'],free,[p['output']]);cm,ca,_=ledger(p['source'][:227],free,[v for pair in p['comparisons']for v in pair]);need((M,A,cm,ca,len(free),len(p['comparisons']))==(103,141,97,130,37,6),'complete paid live source and certificate')
 want=dict(operations=244,M=103,A=141,certificate_operations=227,finalizer_operations=17,comparisons=6,positive_witnesses=36,all_gates_live=True);need(exact(p['ledger'],want),'all current ledger fields');counts['paid_live_gates']=M+A
 projection={'parent':'group_projective_product_radix_scale','signed_pullback':'w_parent=w+packed_z_product-packed_top_sum','positive_parent_embedding':'w_child=w_parent+packed_top_sum-packed_z_product','same_coordinate_polynomial_identity':False,'all_value_identity_under_signed_pullback':True,'positive_zero_bijection':True,'positive_reverse_only_after_native_recovery':True,'X_gt_r_assumed_in_bootstrap':False}
 need(exact(p['quotient_projection'],projection)and p['source_scope']=='Exactly the pinned default ten-letter table, alpha24/beta12, controller range reuse, computed P. The general fixed-table proof does not instantiate a numerical universal alphabet.','current semantic scope metadata')
 bound=upper_bound(p);degree=p['degree_certificate'];need(degree['exact_degree']==degree['upper_degree']==2829 and degree['factor_degrees']==dict(zip(FACTORS,EXPECTED_DEGREES))and degree['all_gate_leaders_nonzero']is True,'claimed degree fields')
 need(degree['prime']==1000000007 and set(degree['weights'])==set(free)and all(type(w)is int and w>0 for w in degree['weights'].values()),'actual degree specialization interface')
 cases=[]
 for prime,weights in [(1000000007,degree['weights']),(1000000009,{n:i+2 for i,n in enumerate(sorted(free))})]:
  env=full_coefficients(p,weights,prime);coeff=env[p['output']]
  need(len(coeff)-1==2829 and coeff[-1]!=0,'independent complete all-coefficient degree witness')
  need(all(len(env[n])-1==bound[n]for n,o,a,b in p['source']),'every full polynomial gate attains independent upper bound')
  need([len(env[n])-1 for n in FACTORS]==EXPECTED_DEGREES,'actual unit polynomial degrees')
  if prime==degree['prime']:need(coeff[-1]==degree['leading_coefficient_mod_prime']==935638906,'published coefficient reproduced by whole polynomial')
  cases.append(dict(prime=prime,weights=weights,degree=len(coeff)-1,leading_coefficient=coeff[-1],complete_coefficient_sha256=sha(json.dumps(coeff,separators=(',',':')).encode())))
 counts['full_polynomial_coefficient_expansions']=2;counts['all_gate_polynomial_degree_checks']=488
 # Source-only load solely for the bounded public builder/evaluator guard audit.
 path=Path(artifacts)/'group_projective_tail_quotient_shift.py';mod=types.ModuleType('_independent_tail_public');mod.__file__=str(path);exec(compile(author[path.name],str(path),'exec'),mod.__dict__)
 need(exact(mod.canonical_parent(root=root),old)and exact(mod.build(root=root),p)and exact(mod.rewrite(old,root=root),p)and exact(mod.checked(p,root=root),p),'all canonical source entrypoints')
 rng=random.Random(2829244);counts.update(numeric_full_identities=0,numeric_gate_identities=0,rational_cases=0,numeric_residuals=0,positive_parent_embeddings=0,guards=0,copy_checks=0,strict_pin_checks=0)
 for case in range(24):
  v={n:rng.randrange(1,4)if case<8 else rng.randrange(-2,4)for n in free}
  if case>=18:v={n:Fraction(x,3)for n,x in v.items()};counts['rational_cases']+=1
  ne=numeric(p['source'],v);pv=dict(v);pv['selection__w']+=ne['packed_z_product']-ne['packed_top_sum'];oe=numeric(old['source'],pv)
  need(all(ne[n]==oe[n]for n,o,a,b in p['source']),'every actual numeric gate');counts['numeric_gate_identities']+=244
  need(ne[p['output']]==oe[old['output']],'complete signed evaluation');counts['numeric_full_identities']+=1
  for a,b in p['comparisons']:
   val=lambda e,z:e[z]if type(z)is str else z
   need(val(ne,a)-val(ne,b)==val(oe,a)-val(oe,b),'every exact residual');counts['numeric_residuals']+=1
  if case<18:need(mod.evaluate(p,v,signed=case>=8,root=root)==ne[p['output']]and exact(mod.integer_pullback(p,v,root=root),pv),'actual integer public evaluation and signed pullback')
 for case in range(8):
  v={n:rng.randrange(1,4)for n in free};oe=numeric(old['source'],v);cv=dict(v);cv['selection__w']+=oe['packed_top_sum']-oe['packed_z_product'];ne=numeric(p['source'],cv)
  need(oe['packed_top_sum']>oe['packed_z_product']>0 and min(cv.values())>0 and ne[p['output']]==oe[old['output']],'actual unconditional positive old-to-new embedding');counts['positive_parent_embeddings']+=1
 v={n:1 for n in free};e=numeric(p['source'],v);negative=1+e['packed_z_product']-e['packed_top_sum'];need(negative<0 and e[p['output']]!=0,'actual off-zero signed inverse only')
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError,FileNotFoundError):counts['guards']+=1
  else:raise ValueError('expected rejection')
 for bad in(None,{},dict(p,output='eight_units'),dict(p,degree_certificate={}),dict(p,source=p['source'][:-1]),dict(p,domains={'parameters':'natural','auxiliaries':'positive'})):
  reject(lambda bad=bad:mod.checked(bad,root=root))
 for obj in('parent','child'):
  base=old if obj=='parent'else p
  variants=[]
  z=copy.deepcopy(base);z['source'][0][2]=24.0;variants.append(z)
  z=copy.deepcopy(base);z['source'][0][2]=True;variants.append(z)
  z=copy.deepcopy(base);z['source'][idx][3]='packed_top_sum'if obj=='child'else'packed_z_product';variants.append(z)
  z=copy.deepcopy(base);z['auxiliaries'].remove('selection__w');variants.append(z)
  z=copy.deepcopy(base);z['comparisons'][4][1]=True;variants.append(z)
  for z in variants:reject(lambda z=z,obj=obj:mod.rewrite(z,root=root)if obj=='parent'else mod.checked(z,root=root))
 for x in(True,1.0,Fraction(1,1),0,-1):
  z=dict(v,x=x);reject(lambda z=z:mod.evaluate(p,z,root=root))
 for z in({},dict(v,extra=1),dict(v,x=True)):reject(lambda z=z:mod.integer_pullback(p,z,root=root))
 for signed in(1,None,'yes'):reject(lambda signed=signed:mod.evaluate(p,v,signed=signed,root=root))
 for maker in(lambda:mod.build(root=root),lambda:mod.checked(p,root=root),lambda:mod.rewrite(old,root=root)):
  for key in('source','auxiliaries','parent_pins','quotient_projection','degree_certificate'):
   z=maker();z[key].clear();need(exact(mod.build(root=root),p),'fresh canonical copies');counts['copy_checks']+=1
 z=mod.canonical_parent(root=root);z['source'].clear();need(exact(mod.canonical_parent(root=root),old),'parent copied');counts['copy_checks']+=1
 entries=[lambda rr:mod.canonical_parent(root=rr),lambda rr:mod.build(root=rr),lambda rr:mod.rewrite(old,root=rr),lambda rr:mod.checked(p,root=rr),lambda rr:mod.evaluate(p,v,root=rr),lambda rr:mod.integer_pullback(p,v,root=rr)]
 with tempfile.TemporaryDirectory(prefix='tail_quotient_review_')as td:
  rr=Path(td)/'Papers'/'research-wip'/'native-stream-queue';rr.mkdir(parents=True)
  for n,b in parents.items():dest=rr/n;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  need(exact(mod.build(root=rr),p),'relocated canonical reconstruction')
  for n,b in parents.items():
   dest=rr/n;dest.write_bytes(b+b'\n')
   for entry in entries:reject(lambda entry=entry:entry(rr));counts['strict_pin_checks']+=1
   dest.write_bytes(b)
 run=subprocess.run([sys.executable,'-O',str(path),'--root',str(root)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 need(run.returncode!=0 and 'Run without -O'in run.stderr,'optimized mode rejects at entry');counts['guards']+=1
 return dict(schema='independent-projective-tail-source-review-v1',status='PASS',review_source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,parent_pins=PINS,scope='One literal244 default source; source/API/degree/all-value proof. Native positive-zero bootstrap separately reviewed; no universal numerical alphabet or family census.',counts=counts,ledger=want,changed_source_row=idx,whole_polynomial_degree_cases=cases,off_zero_inverse={'negative':True,'not_a_zero':True,'sha256':sha(str(negative).encode())})

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--artifacts',default=str(Path(__file__).resolve().parent));ap.add_argument('--output');ap.add_argument('--expect');a=ap.parse_args();r=verify(a.root,a.artifacts)
 if a.expect:need(exact(r,json.loads(Path(a.expect).read_text())),'exact typed review receipt')
 if a.output:Path(a.output).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':'PASS','counts':r['counts'],'ledger':r['ledger']},sort_keys=True))
if __name__=='__main__':main()
