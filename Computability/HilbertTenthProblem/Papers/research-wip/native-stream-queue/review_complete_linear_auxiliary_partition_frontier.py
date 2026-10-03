#!/usr/bin/env python3
"""Independent subset-partition objectives and actual saved-finalist audit."""
import argparse,hashlib,json
from collections import Counter
from functools import lru_cache
from fractions import Fraction
from pathlib import Path

PINS={'../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0', 'complete75_asymmetric_factor_partitions.json': '6d9112e67d18306bb6aa8aaf8660432d7dff2398e198c3018907e1c79c70a42f', 'complete75_asymmetric_factor_partitions.md': '1e54eb9a8b5e704947ed78d69716c79ec2e6e46d187e700960bf1b1b700eebf2', 'complete75_asymmetric_factor_partitions.py': 'b772fc579454b13ce30e5f9feaad25206d35b04af3cb4dffb1d76d1246d4c515', 'complete75_asymmetric_linear_gap_tradeoffs.json': 'dcd2c462e8405bc4535682a624832e8a8ad044a86504fd0b46df6700ab5c0f26', 'complete75_asymmetric_linear_gap_tradeoffs.md': '93aac323a64bf6c7e8946faeddf90de5606d8c133d3bd611a0806269e8f92638', 'complete75_asymmetric_linear_gap_tradeoffs.py': 'a08626905d8a790ec1458bc8e7302b9f28e251b84818695d2fa3c640a8c9dcf2', 'complete75_asymmetric_scale_tradeoffs.json': '47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_asymmetric_scale_tradeoffs.py': 'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660', 'complete75_auxiliary_gap_degree_tradeoffs.json': '741592f41a1ef6df2797a23e1380e3c208b093379b0379a4aedf36700f9592d9', 'complete75_auxiliary_gap_degree_tradeoffs.md': '315792b00530a4517e7f79f3c423f860268145803eb9bc364a235782aad69755', 'complete75_auxiliary_gap_degree_tradeoffs.py': 'f359f6d07c8c8e18d1f41b53e198f1bba70f5d43dcad049e1e12600260521312', 'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39', 'complete75_coupled_index_linear88.py': 'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed', 'complete75_linear_input_degree_tradeoffs.json': '15f62dee3287c5a3d976f43add43e74e755f8e7e2b59787b837c87c2cdf35d84', 'complete75_linear_input_degree_tradeoffs.md': '8b3cb44cbd2b979175ebfe4731556384469adfa93890ca7b01f70fa192a9682b', 'complete75_linear_input_degree_tradeoffs.py': 'cd06f404f5a9cbb0f5b6116ba13498321bfeba845f827541833ef4a1f3c882bc', 'complete75_linear_input_modulus89.json': 'c6758bc90adeb331ddfb8e9512d8974035e46701cd0a2c4ebd378b5f7c59c9fd', 'complete75_linear_input_modulus89.md': '855a1e038dac816043c040decd35d33818e0da25e1e9e1713a9a454bcc531444', 'complete75_linear_input_modulus89.py': 'dfcee79fb8564a29bba3a243da4fbce848709d0de5117426222b39b869ef4efb', 'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b', 'complete75_normalized_strong87.py': '7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749', 'complete75_reversed_auxiliary89.md': '4eddb6627b6261b1d8f8617006e443908574c0b7b2d3fdda15ff85dc86bd9700', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e', 'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b', 'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f', 'complete86_first_root_partitions.json': '7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5', 'complete86_first_root_partitions.md': '7325cf4fcf88bd5c20bd3d556eef7c8a313f3aee914e637483dc065d2417c2e0', 'complete86_first_root_partitions.py': 'b139097ed009580cfe8fc7707e373ec9ecafdecb886bd2cf037d615a06d35988', 'complete86_ordinary_auxiliary_projection.json': 'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6', 'complete86_ordinary_auxiliary_projection.md': 'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570', 'complete86_ordinary_auxiliary_projection.py': '130c8a09570866f3b510f4092aef3ab7fd61154f6c8776fcdba870d80a59019d', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45', 'complete_auxiliary_unit_partition_frontier.json': 'e09f0bb97afa4cfdfdbc354fbc0c886bfdb608d6731a55b8db8314a3c7a89097', 'complete_auxiliary_unit_partition_frontier.md': '690de29dfb86f7c19709d2c88d54379267ca2e73b64cbc683b181fa07324e616', 'complete_auxiliary_unit_partition_frontier.py': '0e234ba9f4cb1889417ba281b1fe217906ac84c9c7c199395b8dfa36b2914f17', 'review_complete85_auxiliary_bezout_math.json': '9cdbf027fe1da74975043f4c5ba022b04e0e73eb92166cf2a1ed2ec1cc258d49', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', 'review_complete85_auxiliary_bezout_math.py': 'ea1c7d39b2afc6c1a004facac777b6ad97af89c5c92309e489439928abcbdd65', 'transport_shear_frontier_probe.json': '4e58078d955a9cc7d5642dea24e8f1ac76ac71da2f8b82b568bb27794d25d865', 'transport_shear_partition_census.json': '93becb442a3809f855053f414e8478e92b2b5eed0ff84c1cb22996b9a0ac1ef0', 'transport_shear_partition_census.md': '27f38b0757d220e605565c6d63ff3470a73292a9cb632a8c529e8d1b89804469', 'transport_shear_partition_census.py': 'd58f6fd00bc658a566a3ae2f1a3c8b9c7fd457b272291b595132c75a7cbf1d1c', 'complete_linear_auxiliary_quotient_family.py': '07d9bd66528a213929475ab560a0265fa872c88599d9b9700fdc5d4910a31153', 'complete_linear_auxiliary_quotient_family.json': 'b2cb2723c3a335df84b8f3472371912beb28cc52b0f07d0b68d4d0d0fcb6a2b5', 'complete_linear_auxiliary_quotient_family.md': '7e85f2e3a236872da22be9d85222289475ebfb825b733e3e881c5a2b220eed66', 'review_linear_auxiliary_quotient_family.py': '54f2b7e9bd1abfb6242e29cb46ca98ccaee1f752dff344a0a38e6d83b1a847ed', 'review_linear_auxiliary_quotient_family.json': 'c19401eac5275ade18af2fbf6ea3c9cacdc40cd36f93dd97b63fc57b0ab77acc', 'review_linear_auxiliary_quotient_family.md': '09cf75696613675829764934cf9c3e65fe8bc5494f5980957383bc03ef60dafd'}
AUTHOR={'complete_linear_auxiliary_partition_frontier.py': '57864764f89891cb8c980713d1e6aa4f56de34fc9df3c39fbf628d059db63309', 'complete_linear_auxiliary_partition_frontier.json': '74523988d0194af3154fddec3193aacc6cc4272e7c5a20299ee90a6e67c1b365', 'complete_linear_auxiliary_partition_frontier.md': '5d4cabc57cbaca43a05def7fafd1275bae906facf31bcfc7a91dde18d4421caf'}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
MODES=['root_ordinate','root_gap','gap_ordinate','gap_gap']
EXPECTED_WEIGHTS=[[22,18,20,28,7,2,22],[22,18,20,22,7,2,22],[12,18,20,28,7,2,22],[12,18,20,22,7,2,22]]
def require(ok,message='independent check failed'):
 if not ok:raise ValueError(message)
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def sha(x):return hashlib.sha256(x).hexdigest()
def same(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
 if isinstance(a,list):return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b

# Elementary sparse operations adapted from this reviewer's earlier seven-unit
# audit; no predecessor helper, author emitter or historical verifier executes.
class Ring:
 def __init__(self,names):
  self.names=sorted(names);self.index={n:i for i,n in enumerate(self.names)};self.zero=(0,)*len(names)
  self.weights=[int(n not in FIXED)for n in self.names]
 def const(self,n):return {self.zero:n}if n else {}
 def var(self,n):
  v=list(self.zero);v[self.index[n]]=1;return {tuple(v):1}
 def add(self,a,b,sign=1):
  c=a.copy()
  for m,v in b.items():c[m]=c.get(m,0)+sign*v
  return {m:v for m,v in c.items()if v}
 def mul(self,a,b):
  c={}
  for m,v in a.items():
   for n,w in b.items():
    k=tuple(x+y for x,y in zip(m,n));c[k]=c.get(k,0)+v*w
  return {m:v for m,v in c.items()if v}
 def product(self,xs):
  result=self.const(1)
  for x in xs:result=self.mul(result,x)
  return result
 def leader(self,p):
  require(bool(p),'nonzero polynomial')
  ds={m:sum(e*w for e,w in zip(m,self.weights))for m in p};d=max(ds.values())
  return d,{m:p[m]for m in p if ds[m]==d}
 def serial(self,p):return [[[[n,m[i]]for i,n in enumerate(self.names)if m[i]],v]for m,v in sorted(p.items())]
 def parse(self,terms):
  out={}
  for monomial,c in terms:
   m=list(self.zero)
   for n,e in monomial:m[self.index[n]]=e
   require(tuple(m)not in out);out[tuple(m)]=c
  return out
 def evaluator(self,source):
  defs={n:(op,a,b)for n,op,a,b in source};cache={n:self.var(n)for n in self.names}
  def at(n):
   if type(n)is int:return self.const(n)
   if n not in cache:
    op,a,b=defs[n];a,b=at(a),at(b);cache[n]=self.mul(a,b)if op=='*'else self.add(a,b,1 if op=='+'else -1)
   return cache[n]
  return at

def extract_core(p):
 defs={r[0]:r[2:]for r in p['source']};live=set()
 def visit(x):
  if type(x)is str and x in defs and x not in live:
   live.add(x)
   for y in defs[x]:visit(y)
 for n in FACTORS:visit(n)
 return [r[:]for r in p['source']if r[0]in live]

def ledger(rows,free,outputs):
 known=set(free);defs={};c=Counter()
 require(len(known)==len(free))
 for n,op,a,b in rows:
  require(n not in known and op in ('+','-','*'))
  require(all(type(v)is int or type(v)is str and v in known for v in (a,b)))
  known.add(n);defs[n]=[a,b];c['M'if op=='*'else 'A']+=1
 live=set(outputs)
 for n,op,a,b in reversed(rows):
  if n in live:live.update(v for v in (a,b)if type(v)is str)
 require(live==known,'complete gate/port liveness')
 return {'operations':len(rows),'M':c['M'],'A':c['A']}

@lru_cache(None)
def subsets_partition(mask):
 if mask==0:return ((),)
 pivot=mask&-mask;rest=mask^pivot;sub=rest;result=[]
 while True:
  block=pivot|sub
  result.extend((block,)+tail for tail in subsets_partition(mask^block))
  if sub==0:break
  sub=(sub-1)&rest
 return tuple(result)

def objective(core,weights,part,anchor):
 k=len(part);w=[sum(weights[i]for i in range(7)if b>>i&1)for b in part]
 fold=0 if 64 not in part else 1 if anchor>=0 and part[anchor]==64 else 2
 ops=core['operations']+6+2*k-fold;M=core['M']+7
 degree=2*max(w)
 if anchor>=0:
  if k==1:ops=core['operations']+7;M-=1;degree=sum(w)
  else:degree=w[anchor]+2*max(v for i,v in enumerate(w)if i!=anchor)
 return ops,M,ops-M,degree

def encode_plan(part,anchor):return {'groups':[[i for i in range(7)if b>>i&1]for b in part],'anchor':None if anchor<0 else anchor}
def census(core,weights):
 hist=Counter();minima={};examples={};modegroups=Counter();strata={};folds=Counter()
 for part in subsets_partition(127):
  for anchor in range(-1,len(part)):
   ops,M,A,degree=objective(core,weights,part,anchor);hist[ops,M,A,degree]+=1
   kind='sos'if anchor<0 else 'anchor'
   fold='none'if 64 not in part else 'anchor_plus_one'if anchor>=0 and part[anchor]==64 else 'squared_plus_one'
   key=(len(part),kind,fold);folds[fold]+=1
   if key not in strata or degree<strata[key][0]:strata[key]=[degree,1]
   elif degree==strata[key][0]:strata[key][1]+=1
   modegroups[len(part),kind]+=1
   if ops not in minima or degree<minima[ops]:minima[ops]=degree;examples[ops]=(part,anchor)
 frontier=[];best=10**9
 for ops,d in sorted(minima.items()):
  if d<best:
   multiplicity=sum(v for (o,M,A,g),v in hist.items()if(o,g)==(ops,d))
   frontier.append({'operations':ops,'exact_degree':d,'multiplicity':multiplicity,**encode_plan(*examples[ops])});best=d
 return {'histogram':[[*k,v]for k,v in sorted(hist.items())],
         'minima_by_cost':[[o,d,sum(v for (a,M,A,g),v in hist.items()if(a,g)==(o,d))]for o,d in sorted(minima.items())],
         'frontier':frontier,'schedules':sum(hist.values()),'fold_counts':dict(sorted(folds.items())),
         'stratum_minima':[[*k,*v]for k,v in sorted(strata.items())]}

def independent_emit(parent,core,groups,anchor):
 fold=[6]in groups
 rows=[r[:]for r in core if not(fold and r[0]=='norm_strong')]
 def pay(op,a,b):
  name='tesla_'+str(len(rows));rows.append([name,op,a,b]);return name
 products=[]
 for block in groups:
  v=FACTORS[block[0]]
  for i in block[1:]:v=pay('*',v,FACTORS[i])
  products.append(v)
 if len(groups)==1 and anchor==0:out=pay('-',products[0],1)
 else:
  terms=[]
  for j,block in enumerate(groups):
   if j==anchor:continue
   r='strong_difference'if block==[6]else pay('-',products[j],1)
   terms.append(pay('*',r,r))
  out=terms[0]
  for t in terms[1:]:out=pay('+',out,t)
  if anchor is not None:
   offset=pay('+',out,1)
   if groups[anchor]==[6]:out=pay('+',pay('*','strong_difference',offset),out)
   else:out=pay('-',pay('*',products[anchor],offset),1)
 return rows,out

def alpha_source(rows,free,output):
 names={n:('port',n)for n in free};ans=[]
 at=lambda n:('literal',n)if type(n)is int else names[n]
 for i,(n,op,a,b)in enumerate(rows):
  ans.append([op,at(a),at(b)]);names[n]=('row',i)
 return ans,names[output]

def partition_polynomial(ring,units,groups,anchor):
 products=[ring.product(units[i]for i in block)for block in groups]
 if len(groups)==1 and anchor==0:return ring.add(products[0],ring.const(1),-1)
 squares=[]
 for j,p in enumerate(products):
  if j==anchor:continue
  r=ring.add(p,ring.const(1),-1);squares.append(ring.mul(r,r))
 total=ring.const(0)
 for p in squares:total=ring.add(total,p)
 return total if anchor is None else ring.add(ring.mul(products[anchor],ring.add(total,ring.const(1))),ring.const(1),-1)

def full_numeric(rows,values):
 e=values.copy()
 at=lambda x:x if type(x)is int else e[x]
 for n,op,a,b in rows:
  a,b=at(a),at(b);e[n]=a*b if op=='*'else a+b if op=='+'else a-b
 return e

def audit_winner(form,cores):
 info=form['plan'];mode=info['mode'];parent,core,ring,tops=cores[mode]
 groups=info['groups'];anchor=info['anchor'];part=tuple(sum(1<<i for i in b)for b in groups)
 require(part in subsets_partition(127))
 require(anchor is None or type(anchor)is int and 0<=anchor<len(groups))
 require(groups==encode_plan(part,-1 if anchor is None else anchor)['groups'])
 weights=EXPECTED_WEIGHTS[MODES.index(mode)];corebill=ledger(core,parent['free'],FACTORS)
 expected=objective(corebill,weights,part,-1 if anchor is None else anchor)
 require(expected==(info['operations'],info['M'],info['A'],info['exact_degree']))
 own,out=independent_emit(parent,core,groups,anchor)
 require(alpha_source(own,parent['free'],out)==alpha_source(form['source'],form['free'],form['output']),'complete literal schedule modulo register names')
 require(form['free']==parent['free']and form['witnesses']==parent['witnesses']and form['fixed_numerals']==FIXED)
 require(form['ordinary_input']=='x'and form['witness_domain']=='strictly positive integers')
 actual=ledger(form['source'],form['free'],[form['output']])
 require(all(actual[k]==form['ledger'][k]for k in actual))
 require(actual==dict(operations=expected[0],M=expected[1],A=expected[2]))
 # Interpret just the full finalizer at independent unit ports, Ns=1+D.
 abstract=Ring(FACTORS[:-1]+['strong_difference']);D=abstract.var('strong_difference')
 units=[abstract.var(n)for n in FACTORS[:-1]]+[abstract.add(D,abstract.const(1))]
 defs={n:(op,a,b)for n,op,a,b in form['source']};cache=dict(zip(FACTORS,units));cache['strong_difference']=D
 def at(n):
  if type(n)is int:return abstract.const(n)
  if n not in cache:
   op,a,b=defs[n];a,b=at(a),at(b);cache[n]=abstract.mul(a,b)if op=='*'else abstract.add(a,b,1 if op=='+'else -1)
  return cache[n]
 formal=partition_polynomial(abstract,units,groups,anchor)
 require(at(form['output'])==formal,'full finalizer coefficient identity')
 # Exact uniform leader from actual core expansions; no witness specialization.
 topgroups=[ring.product(tops[i]for i in block)for block in groups]
 ws=[sum(weights[i]for i in block)for block in groups]
 if len(groups)==1 and anchor==0:lead=topgroups[0]
 else:
  degree=max(v for j,v in enumerate(ws)if j!=anchor);lead=ring.const(0)
  for j,t in enumerate(topgroups):
   if j!=anchor and ws[j]==degree:lead=ring.add(lead,ring.mul(t,t))
  if anchor is not None:lead=ring.mul(topgroups[anchor],lead)
 require(ring.leader(lead)[0]==expected[3])
 cert=form['degree_certificate'];parsed=ring.parse([[p['monomial'],p['coefficient']]for p in cert['leading_polynomial']])
 require(parsed==lead and cert['exact_degree']==expected[3]and cert['leading_monomials']==len(lead))
 for i in range(6):
  values={n:(j*3+i)%7-3 for j,n in enumerate(form['free'])}
  if i>=4:values={n:Fraction(v,3)for n,v in values.items()}
  old=full_numeric(parent['source'],values);new=full_numeric(form['source'],values)
  vals=[old[n]for n in FACTORS];products=[]
  for block in groups:
   v=1
   for j in block:v*=vals[j]
   products.append(v)
  value=sum((v-1)**2 for j,v in enumerate(products)if j!=anchor)
  if anchor is not None:value=products[anchor]-1 if len(groups)==1 else products[anchor]*(1+value)-1
  require(new[form['output']]==value)
 return {'plan':info,'ledger':actual,'source_sha256':sha(stable(form['source'])),
  'exact_degree':expected[3],'leading_monomials':len(lead),'leading_polynomial_sha256':sha(stable(ring.serial(lead))),
  'full_finalizer_identity':True,'complete_literal_source':True,'signed_numeric':6,'rational_numeric':2}

def verify(root,author_root=None):
 blobs={}
 for path,digest in PINS.items():
  b=(root/path).read_bytes();require(sha(b)==digest,'pin '+path);blobs[path]=b
 parent=json.loads(blobs['complete_linear_auxiliary_quotient_family.json'])
 parts=subsets_partition(127);require(len(parts)==877 and sum(map(len,parts))==3263)
 cores={};results={};leaders={};counts=Counter()
 for idx,f in enumerate(parent['forms']):
  mode=f['mode'];require(mode==MODES[idx]);p=f['packet']
  require(p['factors']==FACTORS and p['fixed_numerals']==FIXED and len(p['witnesses'])==18)
  core=extract_core(p);bill=ledger(core,p['free'],FACTORS)
  require(bill=={'operations':80+(idx+1)//2,'M':41,'A':39+(idx+1)//2})
  ring=Ring(p['free']);at=ring.evaluator(core);weights=[];tops=[];terms=0
  for i,n in enumerate(FACTORS):
   full=at(n);d,top=ring.leader(full);weights.append(d);tops.append(top);terms+=len(full)
   require(top==ring.parse(f['degree']['factor_leaders'][i]),'actual full factor leader')
  require(weights==EXPECTED_WEIGHTS[idx])
  require(at('norm_strong')==ring.add(at('strong_difference'),ring.const(1)))
  consumers=[r[0]for r in core if 'norm_strong'in r[2:]];require(not consumers,'strong singleton private core port')
  cores[mode]=(p,core,ring,tops);leaders[mode]={'factor_degrees':weights,'core_ledger':bill,'full_factor_monomials':terms,
    'factor_leaders': [ring.serial(x)for x in tops]}
  results[mode]=census(bill,weights);counts['fully_expanded_factor_polynomials']+=7;counts['full_factor_monomials']+=terms
  counts['weighted_schedules']+=results[mode]['schedules']
 frontier=[];best=10**9
 for ops,d,mode in sorted((v['operations'],v['exact_degree'],m)for m,cs in results.items()for v in cs['frontier']):
  if d<best:frontier.append([ops,d,mode]);best=d
 require([(o,d)for o,d,m in frontier]==[(87,119),(88,109),(89,103),(90,98),(91,90),(92,76),(93,60),(94,56),(95,50),(96,44)])
 winner_checks=[]
 if AUTHOR:
  ab={}
  for name,pin in AUTHOR.items():
   b=((author_root or root)/name).read_bytes();require(sha(b)==pin,'author pin '+name);ab[name]=b
  author=json.loads(ab['complete_linear_auxiliary_partition_frontier.json'])
  require(author['source_sha256']==sha(ab['complete_linear_auxiliary_partition_frontier.py']))
  require(author['parent_pins']==PINS)
  require(author['grammar']['total_plans']==16560 and author['grammar']['plans_per_base']==4140)
  require(author['grammar']['set_partitions_per_base']==877 and author['grammar']['anchor_choices_per_base']==3263)
  strata={}
  for mode,record in results.items():
   for g,kind,fold,d,c in record['stratum_minima']:strata[mode,g,kind,fold]=(d,c)
  author_strata={}
  for item in author['census']['minima_by_mode_group_kind_fold']:
   q=item['plan'];key=(q['mode'],len(q['groups']),q['kind'],q['fold'])
   require(key not in author_strata);author_strata[key]=(q['exact_degree'],item['multiplicity'])
  require(strata==author_strata)
  ownfold={(mode,f):n for mode,record in results.items()for f,n in record['fold_counts'].items()}
  require(ownfold=={(x['mode'],x['fold']):x['count']for x in author['census']['fold_counts']})
  ah={(x['mode'],x['operations'],x['exact_degree']):x['count']for x in author['census']['histogram']}
  ownhist=Counter()
  for mode,record in results.items():
   for o,M,A,d,c in record['histogram']:ownhist[mode,o,d]+=c
  require(dict(ownhist)==ah,'every operation/degree histogram multiplicity')
  combined=Counter()
  for (mode,o,d),c in ownhist.items():combined[o,d]+=c
  for v in author['census']['combined_minima_by_operation']:
   p=v['plan'];o=p['operations'];d=min(d for op,d in combined if op==o)
   require(p['exact_degree']==d and v['multiplicity']==combined[o,d])
  require([(x['plan']['operations'],x['plan']['exact_degree'])for x in author['frontier']]==[(o,d)for o,d,m in frontier])
  require(len(author['forms'])==10)
  for f in author['forms']:winner_checks.append(audit_winner(f,cores))
  counts['complete_saved_winner_sources']=len(winner_checks)
  counts['saved_winner_gates']=sum(x['ledger']['operations']for x in winner_checks)
  counts['signed_winner_evaluations']=60;counts['rational_winner_evaluations']=20
  sums={'M':0,'A':0,'operations':0}
  for record in results.values():
   for o,M,A,d,c in record['histogram']:
    sums['M']+=M*c;sums['A']+=A*c;sums['operations']+=o*c
  require((sums['M'],sums['A'],sums['operations'])==(author['census']['M'],author['census']['A'],author['census']['full_live_gates']))
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'author_pins':AUTHOR,
  'counts':dict(counts),'scope':'Independent complete weighted grammar, actual factor expansions and ten saved full sources. Author all-source stream digest is authenticated, not independently rebuilt.',
  'partition_count':877,'distinguished_block_count':3263,'group_counts':{str(k):v for k,v in sorted(Counter(map(len,parts)).items())},
  'cores':leaders,'census_by_mode':results,'four_core_frontier':frontier,'saved_winner_checks':winner_checks}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path)
 group=ap.add_mutually_exclusive_group(required=True);group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
 a=ap.parse_args();d=verify(a.root,a.author_root);text=json.dumps(d,sort_keys=True,indent=2)+'\n';require(same(d,json.loads(text)))
 if a.output:a.output.write_text(text)
 else:require(same(d,json.loads(a.expect.read_text())),'receipt mismatch')
 print(json.dumps({'status':'PASS','counts':d['counts'],'frontier':d['four_core_frontier']},sort_keys=True))
if __name__=='__main__':main()
