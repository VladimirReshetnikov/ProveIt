#!/usr/bin/env python3
"""Four linear-input seven-unit cores: a bounded complete partition grammar.
Utilities adapted from the pinned earlier two-core author; no ancestor code runs.
"""
import argparse,copy,hashlib,json
from pathlib import Path
from collections import Counter
from fractions import Fraction
PINS={'../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0', 'complete75_asymmetric_factor_partitions.json': '6d9112e67d18306bb6aa8aaf8660432d7dff2398e198c3018907e1c79c70a42f', 'complete75_asymmetric_factor_partitions.md': '1e54eb9a8b5e704947ed78d69716c79ec2e6e46d187e700960bf1b1b700eebf2', 'complete75_asymmetric_factor_partitions.py': 'b772fc579454b13ce30e5f9feaad25206d35b04af3cb4dffb1d76d1246d4c515', 'complete75_asymmetric_linear_gap_tradeoffs.json': 'dcd2c462e8405bc4535682a624832e8a8ad044a86504fd0b46df6700ab5c0f26', 'complete75_asymmetric_linear_gap_tradeoffs.md': '93aac323a64bf6c7e8946faeddf90de5606d8c133d3bd611a0806269e8f92638', 'complete75_asymmetric_linear_gap_tradeoffs.py': 'a08626905d8a790ec1458bc8e7302b9f28e251b84818695d2fa3c640a8c9dcf2', 'complete75_asymmetric_scale_tradeoffs.json': '47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_asymmetric_scale_tradeoffs.py': 'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660', 'complete75_auxiliary_gap_degree_tradeoffs.json': '741592f41a1ef6df2797a23e1380e3c208b093379b0379a4aedf36700f9592d9', 'complete75_auxiliary_gap_degree_tradeoffs.md': '315792b00530a4517e7f79f3c423f860268145803eb9bc364a235782aad69755', 'complete75_auxiliary_gap_degree_tradeoffs.py': 'f359f6d07c8c8e18d1f41b53e198f1bba70f5d43dcad049e1e12600260521312', 'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39', 'complete75_coupled_index_linear88.py': 'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed', 'complete75_linear_input_degree_tradeoffs.json': '15f62dee3287c5a3d976f43add43e74e755f8e7e2b59787b837c87c2cdf35d84', 'complete75_linear_input_degree_tradeoffs.md': '8b3cb44cbd2b979175ebfe4731556384469adfa93890ca7b01f70fa192a9682b', 'complete75_linear_input_degree_tradeoffs.py': 'cd06f404f5a9cbb0f5b6116ba13498321bfeba845f827541833ef4a1f3c882bc', 'complete75_linear_input_modulus89.json': 'c6758bc90adeb331ddfb8e9512d8974035e46701cd0a2c4ebd378b5f7c59c9fd', 'complete75_linear_input_modulus89.md': '855a1e038dac816043c040decd35d33818e0da25e1e9e1713a9a454bcc531444', 'complete75_linear_input_modulus89.py': 'dfcee79fb8564a29bba3a243da4fbce848709d0de5117426222b39b869ef4efb', 'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b', 'complete75_normalized_strong87.py': '7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749', 'complete75_reversed_auxiliary89.md': '4eddb6627b6261b1d8f8617006e443908574c0b7b2d3fdda15ff85dc86bd9700', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e', 'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b', 'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f', 'complete86_first_root_partitions.json': '7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5', 'complete86_first_root_partitions.md': '7325cf4fcf88bd5c20bd3d556eef7c8a313f3aee914e637483dc065d2417c2e0', 'complete86_first_root_partitions.py': 'b139097ed009580cfe8fc7707e373ec9ecafdecb886bd2cf037d615a06d35988', 'complete86_ordinary_auxiliary_projection.json': 'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6', 'complete86_ordinary_auxiliary_projection.md': 'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570', 'complete86_ordinary_auxiliary_projection.py': '130c8a09570866f3b510f4092aef3ab7fd61154f6c8776fcdba870d80a59019d', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45', 'complete_auxiliary_unit_partition_frontier.json': 'e09f0bb97afa4cfdfdbc354fbc0c886bfdb608d6731a55b8db8314a3c7a89097', 'complete_auxiliary_unit_partition_frontier.md': '690de29dfb86f7c19709d2c88d54379267ca2e73b64cbc683b181fa07324e616', 'complete_auxiliary_unit_partition_frontier.py': '0e234ba9f4cb1889417ba281b1fe217906ac84c9c7c199395b8dfa36b2914f17', 'review_complete85_auxiliary_bezout_math.json': '9cdbf027fe1da74975043f4c5ba022b04e0e73eb92166cf2a1ed2ec1cc258d49', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', 'review_complete85_auxiliary_bezout_math.py': 'ea1c7d39b2afc6c1a004facac777b6ad97af89c5c92309e489439928abcbdd65', 'transport_shear_frontier_probe.json': '4e58078d955a9cc7d5642dea24e8f1ac76ac71da2f8b82b568bb27794d25d865', 'transport_shear_partition_census.json': '93becb442a3809f855053f414e8478e92b2b5eed0ff84c1cb22996b9a0ac1ef0', 'transport_shear_partition_census.md': '27f38b0757d220e605565c6d63ff3470a73292a9cb632a8c529e8d1b89804469', 'transport_shear_partition_census.py': 'd58f6fd00bc658a566a3ae2f1a3c8b9c7fd457b272291b595132c75a7cbf1d1c', 'complete_linear_auxiliary_quotient_family.py': '07d9bd66528a213929475ab560a0265fa872c88599d9b9700fdc5d4910a31153', 'complete_linear_auxiliary_quotient_family.json': 'b2cb2723c3a335df84b8f3472371912beb28cc52b0f07d0b68d4d0d0fcb6a2b5', 'complete_linear_auxiliary_quotient_family.md': '7e85f2e3a236872da22be9d85222289475ebfb825b733e3e881c5a2b220eed66', 'review_linear_auxiliary_quotient_family.py': '54f2b7e9bd1abfb6242e29cb46ca98ccaee1f752dff344a0a38e6d83b1a847ed', 'review_linear_auxiliary_quotient_family.json': 'c19401eac5275ade18af2fbf6ea3c9cacdc40cd36f93dd97b63fc57b0ab77acc', 'review_linear_auxiliary_quotient_family.md': '09cf75696613675829764934cf9c3e65fe8bc5494f5980957383bc03ef60dafd'}
FACTORS=['norm_first', 'norm_main', 'norm_input', 'norm_aux', 'norm_index', 'norm_transport', 'norm_strong']
FIXED=['Bm1', 'Kconstant', 'twice_cell_bits', 'inner_bits', 'MC', 'MF']
def require(v,m):
 if not v: raise ValueError(m)
def sha(b): return hashlib.sha256(b).hexdigest()
def stable(v): return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def same(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k])for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y)for x,y in zip(a,b))
 return a==b
def atom(v):return {((v,1),):1}
def const(v):return {():v} if v else {}
def add(a,b,s=1):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+s*c
 return {m:c for m,c in z.items()if c}
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   e=dict(m)
   for v,k in n:e[v]=e.get(v,0)+k
   q=tuple(sorted(e.items()));z[q]=z.get(q,0)+c*d
 return {m:c for m,c in z.items()if c}
def power(a,n):
 z=const(1)
 for _ in range(n):z=mul(z,a)
 return z
def sum_polys(xs):
 z={}
 for x in xs:z=add(z,x)
 return z
def plus(a,b,s=1):
 d=max(a[0],b[0]);return d,add(a[1]if a[0]==d else{},b[1]if b[0]==d else{},s)
def times(a,b):return a[0]+b[0],mul(a[1],b[1])
def ledger(p):
 require(len(p['free'])==len(set(p['free'])),'unique supplied leaves')
 degrees={v:0 if v in FIXED else 1 for v in p['free']};defs={};counts=Counter()
 for n,o,a,b in p['source']:
  require(n not in degrees and o in ('+','-','*'),'fresh supported row')
  require(all(type(v)is int or type(v)is str and v in degrees for v in (a,b)),'strict closed source')
  da,db=(degrees.get(v,0)for v in (a,b));degrees[n]=da+db if o=='*'else max(da,db)
  defs[n]=(a,b);counts['M'if o=='*'else'A']+=1
 seen=set();leaves=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in defs:leaves.add(n)
  elif n not in seen:seen.add(n);todo.extend(defs[n])
 require(seen==set(defs) and leaves==set(p['free']),'all gates and declared coordinates live')
 return dict(operations=len(defs),M=counts['M'],A=counts['A'],naive_degree_upper=degrees[p['output']])
def evaluate(p,v):
 e=dict(v)
 for n,o,a,b in p['source']:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b
  e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def authenticate(root):
 blobs={}
 for name,pin in PINS.items():
  b=(root/name).read_bytes();require(sha(b)==pin,'fresh pin '+name);blobs[name]=b
 return blobs

def closure(source,roots):
 d={r[0]:r for r in source};seen=set();stack=list(roots)
 while stack:
  n=stack.pop()
  if type(n)is str and n in d and n not in seen:seen.add(n);stack.extend(d[n][2:])
 return [r[:]for r in source if r[0]in seen]

def load_parents(blobs):
 receipt=json.loads(blobs['complete_linear_auxiliary_quotient_family.json'])
 require(receipt['source_sha256']==sha(blobs['complete_linear_auxiliary_quotient_family.py']),'parent source binding')
 for n,h in receipt['parent_pins'].items():require(PINS.get(n)==h,'inherited parent pin '+n)
 expected=[('root_ordinate',False,False,87,[22,18,20,28,7,2,22]),('root_gap',False,True,88,[22,18,20,22,7,2,22]),('gap_ordinate',True,False,88,[12,18,20,28,7,2,22]),('gap_gap',True,True,89,[12,18,20,22,7,2,22])]
 require(len(receipt['forms'])==4,'four exact source forms')
 out={}
 for item,(mode,fg,ag,count,weights) in zip(receipt['forms'],expected):
  p=item['packet']
  require(item['mode']==mode and p['mode']==mode and p['first_gap']is fg and p['auxiliary_gap']is ag,'exact source coordinates')
  require(p['normalized_strong']is False and p['witness_domain']=='strictly positive integers' and p['ordinary_input']=='x' and p['fixed_numerals']==FIXED and len(p['witnesses'])==18,'positive ordinary parent interface')
  require(p['free']==p['witnesses']+['x']+FIXED and p['factors']==FACTORS,'all supplied ports and factors')
  require(ledger(p)['operations']==count and item['degree']['factor_degrees']==weights,'full actual parent count/weights')
  core=closure(p['source'],FACTORS);defs={r[0]:r[1:]for r in core}
  require(defs['norm_strong']==['+','strong_difference',1],'literal strong plus-one definition')
  require([r[0]for r in core if 'norm_strong'in r[2:]]==[],'private strong factor producer')
  cm=sum(r[1]=='*'for r in core);ca=len(core)-cm
  require(cm==41 and ca==39+fg+ag,'literal four core ledgers')
  require(defs['index_product']==['*','delta','a_plus_one'] and defs['a_plus_one']==['+','R12',1],'linear input modulus retained')
  out[mode]=dict(parent=p,core=core,weights=weights,core_M=cm,core_A=ca,first_gap=fg,auxiliary_gap=ag,parent_degree=item['degree'])
 return out

def partitions(n):
 def rec(j,blocks):
  if j==n:
   yield tuple(tuple(b)for b in blocks);return
  for b in blocks:
   b.append(j);yield from rec(j+1,blocks);b.pop()
  blocks.append([j]);yield from rec(j+1,blocks);blocks.pop()
 yield from rec(0,[])

def plan_info(base,mode,groups,anchor):
 w=[sum(base['weights'][i]for i in b)for b in groups];g=len(groups)
 fold='none'
 if g>1 and (6,)in groups:
  fold='anchor_plus_one'if anchor==groups.index((6,))else 'squared_plus_one'
 if anchor is not None and g==1:
  m=base['core_M']+6;a=base['core_A']+1;degree=sum(w)
 else:
  m=base['core_M']+7;a=base['core_A']+2*g-1
  a-=2 if fold=='squared_plus_one'else 1 if fold=='anchor_plus_one'else 0
  degree=2*max(w)if anchor is None else w[anchor]+2*max(x for j,x in enumerate(w)if j!=anchor)
 return dict(mode=mode,groups=[list(b)for b in groups],anchor=anchor,kind='sos'if anchor is None else'anchor',group_weights=w,fold=fold,M=m,A=a,operations=m+a,exact_degree=degree)

def emit(base,info):
 src=[r[:]for r in base['core']];groups=info['groups'];anchor=info['anchor'];g=len(groups)
 def row(name,op,a,b):src.append([name,op,a,b]);return name
 products=[]
 for j,block in enumerate(groups):
  acc=FACTORS[block[0]]
  for k,i in enumerate(block[1:]):acc=row('group_%d_product_%d'%(j,k),'*',acc,FACTORS[i])
  products.append(acc)
 if anchor is not None and g==1:output=row('partition_output','-',products[0],1)
 else:
  squares=[]
  for j,block in enumerate(groups):
   if j==anchor:continue
   residual='strong_difference'if info['fold']=='squared_plus_one'and block==[6]else row('group_%d_residual'%j,'-',products[j],1)
   squares.append(row('group_%d_square'%j,'*',residual,residual))
  total=squares[0]
  for j,sq in enumerate(squares[1:]):total=row('sos_sum_%d'%j,'+',total,sq)
  if anchor is None:output=total
  else:
   shifted=row('sos_plus_one','+',total,1)
   if info['fold']=='anchor_plus_one':
    scaled=row('anchor_scaled','*','strong_difference',shifted)
    output=row('partition_output','+',scaled,total)
   else:
    scaled=row('anchor_scaled','*',products[anchor],shifted)
    output=row('partition_output','-',scaled,1)
 src=closure(src,[output]);p=base['parent']
 return dict(source=src,output=output,free=p['free'][:],witnesses=p['witnesses'][:],fixed_numerals=FIXED[:],ordinary_input='x',first_gap=base['first_gap'],auxiliary_gap=base['auxiliary_gap'],normalized_strong=False,witness_domain='strictly positive integers',plan=copy.deepcopy(info),positive_witnesses=18,full_positive_zero_set_unchanged=True,full_polynomial_identity_to_parent=(len(groups)==1 and anchor==0),scope='Complete source for one declared partition/finalizer. Positive-zero equivalence to its own parent; polynomial identity to that parent only for the sole-group anchor. No all-integer zero equivalence theorem.')

def finalizer_proof(base,p):
 info=p['plan'];groups=info['groups'];a=info['anchor'];d={r[0]:r[1:]for r in p['source']}
 bd={r[0]:r[1:]for r in base['core']}
 present=set(bd)&set(d);require(all(bd[n]==d[n]for n in present),'unchanged literal core definitions')
 absent=set(bd)-set(d)
 require(absent==({'norm_strong'}if info['fold']!='none'else set()),'only private +1 pruned')
 require(len(p['witnesses'])==18 and p['free']==base['parent']['free'],'entire supplied interface retained')
 # A formal strong_difference cut proves the two source folds over Z.
 atoms={v:atom(v)for v in FACTORS}
 atoms['norm_strong']=add(atom('strong_difference'),const(1))
 memo=dict(atoms);memo['strong_difference']=atom('strong_difference')
 def get(v):
  if type(v)is int:return const(v)
  if v not in memo:
   op,x,y=d[v];x,y=get(x),get(y);memo[v]=mul(x,y)if op=='*'else add(x,y,1 if op=='+'else-1)
  return memo[v]
 products=[]
 for block in groups:
  z=const(1)
  for i in block:z=mul(z,atoms[FACTORS[i]])
  products.append(z)
 if a is not None and len(groups)==1:expected=add(products[0],const(1),-1)
 else:
  sos=sum_polys([power(add(z,const(1),-1),2)for j,z in enumerate(products)if j!=a])
  expected=sos if a is None else add(mul(products[a],add(const(1),sos)),const(1),-1)
 require(get(p['output'])==expected,'full finalizer coefficient identity under all supplied factor values')
 return sha(stable(sorted((list(m),c)for m,c in expected.items())))

def parent_product_proof(base):
 p=base['parent'];defs={r[0]:r[1:]for r in p['source']};memo={n:atom(n)for n in FACTORS}
 def get(n):
  if type(n)is int:return const(n)
  if n not in memo:
   op,a,b=defs[n];a,b=get(a),get(b);memo[n]=mul(a,b)if op=='*'else add(a,b,1 if op=='+'else-1)
  return memo[n]
 expected=const(1)
 for name in FACTORS:expected=mul(expected,atom(name))
 expected=add(expected,const(1),-1)
 require(get(p['output'])==expected,'actual complete parent product finalizer')
 return sha(stable(sorted((list(m),c)for m,c in expected.items())))

def factor_leaders(base,mode):
 src=base['core'];d={r[0]:r[1:]for r in src}
 guards={'norm_main':['-','L15','Ac2'],'L15':['*','R14','R14'],'R14':['+','D1','gam'],'D1':['+','wn2','cam2'],'cam2':['*','R10a','R12'],
 'norm_input':['-','mu2','scaled_kappa2'],'mu2':['*','exponent_rhs','exponent_rhs'],'exponent_rhs':['+','exponent_partial','modulus_multiple'],'exponent_partial':['+','W','difference_multiple'],'difference_multiple':['*','index_rhs','R12'],
 'Ac2':['*','A','c2'],'c2':['*','R10a','R10a'],'scaled_kappa2':['*','A','kappa2'],'kappa2':['*','index_rhs','index_rhs'],'A':['+','a_square','a4m5'],'a_square':['*','R12','R12']}
 require(all(d[n]==r for n,r in guards.items()),'literal guarded degree-cancellation cones')
 if base['auxiliary_gap']:
  require(d['y_aux']==['+','aux_u_rhs','aux_gap'] and d['H2']==['*','aux_u_rhs','aux_u_rhs'] and d['aux_y2']==['*','y_aux','y_aux'] and d['aux_square_gap']==['-','H2','aux_y2'],'literal auxiliary-gap cancellation cone')
 e={n:(0 if n in FIXED else 1,atom(n))for n in base['parent']['free']}
 for n,o,a,b in src:
  av=e[a]if type(a)is str else(0,const(a));bv=e[b]if type(b)is str else(0,const(b));v=times(av,bv)if o=='*'else plus(av,bv,1 if o=='+'else-1)
  if n=='aux_square_gap' and base['auxiliary_gap']:
   v=times((0,const(-1)),times(e['aux_gap'],plus(times((0,const(2)),e['aux_u_rhs']),e['aux_gap'])))
  if n in ('norm_main','norm_input'):
   off='wn2'if n=='norm_main'else'W';shift='gam'if n=='norm_main'else'modulus_multiple';ordinate='R10a'if n=='norm_main'else'index_rhs'
   t=plus(e[off],e[shift]);v=plus(times(t,plus(t,times((0,const(2)),times(e['R12'],e[ordinate])))),times(e['a4m5'],times(e[ordinate],e[ordinate])),-1)
  require(bool(v[1]),'nonzero symbolic core leader '+n);e[n]=v
 Q=mul(atom('Bm1'),atom('Jrep'));k=add(atom('eta'),atom('zeta'));gamma=add(atom('rho'),atom('sigma'))
 C=Q
 for n in ('F','Z','alpha'):C=add(C,atom(n),-1)
 C=add(C,mul(atom('twice_cell_bits'),atom('x')),-1)
 tr=add(mul(atom('w'),C),mul(atom('transport_quotient'),Q),-1)
 def mon(c,*factors):
  z=const(c)
  for a,n in factors:z=mul(z,power(a,n))
  return z
 w,s,i,T,f,h,delta=[atom(n)for n in ('w','s','i','auxiliary_quotient','f','h','delta')]
 first=mon(1,(w,1),(k,1),(s,2),(Q,7),(add(mul(const(2),atom('tau_gap')),k,-1),1))if base['first_gap']else mon(-1,(w,2),(k,2),(s,4),(Q,14))
 inp=mon(4,(delta,1),(add(mul(const(2),atom('rho')),delta,-1),1),(w,3),(s,3),(Q,12))
 aux=mon(-2,(w,2),(k,1),(s,3),(Q,11),(T,1),(f,3),(atom('aux_gap'),1))if base['auxiliary_gap']else mon(1,(w,2),(k,2),(s,4),(Q,14),(T,2),(f,4))
 expected=[first,mon(8,(gamma,1),(w,2),(k,1),(s,3),(Q,11)),inp,aux,mon(-1,(h,1),(w,1),(s,1),(Q,4)),tr,mon(1,(i,2),(k,4),(s,4),(Q,12))]
 require([e[n][0]for n in FACTORS]==base['weights'],'all seven actual exact degrees')
 require([e[n][1]for n in FACTORS]==expected,'all seven entire leading homogeneous forms')
 saved=base['parent_degree']['factor_leaders']
 parsed=[{tuple((n,e)for n,e in m):c for m,c in polynomial}for polynomial in saved]
 require(expected==parsed,'agreement with all pinned parent coefficient leaders')
 # All expected factors are products of nonzero powers/linear forms. The
 # transport form's unique transport_quotient*Jrep coefficient is -Bm1.
 return expected

def finalist_degree(base,info,leaders):
 group=[]
 for block in info['groups']:
  z=const(1)
  for i in block:z=mul(z,leaders[i])
  group.append(z)
 a=info['anchor'];w=info['group_weights']
 if a is not None and len(group)==1:lead=group[0]
 else:
  largest=max(x for j,x in enumerate(w)if j!=a)
  lead=sum_polys([power(z,2)for j,z in enumerate(group)if j!=a and w[j]==largest])
  if a is not None:lead=mul(group[a],lead)
 require(bool(lead),'nonzero entire finalist leader')
 # Verify total degree after assigning degree zero only to fixed numeral ports.
 deg={sum(e for n,e in mon if n not in FIXED)for mon in lead}
 require(deg=={info['exact_degree']},'actual entire leader homogeneous degree')
 return dict(exact_degree=info['exact_degree'],leading_monomials=len(lead),leading_polynomial=[{'monomial':[[n,e]for n,e in m],'coefficient':c}for m,c in sorted(lead.items())],uniform_noncancellation='Nonzero factor products and sums of real squares for every valid fixed numeral recipe with Bm1>0; no zero-set substitution.')

def numeric_finalists(base,p):
 count=0
 for case in range(12):
  v={n:((case+3)*(j+5)%9)-4 for j,n in enumerate(p['free'])}
  if case>=8:v={n:Fraction(x,3)for n,x in v.items()}
  e=evaluate(base['parent'],v);z=evaluate(p,v);pr=[]
  for b in p['plan']['groups']:
   prod=1
   for i in b:prod*=e[FACTORS[i]]
   pr.append(prod)
  a=p['plan']['anchor']
  expected=sum((x-1)**2 for j,x in enumerate(pr)if j!=a)
  if a is not None:expected=pr[a]-1 if len(pr)==1 else pr[a]*(1+expected)-1
  require(z[p['output']]==expected,'full supplied-tuple grouped finalizer evaluation');count+=1
 return count

def cancellation_identity():
 x,a,c,g,H=[atom(n)for n in ('X','a','c','gamma','H')]
 left=add(power(sum_polys([x,mul(a,c),g]),2),mul(add(power(a,2),H),power(c,2)),-1);t=add(x,g)
 right=add(mul(t,add(t,mul(const(2),mul(a,c)))),mul(H,power(c,2)),-1)
 require(left==right,'exact all-value norm cancellation')
 v,e=atom('V'),atom('aux_gap')
 require(add(power(v,2),power(add(v,e),2),-1)==mul(const(-1),mul(e,add(mul(const(2),v),e))),'exact all-value auxiliary-gap cancellation')


def verify(root):
 blobs=authenticate(root);bases=load_parents(blobs);cancellation_identity()
 parent_finalizers={m:parent_product_proof(b)for m,b in bases.items()}
 leaders={m:factor_leaders(b,m)for m,b in bases.items()};ps=list(partitions(7));require(len(ps)==877 and sum(map(len,ps))==3263,'complete Bell partition/anchor counts')
 hist=Counter();folds=Counter();minimum={};minimum_by_cost={};stream=hashlib.sha256();total_gates=total_m=total_a=0;plans=0
 for mode,base in bases.items():
  for groups in ps:
   for anchor in [None]+list(range(len(groups))):
    info=plan_info(base,mode,groups,anchor);p=emit(base,info);ld=ledger(p)
    require((ld['operations'],ld['M'],ld['A'])==(info['operations'],info['M'],info['A']),'literal full live census ledger')
    proof=finalizer_proof(base,p);hist[(mode,info['operations'],info['exact_degree'])]+=1;folds[(mode,info['fold'])]+=1
    stream.update(stable(dict(plan=info,source=p['source'],output=p['output'],proof=proof)));stream.update(b'\n')
    total_gates+=ld['operations'];total_m+=ld['M'];total_a+=ld['A'];plans+=1
    key=(mode,len(groups),info['kind'],info['fold'])
    if key not in minimum or info['exact_degree']<minimum[key]['plan']['exact_degree']:minimum[key]=dict(plan=info,multiplicity=1)
    elif info['exact_degree']==minimum[key]['plan']['exact_degree']:minimum[key]['multiplicity']+=1
    op=info['operations']
    if op not in minimum_by_cost or info['exact_degree']<minimum_by_cost[op]['plan']['exact_degree']:minimum_by_cost[op]=dict(plan=info,multiplicity=1)
    elif info['exact_degree']==minimum_by_cost[op]['plan']['exact_degree']:minimum_by_cost[op]['multiplicity']+=1
 require(plans==16560,'entire declared finite grammar')
 frontier=[];best_degree=None
 for op,r in sorted(minimum_by_cost.items()):
  d=r['plan']['exact_degree']
  if best_degree is None or d<best_degree:frontier.append(r);best_degree=d
 require([(r['plan']['operations'],r['plan']['exact_degree'])for r in frontier]==[(87,119),(88,109),(89,103),(90,98),(91,90),(92,76),(93,60),(94,56),(95,50),(96,44)],'finite family frontier')
 saved=[]
 for r in frontier:
  info=r['plan'];base=bases[info['mode']];p=emit(base,info)
  p['ledger']=ledger(p);p['finalizer_identity_sha256']=finalizer_proof(base,p);p['degree_certificate']=finalist_degree(base,info,leaders[info['mode']]);p['numeric_cases']=numeric_finalists(base,p)
  saved.append(p)
 # Only this explicit historical18-witness union is used for the comparison.
 older=json.loads(blobs['complete_auxiliary_unit_partition_frontier.json'])
 oldpoints=[(r['plan']['operations'],r['plan']['exact_degree'])for r in older['frontier']]
 inherited=oldpoints+[(ledger(b['parent'])['operations'],b['parent']['exact_degree'])for b in bases.values()]
 def pareto(points):
  out=[];best=None
  for op,degr in sorted(set(points)):
   if best is None or degr<best:out.append([op,degr]);best=degr
  return out
 before=pareto(inherited);after=pareto(inherited+[(r['plan']['operations'],r['plan']['exact_degree'])for r in frontier])
 added=[r for r in after if r not in before]
 require(added==[[90,98],[92,76],[93,60],[94,56],[95,50],[96,44]],'new points in explicit eighteen-witness union')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=copy.deepcopy(PINS),grammar=dict(factors=FACTORS,set_partitions_per_base=877,anchor_choices_per_base=3263,plans_per_base=4140,total_plans=plans,fixed_products='Increasing factor indices, left-associated; no CSE/reassociation/coordinate search.',singleton_folds=['(Ns-1)^2=strong_difference^2','Ns*(1+S)-1=strong_difference*(1+S)+S'],all_plans_generated_and_recounted=True,saved_complete_sources=len(saved)),cores={m:dict(M=b['core_M'],A=b['core_A'],operations=len(b['core']),factor_degrees=b['weights'],source_sha256=sha(stable(b['core'])),parent_finalizer_identity_sha256=parent_finalizers[m])for m,b in bases.items()},census=dict(full_live_gates=total_gates,M=total_m,A=total_a,source_and_identity_stream_sha256=stream.hexdigest(),fold_counts=[dict(mode=m,fold=f,count=n)for(m,f),n in sorted(folds.items())],histogram=[dict(mode=m,operations=o,exact_degree=d,count=n)for(m,o,d),n in sorted(hist.items())],minima_by_mode_group_kind_fold=[v for k,v in sorted(minimum.items())],combined_minima_by_operation=[v for k,v in sorted(minimum_by_cost.items())]),frontier=frontier,forms=saved,historical_eighteen_witness_comparison=dict(before=before,after=after,new_points=added,scope='Only the pinned earlier auxiliary-unit partition frontier and four immediate linear parents; separate nineteen-witness families and arbitrary representations are outside this comparison.'),scope='Exact finite four-core grammar, eighteen positive witnesses and complete fixed-program hypotheses. All16560 plans are generated, proved at factor ports and live-recounted; only ten frontier full arrays are saved. Positive-zero equivalence uses the parent all-seven=1 theorem. No lower operation record, unrestricted Pareto claim, archived/ancestor Python execution, or materialized full Pell zero.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();r=verify(args.root)
 if args.expect:require(same(r,json.loads(args.expect.read_text())),'type-exact saved receipt')
 if args.output:args.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status='PASS',plans=r['grammar']['total_plans'],gates=r['census']['full_live_gates'],frontier=[(x['plan']['operations'],x['plan']['exact_degree'])for x in r['frontier']])))
if __name__=='__main__':main()
