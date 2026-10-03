#!/usr/bin/env python3
"""Four ordinary-strong linear-input quotient circuits; pinned-data research CLI.
No predecessor Python is imported or executed. Elementary sparse-polynomial
utilities are adapted from the ordinary86 author helper (not an independent audit).
"""
import argparse, copy, hashlib, json, random
from collections import Counter
from fractions import Fraction
from pathlib import Path
PINS={'../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0', 'complete75_asymmetric_factor_partitions.json': '6d9112e67d18306bb6aa8aaf8660432d7dff2398e198c3018907e1c79c70a42f', 'complete75_asymmetric_factor_partitions.md': '1e54eb9a8b5e704947ed78d69716c79ec2e6e46d187e700960bf1b1b700eebf2', 'complete75_asymmetric_factor_partitions.py': 'b772fc579454b13ce30e5f9feaad25206d35b04af3cb4dffb1d76d1246d4c515', 'complete75_asymmetric_linear_gap_tradeoffs.json': 'dcd2c462e8405bc4535682a624832e8a8ad044a86504fd0b46df6700ab5c0f26', 'complete75_asymmetric_linear_gap_tradeoffs.md': '93aac323a64bf6c7e8946faeddf90de5606d8c133d3bd611a0806269e8f92638', 'complete75_asymmetric_linear_gap_tradeoffs.py': 'a08626905d8a790ec1458bc8e7302b9f28e251b84818695d2fa3c640a8c9dcf2', 'complete75_asymmetric_scale_tradeoffs.json': '47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_asymmetric_scale_tradeoffs.py': 'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660', 'complete75_auxiliary_gap_degree_tradeoffs.json': '741592f41a1ef6df2797a23e1380e3c208b093379b0379a4aedf36700f9592d9', 'complete75_auxiliary_gap_degree_tradeoffs.md': '315792b00530a4517e7f79f3c423f860268145803eb9bc364a235782aad69755', 'complete75_auxiliary_gap_degree_tradeoffs.py': 'f359f6d07c8c8e18d1f41b53e198f1bba70f5d43dcad049e1e12600260521312', 'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39', 'complete75_coupled_index_linear88.py': 'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed', 'complete75_linear_input_degree_tradeoffs.json': '15f62dee3287c5a3d976f43add43e74e755f8e7e2b59787b837c87c2cdf35d84', 'complete75_linear_input_degree_tradeoffs.md': '8b3cb44cbd2b979175ebfe4731556384469adfa93890ca7b01f70fa192a9682b', 'complete75_linear_input_degree_tradeoffs.py': 'cd06f404f5a9cbb0f5b6116ba13498321bfeba845f827541833ef4a1f3c882bc', 'complete75_linear_input_modulus89.json': 'c6758bc90adeb331ddfb8e9512d8974035e46701cd0a2c4ebd378b5f7c59c9fd', 'complete75_linear_input_modulus89.md': '855a1e038dac816043c040decd35d33818e0da25e1e9e1713a9a454bcc531444', 'complete75_linear_input_modulus89.py': 'dfcee79fb8564a29bba3a243da4fbce848709d0de5117426222b39b869ef4efb', 'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b', 'complete75_normalized_strong87.py': '7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749', 'complete75_reversed_auxiliary89.md': '4eddb6627b6261b1d8f8617006e443908574c0b7b2d3fdda15ff85dc86bd9700', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e', 'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b', 'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f', 'complete86_first_root_partitions.json': '7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5', 'complete86_first_root_partitions.md': '7325cf4fcf88bd5c20bd3d556eef7c8a313f3aee914e637483dc065d2417c2e0', 'complete86_first_root_partitions.py': 'b139097ed009580cfe8fc7707e373ec9ecafdecb886bd2cf037d615a06d35988', 'complete86_ordinary_auxiliary_projection.json': 'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6', 'complete86_ordinary_auxiliary_projection.md': 'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570', 'complete86_ordinary_auxiliary_projection.py': '130c8a09570866f3b510f4092aef3ab7fd61154f6c8776fcdba870d80a59019d', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45', 'complete_auxiliary_unit_partition_frontier.json': 'e09f0bb97afa4cfdfdbc354fbc0c886bfdb608d6731a55b8db8314a3c7a89097', 'complete_auxiliary_unit_partition_frontier.md': '690de29dfb86f7c19709d2c88d54379267ca2e73b64cbc683b181fa07324e616', 'complete_auxiliary_unit_partition_frontier.py': '0e234ba9f4cb1889417ba281b1fe217906ac84c9c7c199395b8dfa36b2914f17', 'review_complete85_auxiliary_bezout_math.json': '9cdbf027fe1da74975043f4c5ba022b04e0e73eb92166cf2a1ed2ec1cc258d49', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', 'review_complete85_auxiliary_bezout_math.py': 'ea1c7d39b2afc6c1a004facac777b6ad97af89c5c92309e489439928abcbdd65', 'transport_shear_frontier_probe.json': '4e58078d955a9cc7d5642dea24e8f1ac76ac71da2f8b82b568bb27794d25d865', 'transport_shear_partition_census.json': '93becb442a3809f855053f414e8478e92b2b5eed0ff84c1cb22996b9a0ac1ef0', 'transport_shear_partition_census.md': '27f38b0757d220e605565c6d63ff3470a73292a9cb632a8c529e8d1b89804469', 'transport_shear_partition_census.py': 'd58f6fd00bc658a566a3ae2f1a3c8b9c7fd457b272291b595132c75a7cbf1d1c'}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
MODES=[('root_ordinate',3,False,False,87,119),('root_gap',8,False,True,88,113),('gap_ordinate',16,True,False,88,109),('gap_gap',21,True,True,89,103)]
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
def serialized(p):return [[[[v,e]for v,e in m],c]for m,c in sorted(p.items())]
def authenticate(root):
 blobs={}
 for name,pin in PINS.items():
  data=(root/name).read_bytes();require(sha(data)==pin,'fresh pin '+name);blobs[name]=data
 for stem in ['transport_shear_partition_census','complete86_ordinary_auxiliary_projection','complete_auxiliary_unit_partition_frontier']:
  data=json.loads(blobs[stem+'.json']);require(data['source_sha256']==PINS[stem+'.py'],'receipt source pin '+stem)
 return blobs

def ledger(p):
 require(len(p['free'])==len(set(p['free'])),'unique supplied leaves')
 degrees={v:0 if v in FIXED else 1 for v in p['free']};defs={};counts=Counter()
 for row in p['source']:
  require(type(row)is list and len(row)==4,'literal four-entry row')
  n,o,a,b=row;require(type(n)is str and n not in degrees and o in ('+','-','*'),'fresh supported row')
  require(all(type(v)is int or type(v)is str and v in degrees for v in (a,b)),'strict closed source')
  da,db=(degrees.get(v,0)for v in (a,b));degrees[n]=da+db if o=='*'else max(da,db)
  defs[n]=(a,b);counts['M'if o=='*'else'A']+=1
 seen=set();leaves=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in defs:leaves.add(n)
  elif n not in seen:seen.add(n);todo.extend(defs[n])
 require(seen==set(defs) and leaves==set(p['free']),'every gate and supplied coordinate live')
 return dict(operations=len(defs),M=counts['M'],A=counts['A'],naive_degree_upper=degrees[p['output']],all_gates_live=True,positive_witnesses=len(p['witnesses']))

def select_parent(data,index,fg,ag):
 f=data['forms'][index]
 require(f['coordinate_family']==('gap_root'if fg else'first_root'),'exact first-coordinate family')
 require(f['kind']==('auxgap_coupled_units'if ag else'linear_coupled_units'),'exact linear coupled family')
 require(f['factors']==FACTORS+['norm_linear'] and f['ordinary_comparisons']==[],'eight exact factors and no extra equations')
 winners=[w for w in f['winners']if w['partition']==[list(range(8))]and w['anchor']==0]
 require(len(winners)==1,'unique actual saved one-block anchor')
 w=winners[0];p=copy.deepcopy(dict(source=w['source'],output=w['output'],witnesses=f['witnesses'],ordinary_input=f['ordinary_input'],fixed_numerals=f['fixed_numerals'],factors=f['factors']))
 p['free']=p['witnesses']+['x']+FIXED;require(p['fixed_numerals']==FIXED and p['ordinary_input']=='x','complete parent interface')
 require(p['output']=='shear_output' and len(p['witnesses'])==19,'parent output and witnesses')
 l=ledger(p);require(l['operations']==88+int(fg)+int(ag) and l['M']==47,'saved parent paid ledger')
 require(w['ledger']['operations']==l['operations']and w['ledger']['M']==l['M']and w['ledger']['A']==l['A'],'saved ledger matches actual rows')
 require(w['exact_degree']==122-10*int(fg)-4*int(ag),'saved parent degree')
 p['ledger']=l;p['exact_degree']=w['exact_degree']
 return p

def build(parent,mode,fg,ag,cost,deg):
 remove={'of','jc','linear_difference','norm_linear','shear_group_0_6','aux_u_rhs','shear_output'}
 rows=[r[:]for r in parent['source']if r[0]not in remove]
 rows += [['auxiliary_Tf','*','auxiliary_quotient','f'],['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],['auxiliary_R_f2','*','r_lhs','L16'],['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],['shear_output','-','shear_group_0_5',1]]
 free=[('auxiliary_quotient'if n=='j'else n)for n in parent['free']if n!='o']
 source=[];known=set(free)
 while rows:
  ready=[r for r in rows if all(type(v)is int or v in known for v in r[2:])]
  require(ready,'acyclic complete replacement source')
  for r in ready:source.append(r);known.add(r[0]);rows.remove(r)
 p=dict(mode=mode,first_gap=fg,auxiliary_gap=ag,source=source,free=free,witnesses=[n for n in free if n not in FIXED+['x']],ordinary_input='x',fixed_numerals=FIXED[:],output='shear_output',factors=FACTORS[:],exact_degree=deg,witness_domain='strictly positive integers',full_positive_zero_bijection=True,full_polynomial_identity=False,unconditional_integer_pullback=False,normalized_strong=False,scope='One complete linear-input ordinary-strong fixed-program product; all inherited compiler hypotheses required. Pinned-data CLI only.')
 p['ledger']=ledger(p);require(p['ledger']['operations']==cost and p['ledger']['M']==47 and p['ledger']['positive_witnesses']==18,'full child paid ledger')
 return p

def graph_proof(old,new):
 od={r[0]:r[1:]for r in old['source']};nd={r[0]:r[1:]for r in new['source']}
 uses=lambda n:[r[0]for r in old['source']if n in r[2:]]
 require(uses('o')==['of']and uses('j')==['jc']and uses('of')==['aux_u_rhs']and uses('jc')==['linear_difference'],'all removed coordinate consumers')
 require(uses('norm_linear')==['shear_group_0_6']and uses('shear_group_0_6')==['shear_output'],'omitted factor closure')
 require(all(od[n]==r for n,r in {'of':['*','o','f'],'aux_u_rhs':['-','of','R10a'],'jc':['*','j','R10a'],'linear_difference':['-','aux_u_rhs','jc'],'norm_linear':['+','linear_difference','index_difference']}.items()),'literal parent auxiliary and omitted-factor cut')
 require(all(nd[n]==r for n,r in {'auxiliary_Tf':['*','auxiliary_quotient','f'],'auxiliary_Tf_minus_one':['-','auxiliary_Tf',1],'auxiliary_c_Tf':['*','R10a','auxiliary_Tf_minus_one'],'auxiliary_R_f2':['*','r_lhs','L16'],'aux_u_rhs':['-','auxiliary_c_Tf','auxiliary_R_f2']}.items()),'literal child polynomial V cut')
 guards={'R16':['*','A','f_square_minus_one'],'f_square_minus_one':['-','L16',1],'strong_difference':['-','ic22','R16'],'norm_strong':['+','strong_difference',1],'a_plus_one':['+','R12',1],'index_product':['*','delta','a_plus_one'],'index_rhs':['+','odd_index','index_product'],'wn2':['*','w','q'],'sn2':['*','s','n2'],'kinner':['+','Kconstant','w']}
 require(all(od[n]==row and nd[n]==row for n,row in guards.items()),'actual linear modulus, ordinary strong, scale and shear')
 removed=set(od)-set(nd);require(removed=={'of','jc','linear_difference','norm_linear','shear_group_0_6'},'exact removed row set')
 common=set(od)&set(nd);changed={n for n in common if od[n]!=nd[n]}
 require(changed=={'aux_u_rhs','shear_output'},'only declared common row changes')
 def dag(p):
  defs={r[0]:r[1:]for r in p['source']};memo={'aux_u_rhs':('cut','V')}
  def get(v):
   if type(v)is int:return ('integer',v)
   if v not in defs:return ('supplied',v)
   if v not in memo:
    o,a,b=defs[v];memo[v]=(o,get(a),get(b))
   return memo[v]
  return get
 a,b=dag(old),dag(new);retained=sorted(common-{'shear_output'})
 require(all(a(n)==b(n)for n in retained),'every retained expression under proved V cut')
 for n in ('R10a','r_lhs','A','ic22','L16'):require(a(n)==b(n),'upstream cut independence '+n)
 def tail(p,ports):
  defs={r[0]:r[1:]for r in p['source']};memo={v:atom(v)for v in ports}
  def get(v):
   if type(v)is int:return const(v)
   if v not in memo:
    o,x,y=defs[v];x,y=get(x),get(y);memo[v]=mul(x,y)if o=='*'else add(x,y,1 if o=='+'else-1)
   return memo[v]
  return get(p['output'])
 product=const(1)
 for n in FACTORS:product=mul(product,atom(n))
 require(tail(new,FACTORS)==add(product,const(1),-1),'complete child finalizer')
 require(tail(old,FACTORS+['norm_linear'])==add(mul(product,atom('norm_linear')),const(1),-1),'complete parent finalizer')
 return dict(unchanged_rows=len(common)-2,retained_expression_identities=len(retained),removed_rows=sorted(removed),new_rows=sorted(set(nd)-set(od)),retained_factors=7,all_consumers_checked=True,full_factor_and_finalizer_identity_under_proved_correction=True)

def algebra():
 c,f,R,T,K,j=[atom(n)for n in ('c','f','R','T','K','j')]
 o=add(mul(c,T),mul(R,f),-1)
 V=add(mul(c,add(mul(T,f),const(1),-1)),mul(R,power(f,2)),-1)
 require(add(mul(o,f),c,-1)==V,'exact V identity')
 Nk=add(K,R,-1);Nl=add(add(V,mul(j,c),-1),K);res=add(add(V,R),mul(j,c),-1)
 require(add(Nl,Nk,-1)==res,'cleared omitted factor correction')
 require(add(V,R)==add(mul(c,add(mul(T,f),const(1),-1)),mul(R,add(power(f,2),const(1),-1)),-1),'rational j numerator')
 product=atom('retained_product');parent=add(mul(product,Nl),const(1),-1);child=add(product,const(1),-1)
 require(add(add(parent,const(1)),mul(add(child,const(1)),Nk),-1)==mul(add(child,const(1)),res),'full ring correction')
 x,a,b,g,h=[atom(n)for n in ('X','a','c','gamma','H')]
 left=add(power(sum_polys([x,mul(a,b),g]),2),mul(add(power(a,2),h),power(b,2)),-1)
 z=add(x,g);right=add(mul(z,add(z,mul(const(2),mul(a,b)))),mul(h,power(b,2)),-1)
 require(left==right,'exact main/input norm cancellation')
 v,e,L,k,G=[atom(n)for n in ('V','e','L','k','g')]
 require(add(power(v,2),power(add(v,e),2),-1)==mul(const(-1),mul(e,add(mul(const(2),v),e))),'exact auxiliary gap cancellation')
 require(add(power(add(L,G),2),mul(L,add(L,k)),-1)==add(power(G,2),mul(L,add(mul(const(2),G),k,-1))),'exact first gap norm')
 return dict(auxiliary_cut=True,first_gap_identity=True,auxiliary_gap_cancellation=True,norm_cancellation=True,whole_ring_correction_including_zero_c=True,rational_pullback_for_nonzero_c=True)

def degree(p):
 defs={r[0]:r[1:]for r in p['source']}
 guards={'norm_main':['-','L15','Ac2'],'L15':['*','R14','R14'],'R14':['+','D1','gam'],'D1':['+','wn2','cam2'],'cam2':['*','R10a','R12'],'norm_input':['-','mu2','scaled_kappa2'],'mu2':['*','exponent_rhs','exponent_rhs'],'exponent_rhs':['+','exponent_partial','modulus_multiple'],'exponent_partial':['+','W','difference_multiple'],'difference_multiple':['*','index_rhs','R12'],'Ac2':['*','A','c2'],'c2':['*','R10a','R10a'],'scaled_kappa2':['*','A','kappa2'],'kappa2':['*','index_rhs','index_rhs'],'A':['+','a_square','a4m5'],'a_square':['*','R12','R12']}
 if p['auxiliary_gap']:guards.update(y_aux=['+','aux_u_rhs','aux_gap'],H2=['*','aux_u_rhs','aux_u_rhs'],aux_y2=['*','y_aux','y_aux'],aux_square_gap=['-','H2','aux_y2'])
 require(all(defs[n]==row for n,row in guards.items()),'literal degree cancellation cones')
 env={n:(0 if n in FIXED else 1,atom(n))for n in p['free']}
 for n,op,a,b in p['source']:
  av=env[a]if type(a)is str else(0,const(a));bv=env[b]if type(b)is str else(0,const(b))
  v=times(av,bv)if op=='*'else plus(av,bv,1 if op=='+'else-1)
  if n in ('norm_main','norm_input'):
   off='wn2'if n=='norm_main'else'W';shift='gam'if n=='norm_main'else'modulus_multiple';ordinate='R10a'if n=='norm_main'else'index_rhs'
   z=plus(env[off],env[shift]);v=plus(times(z,plus(z,times((0,const(2)),times(env['R12'],env[ordinate])))),times(env['a4m5'],times(env[ordinate],env[ordinate])),-1)
  if n=='aux_square_gap'and p['auxiliary_gap']:
   v=times((0,const(-1)),times(env['aux_gap'],plus(times((0,const(2)),env['aux_u_rhs']),env['aux_gap'])))
  require(bool(v[1]),'nonzero symbolic highest form '+n);env[n]=v
 q=mul(atom('Bm1'),atom('Jrep'));k=add(atom('eta'),atom('zeta'));gamma=add(atom('rho'),atom('sigma'))
 c1=q
 for n in ('F','Z','alpha'):c1=add(c1,atom(n),-1)
 c1=add(c1,mul(atom('twice_cell_bits'),atom('x')),-1)
 t2=add(mul(atom('w'),c1),mul(atom('transport_quotient'),q),-1)
 def monomial(coef,ps):
  z=const(coef)
  for a,e in ps:z=mul(z,power(a,e))
  return z
 w,s,T,f,d,i,h=[atom(n)for n in ('w','s','auxiliary_quotient','f','delta','i','h')]
 first=monomial(1,[(w,1),(k,1),(s,2),(q,7),(add(mul(const(2),atom('tau_gap')),k,-1),1)])if p['first_gap']else monomial(-1,[(w,2),(k,2),(s,4),(q,14)])
 aux=monomial(-2,[(w,2),(k,1),(s,3),(q,11),(T,1),(f,3),(atom('aux_gap'),1)])if p['auxiliary_gap']else monomial(1,[(w,2),(k,2),(s,4),(q,14),(T,2),(f,4)])
 expected=[first,monomial(8,[(gamma,1),(w,2),(k,1),(s,3),(q,11)]),monomial(4,[(d,1),(add(mul(const(2),atom('rho')),d,-1),1),(w,3),(s,3),(q,12)]),aux,monomial(-1,[(h,1),(w,1),(s,1),(q,4)]),t2,monomial(1,[(i,2),(k,4),(s,4),(q,12)])]
 weights=[12 if p['first_gap']else 22,18,20,22 if p['auxiliary_gap']else 28,7,2,22]
 for n,dg,lead in zip(FACTORS,weights,expected):require(env[n]==(dg,lead),'entire factor leader '+n)
 wanted=const(1)
 for lead in expected:wanted=mul(wanted,lead)
 require(env[p['output']]==(sum(weights),wanted) and sum(weights)==p['exact_degree'],'entire exact homogeneous output')
 require(len(wanted)=={(False,False):240,(False,True):216,(True,False):456,(True,True):408}[p['first_gap'],p['auxiliary_gap']],'full leading coefficient support')
 return dict(exact_degree=p['exact_degree'],factor_degrees=weights,factor_leaders=[serialized(z)for z in expected],whole_leading_monomials=len(wanted),whole_leading_form=serialized(wanted),leading_form_sha256=sha(stable(serialized(wanted))),uniform_for_valid_fixed_compiler_numerals=True,all_supplied_coordinates_and_input_degree_one=True)

def evaluate(p,values):
 e=dict(values)
 for n,o,a,b in p['source']:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b
  e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def numerical(old,new,seed):
 rng=random.Random(seed);counts=Counter()
 for case in range(40):
  values={n:rng.randrange(-4,6)for n in new['free']}
  if case==0:values.update(eta=0,zeta=0)
  if case>=24:values={n:Fraction(v,3)for n,v in values.items()}
  e=evaluate(new,values);c,f,R,T=(e[n]for n in ('R10a','f','r_lhs','auxiliary_quotient'))
  restore={n:values[n]for n in old['free']if n not in ('o','j')};restore.update(o=c*T-R*f,j=Fraction(case-7,3)if case>=24 else case-7)
  v=evaluate(old,restore)
  require(all(v[n]==e[n]for n in FACTORS),'seven full retained factor evaluations')
  require(v[old['output']]+1-(e[new['output']]+1)*e['norm_index']==(e[new['output']]+1)*(e['aux_u_rhs']+R-restore['j']*c),'whole signed/rational ring correction')
  counts['whole_ring_corrections']+=1;counts['retained_factor_values']+=7
  if case>=24:counts['rational_cases']+=1
  if c:
   restore['j']=Fraction(e['aux_u_rhs']+R,c);v=evaluate(old,restore)
   require(v[old['output']]+1==(e[new['output']]+1)*e['norm_index'],'rational complete pullback');counts['rational_pullbacks']+=1
  else:counts['zero_c_corrections']+=1
  if new['auxiliary_gap']and e['y_aux']<0:counts['negative_computed_y_algebra_fixtures']+=1
 return dict(counts=dict(counts),scope='Supplemental exact signed/rational algebra fixtures; no auxiliary norm or full compiler zero asserted.')

def components():
 strong=aux=0
 for a in range(4):
  d=(a+2)**2-1
  for i in range(4):
   for c in range(4):
    for f in range(4):require(((i*c*c)**2-d*(f*f-1)+1)%4!=3,'ordinary strong sign');strong+=1
 for S in range(4):
  for V in range(4):
   for y in range(4):require((S*S*(V*V-y*y)+y*y)%4!=3,'signed auxiliary norm sign');aux+=1
 return dict(ordinary_strong_residue_cases=strong,signed_auxiliary_residue_cases=aux,scope='Residues supplement the proof; no native acceptance examples.')

def pareto(points):
 pts=sorted(set(points));return [list(p)for p in pts if not any(q[0]<=p[0]and q[1]<=p[1]and q!=p for q in pts)]
def verify(root):
 blobs=authenticate(root);data=json.loads(blobs['transport_shear_partition_census.json']);forms=[]
 for mode,index,fg,ag,cost,deg in MODES:
  old=select_parent(data,index,fg,ag);new=build(old,mode,fg,ag,cost,deg)
  forms.append(dict(mode=mode,parent_form_index=index,parent_ledger=old['ledger'],parent_exact_degree=old['exact_degree'],packet=new,source_proof=graph_proof(old,new),degree=degree(new),numerical=numerical(old,new,index+870119)))
 previous=json.loads(blobs['complete_auxiliary_unit_partition_frontier.json'])['frontier']
 # This is only the declared union with the saved 18-witness frontier.
 oldpts=[(x['plan']['operations'],x['plan']['exact_degree'])for x in previous]
 newpts=[(f['packet']['ledger']['operations'],f['packet']['exact_degree'])for f in forms]
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=copy.deepcopy(PINS),forms=forms,identities=algebra(),components=components(),frontier_comparison=dict(previous=sorted([list(p)for p in oldpts]),new=[list(p)for p in newpts],union=pareto(oldpts+newpts),scope='Union only with the saved complete_auxiliary_unit_partition_frontier, not a global circuit optimum.'),scope='Four complete 18-positive-witness ordinary-strong linear-input sources; full positive-zero bijection to each selected parent under its entire fixed compiler recipe. No ancestor Python execution, full zero materialization, new grouping census or maintained public API.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:require(same(r,json.loads(a.expect.read_text())),'type-exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status='PASS',forms=[dict(mode=f['mode'],ledger=f['packet']['ledger'],degree=f['degree']['exact_degree'])for f in r['forms']],frontier=r['frontier_comparison']['union'])))
if __name__=='__main__':main()
