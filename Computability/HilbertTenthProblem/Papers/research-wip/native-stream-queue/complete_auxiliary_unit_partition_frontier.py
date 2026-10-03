#!/usr/bin/env python3
"""Finite seven-unit partition grammar; saved-parent data only, no ancestor execution."""
import argparse,copy,hashlib,json
from pathlib import Path
from collections import Counter
from fractions import Fraction
PINS={'../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39', 'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b', 'complete75_reversed_auxiliary89.md': '4eddb6627b6261b1d8f8617006e443908574c0b7b2d3fdda15ff85dc86bd9700', 'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e', 'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b', 'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45', 'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'review_complete85_auxiliary_bezout_math.py': 'ea1c7d39b2afc6c1a004facac777b6ad97af89c5c92309e489439928abcbdd65', 'review_complete85_auxiliary_bezout_math.json': '9cdbf027fe1da74975043f4c5ba022b04e0e73eb92166cf2a1ed2ec1cc258d49', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', 'complete86_ordinary_auxiliary_projection.py': '130c8a09570866f3b510f4092aef3ab7fd61154f6c8776fcdba870d80a59019d', 'complete86_ordinary_auxiliary_projection.json': 'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6', 'complete86_ordinary_auxiliary_projection.md': 'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570', 'neary_woods_universal_tail_partitions.md': 'f6673dfebc6966b550ecd364c8f97b4cd02c7043a00070f6efc18a2102a7b387', 'complete_unit_partition_frontier109.md': 'd45817fbd03d2c5709bf39f90dd645428847308826eadfa011db050d53a2053a'}
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
  p=root/name
  # Newly frozen parent may be staged beside this source before installation.
  if not p.exists() and '/'not in name:p=Path(__file__).parent/name
  b=p.read_bytes();require(sha(b)==pin,'fresh pin '+name);blobs[name]=b
 return blobs

def closure(source,roots):
 d={r[0]:r for r in source};seen=set();stack=list(roots)
 while stack:
  n=stack.pop()
  if type(n)is str and n in d and n not in seen:seen.add(n);stack.extend(d[n][2:])
 return [r[:]for r in source if r[0]in seen]

def load_parents(blobs):
 out={}
 for mode,stem,flag,count in [('normalized','complete85_auxiliary_bezout_projection',True,85),('ordinary','complete86_ordinary_auxiliary_projection',False,86)]:
  r=json.loads(blobs[stem+'.json']);p=r['packet']
  require(r['source_sha256']==sha(blobs[stem+'.py']),'parent receipt source binding')
  for n,h in r['parent_pins'].items():require(n in PINS and PINS[n]==h,'retained parent dependency '+n)
  require(p['normalized']is flag and p['ordinary_input']=='x' and p['fixed_numerals']==FIXED and len(p['witnesses'])==18,'actual parent interface')
  require(ledger(p)['operations']==count,'actual full parent source count')
  c=closure(p['source'],FACTORS);d={r[0]:r[1:]for r in c}
  if mode=='ordinary':require(d['norm_strong']==['+','strong_difference',1],'actual private +1 strong producer')
  cm=sum(r[1]=='*'for r in c);ca=len(c)-cm
  require((cm,ca)==((42,36)if flag else(41,38)),'actual factor-producing core')
  out[mode]=dict(parent=p,core=c,weights=p['factor_exact_degrees'],core_M=cm,core_A=ca)
 require(out['normalized']['parent']['free']==out['ordinary']['parent']['free'],'same18 supplied witnesses and fixed interface')
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
 if mode=='ordinary'and g>1 and (6,)in groups:
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
 return dict(source=src,output=output,free=p['free'][:],witnesses=p['witnesses'][:],fixed_numerals=FIXED[:],ordinary_input='x',normalized=p['normalized'],plan=copy.deepcopy(info),positive_witnesses=18,full_positive_zero_set_unchanged=True,full_polynomial_identity_to_parent=(len(groups)==1 and anchor==0),scope='Complete source for one declared partition/finalizer; positive-zero equivalence to its own fixed-program parent, not unconditional polynomial equality or an all-integer zero theorem.')

def finalizer_proof(base,p):
 info=p['plan'];groups=info['groups'];a=info['anchor'];d={r[0]:r[1:]for r in p['source']}
 bd={r[0]:r[1:]for r in base['core']}
 present=set(bd)&set(d);require(all(bd[n]==d[n]for n in present),'unchanged literal core definitions')
 absent=set(bd)-set(d)
 require(absent==({'norm_strong'}if info['fold']!='none'else set()),'only private +1 pruned')
 require(len(p['witnesses'])==18 and p['free']==base['parent']['free'],'entire supplied interface retained')
 # A formal strong_difference cut proves the two source folds over Z.
 atoms={v:atom(v)for v in FACTORS}
 if info['mode']=='ordinary':atoms['norm_strong']=add(atom('strong_difference'),const(1))
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

def factor_leaders(base,mode):
 src=base['core'];d={r[0]:r[1:]for r in src}
 guards={'norm_main':['-','L15','Ac2'],'L15':['*','R14','R14'],'R14':['+','D1','gam'],'D1':['+','wn2','cam2'],'cam2':['*','R10a','R12'],
 'norm_input':['-','mu2','scaled_kappa2'],'mu2':['*','exponent_rhs','exponent_rhs'],'exponent_rhs':['+','exponent_partial','modulus_multiple'],'exponent_partial':['+','W','difference_multiple'],'difference_multiple':['*','index_rhs','R12'],
 'Ac2':['*','A','c2'],'c2':['*','R10a','R10a'],'scaled_kappa2':['*','A','kappa2'],'kappa2':['*','index_rhs','index_rhs'],'A':['+','a_square','a4m5'],'a_square':['*','R12','R12']}
 require(all(d[n]==r for n,r in guards.items()),'literal guarded degree-cancellation cones')
 e={n:(0 if n in FIXED else 1,atom(n))for n in base['parent']['free']}
 for n,o,a,b in src:
  av=e[a]if type(a)is str else(0,const(a));bv=e[b]if type(b)is str else(0,const(b));v=times(av,bv)if o=='*'else plus(av,bv,1 if o=='+'else-1)
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
 expected=[mon(-1,(w,2),(k,2),(s,4),(Q,14)),mon(8,(gamma,1),(w,2),(k,1),(s,3),(Q,11)),mon(-4,(delta,2),(w,5),(s,5),(Q,20)),None,mon(-1,(h,1),(w,1),(s,1),(Q,4)),tr,None]
 if mode=='ordinary':expected[3]=mon(1,(w,2),(k,2),(s,4),(Q,14),(T,2),(f,4));expected[6]=mon(1,(i,2),(k,4),(s,4),(Q,12))
 else:expected[3]=mon(1,(w,4),(i,2),(k,6),(s,10),(Q,34),(T,2),(f,2));expected[6]=mon(-1,(w,2),(i,2),(k,4),(s,6),(Q,20))
 require([e[n][0]for n in FACTORS]==base['weights'],'all seven actual exact degrees')
 require([e[n][1]for n in FACTORS]==expected,'all seven entire leading homogeneous forms')
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
 return dict(exact_degree=info['exact_degree'],leading_monomials=len(lead),leading_polynomial=[{'monomial':[[n,e]for n,e in m],'coefficient':c}for m,c in sorted(lead.items())],uniform_noncancellation='Nonzero factor products and sums of real squares for every valid fixed numerator recipe with Bm1>0; no zero-set substitution.')

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


def verify(root):
 blobs=authenticate(root);bases=load_parents(blobs);cancellation_identity()
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
 require(plans==8280,'entire declared finite grammar')
 frontier=[];best_degree=None
 for op,r in sorted(minimum_by_cost.items()):
  d=r['plan']['exact_degree']
  if best_degree is None or d<best_degree:frontier.append(r);best_degree=d
 require([(r['plan']['operations'],r['plan']['exact_degree'])for r in frontier]==[(85,175),(86,131),(89,110),(91,80),(93,64)],'finite family frontier')
 saved=[]
 for r in frontier:
  info=r['plan'];base=bases[info['mode']];p=emit(base,info)
  p['ledger']=ledger(p);p['finalizer_identity_sha256']=finalizer_proof(base,p);p['degree_certificate']=finalist_degree(base,info,leaders[info['mode']]);p['numeric_cases']=numeric_finalists(base,p)
  saved.append(p)
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=copy.deepcopy(PINS),grammar=dict(factors=FACTORS,set_partitions_per_base=877,anchor_choices_per_base=3263,plans_per_base=4140,total_plans=plans,fixed_products='Increasing factor indices, left-associated; no CSE/reassociation/coordinate search.',ordinary_singleton_folds=['(Ns-1)^2=strong_difference^2','Ns*(1+S)-1=strong_difference*(1+S)+S'],all_plans_generated_and_recounted=True,saved_complete_sources=len(saved)),cores={m:dict(M=b['core_M'],A=b['core_A'],operations=len(b['core']),factor_degrees=b['weights'],source_sha256=sha(stable(b['core'])))for m,b in bases.items()},census=dict(full_live_gates=total_gates,M=total_m,A=total_a,source_and_identity_stream_sha256=stream.hexdigest(),fold_counts=[dict(mode=m,fold=f,count=n)for(m,f),n in sorted(folds.items())],histogram=[dict(mode=m,operations=o,exact_degree=d,count=n)for(m,o,d),n in sorted(hist.items())],minima_by_mode_group_kind_fold=[v for k,v in sorted(minimum.items())],combined_minima_by_operation=[v for k,v in sorted(minimum_by_cost.items())]),frontier=frontier,forms=saved,scope='Exact finite grammar only, two18-positive-witness parents with their complete fixed-program hypotheses. Every plan is reconstructed, proved at the factor ports and recounted; only five frontier full arrays are saved. Positive-zero theorem by grouped product implication and parent all-seven=1 theorem. No global circuit optimality, fewer-than85 claim, or materialized universal Pell zero; no historical Python executed.')

def main():
 if not __debug__:raise RuntimeError('Run without optimized Python')
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();r=verify(args.root)
 if args.expect:require(same(r,json.loads(args.expect.read_text())),'type-exact saved receipt')
 if args.output:args.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status='PASS',plans=r['grammar']['total_plans'],gates=r['census']['full_live_gates'],frontier=[(x['plan']['operations'],x['plan']['exact_degree'])for x in r['frontier']])))
if __name__=='__main__':main()
