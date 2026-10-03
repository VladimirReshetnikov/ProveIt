#!/usr/bin/env python3
"""Independent seven-factor finalizer census and full finalist source review."""
import argparse,hashlib,json
from collections import Counter,defaultdict
from fractions import Fraction
from itertools import combinations
from pathlib import Path
PINS={'../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39', 'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b', 'complete75_reversed_auxiliary89.md': '4eddb6627b6261b1d8f8617006e443908574c0b7b2d3fdda15ff85dc86bd9700', 'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e', 'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b', 'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45', 'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'review_complete85_auxiliary_bezout_math.py': 'ea1c7d39b2afc6c1a004facac777b6ad97af89c5c92309e489439928abcbdd65', 'review_complete85_auxiliary_bezout_math.json': '9cdbf027fe1da74975043f4c5ba022b04e0e73eb92166cf2a1ed2ec1cc258d49', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', 'complete86_ordinary_auxiliary_projection.py': '130c8a09570866f3b510f4092aef3ab7fd61154f6c8776fcdba870d80a59019d', 'complete86_ordinary_auxiliary_projection.json': 'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6', 'complete86_ordinary_auxiliary_projection.md': 'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570', 'neary_woods_universal_tail_partitions.md': 'f6673dfebc6966b550ecd364c8f97b4cd02c7043a00070f6efc18a2102a7b387', 'complete_unit_partition_frontier109.md': 'd45817fbd03d2c5709bf39f90dd645428847308826eadfa011db050d53a2053a'}
AUTHOR={'complete_auxiliary_unit_partition_frontier.py': '0e234ba9f4cb1889417ba281b1fe217906ac84c9c7c199395b8dfa36b2914f17', 'complete_auxiliary_unit_partition_frontier.json': 'e09f0bb97afa4cfdfdbc354fbc0c886bfdb608d6731a55b8db8314a3c7a89097', 'complete_auxiliary_unit_partition_frontier.md': '690de29dfb86f7c19709d2c88d54379267ca2e73b64cbc683b181fa07324e616'}
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
def digest(x): return hashlib.sha256(x).hexdigest()

def stable(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()

def exact(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

class Ring:
 def __init__(self,variables):
  self.variables=tuple(sorted(variables));self.index={n:i for i,n in enumerate(self.variables)};self.zero=(0,)*len(self.variables)
 def c(self,n): return {self.zero:n} if n else {}
 def v(self,n):
  e=list(self.zero);e[self.index[n]]=1;return {tuple(e):1}
 def add(self,a,b,sign=1):
  out=dict(a)
  for e,n in b.items():out[e]=out.get(e,0)+sign*n
  return {e:n for e,n in out.items() if n}
 def mul(self,a,b):
  out={}
  for e,n in a.items():
   for f,m in b.items():
    g=tuple(x+y for x,y in zip(e,f));out[g]=out.get(g,0)+n*m
  return {e:n for e,n in out.items() if n}
 def power(self,a,n):
  out=self.c(1)
  for _ in range(n):out=self.mul(out,a)
  return out
 def expression(self,rows,substitutions=None):
  cache={n:self.v(n) for n in self.variables};cache.update(substitutions or {})
  def get(n):
   if type(n)is int:return self.c(n)
   if n not in cache:
    op,a,b=rows[n];a,b=get(a),get(b);cache[n]=self.mul(a,b) if op=='*' else self.add(a,b,1 if op=='+' else -1)
   return cache[n]
  return get
 def top(self,p):
  weight=[int(n not in FIXED) for n in self.variables]
  degrees={e:sum(x*w for x,w in zip(e,weight)) for e in p};d=max(degrees.values())
  return d,{e:n for e,n in p.items() if degrees[e]==d}
 def serial(self,p):
  return [[[[n,e[i]] for i,n in enumerate(self.variables) if e[i]],v] for e,v in sorted(p.items())]

def ledger(p):
 known={n:0 if n in FIXED else 1 for n in p['free']};defs={};counts=Counter()
 assert len(known)==len(p['free'])
 for n,op,a,b in p['source']:
  assert n not in known and op in ['+','-','*']
  assert all(type(v)is int or type(v)is str and v in known for v in [a,b])
  da,db=[known[v] if type(v)is str else 0 for v in [a,b]]
  known[n]=da+db if op=='*' else max(da,db);defs[n]=[a,b];counts['M' if op=='*' else 'A']+=1
 gates=set();leaves=set()
 def visit(n):
  if type(n)is int:return
  if n not in defs:leaves.add(n);return
  if n not in gates:
   gates.add(n)
   for v in defs[n]:visit(v)
 visit(p['output']);assert gates==set(defs) and leaves==set(p['free'])
 return {'operations':len(defs),'M':counts['M'],'A':counts['A'],'naive_degree_upper':known[p['output']]}

def evaluate(p,values):
 env=dict(values)
 for n,op,a,b in p['source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b
  env[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return env

def partitions(left):
 if not left:
  yield ();return
 pivot=min(left);tail=sorted(left-{pivot})
 for size in range(len(tail)+1):
  for rest in combinations(tail,size):
   block=(pivot,)+rest
   for suffix in partitions(left-set(block)):yield (block,)+suffix

def core(parent):
 defs={r[0]:r[1:] for r in parent['source']};seen=set()
 def visit(n):
  if n in defs and n not in seen:
   seen.add(n)
   for v in defs[n][1:]:
    if type(v)is str:visit(v)
 for f in FACTORS:visit(f)
 return [r[:] for r in parent['source'] if r[0] in seen]

def emit(parent,mode,blocks,anchor):
 fold=mode=='ordinary' and (6,) in blocks
 rows=[r[:] for r in core(parent) if not(fold and r[0]=='norm_strong')]
 def pay(n,op,a,b):rows.append([n,op,a,b]);return n
 products=[]
 for g,block in enumerate(blocks):
  p=FACTORS[block[0]]
  for j,f in enumerate(block[1:]):p=pay(f'review_g{g}_m{j}','*',p,FACTORS[f])
  products.append(p)
 g=len(blocks)
 if g==1 and anchor==0:
  out=pay('review_output','-',products[0],1)
 else:
  squares=[]
  for j,p in enumerate(products):
   if j==anchor:continue
   residual='strong_difference' if fold and blocks[j]==(6,) else pay(f'review_res{j}','-',p,1)
   squares.append(pay(f'review_square{j}','*',residual,residual))
  total=squares[0]
  for j,square in enumerate(squares[1:]):total=pay(f'review_sum{j}','+',total,square)
  if anchor is None:out=total
  else:
   offset=pay('review_offset','+',total,1)
   if fold and blocks[anchor]==(6,):
    product=pay('review_anchored','*','strong_difference',offset)
    out=pay('review_output','+',product,total)
   else:
    product=pay('review_anchored','*',products[anchor],offset)
    out=pay('review_output','-',product,1)
 return {'source':rows,'free':parent['free'][:],'output':out}

def theoretical(mode,blocks,anchor,weights):
 g=len(blocks);ds=[sum(weights[i] for i in b) for b in blocks];base=78 if mode=='normalized' else 79
 ops=base+6+2*g;M=49 if mode=='normalized' else 48;degree=2*max(ds)
 if anchor is not None:
  if g==1:ops=base+7;M-=1;degree=ds[0]
  else:degree=ds[anchor]+2*max(d for j,d in enumerate(ds) if j!=anchor)
 if mode=='ordinary' and (6,)in blocks:ops-=1 if anchor==blocks.index((6,)) else 2
 return ops,M,ops-M,degree

def partition_polynomial(ring,blocks,anchor,mode):
 units=[ring.v(n) for n in FACTORS]
 if mode=='ordinary':units[6]=ring.add(ring.v('strong_difference'),ring.c(1))
 products=[]
 for block in blocks:
  p=ring.c(1)
  for i in block:p=ring.mul(p,units[i])
  products.append(p)
 if anchor is not None and len(blocks)==1:return ring.add(products[anchor],ring.c(1),-1)
 total=ring.c(0)
 for i,p in enumerate(products):
  if i!=anchor:total=ring.add(total,ring.power(ring.add(p,ring.c(1),-1),2))
 return total if anchor is None else ring.add(ring.mul(products[anchor],ring.add(total,ring.c(1))),ring.c(1),-1)

def abstract_tail(p,blocks,anchor,mode):
 ring=Ring(FACTORS+['strong_difference'])
 # All-value Ns=D+1 is used only for the actual ordinary source.
 subs={'norm_strong':ring.add(ring.v('strong_difference'),ring.c(1))} if mode=='ordinary' else {}
 actual=ring.expression({r[0]:r[1:] for r in p['source']},subs)(p['output'])
 expected=partition_polynomial(ring,blocks,anchor,mode)
 assert actual==expected
 return digest(stable(canonical(ring,actual)))

def factor_data(parent,mode):
 ring=Ring(parent['free']);get=ring.expression({r[0]:r[1:] for r in parent['source']})
 wanted=[22,18,32,60,7,2,34] if mode=='normalized' else [22,18,32,28,7,2,22]
 factors=[];tops={}
 for row in core(parent):tops[row[0]]=ring.top(get(row[0]))
 for name,degree in zip(FACTORS,wanted):
  poly=get(name);d,top=tops[name];assert d==degree
  factors.append({'name':name,'degree':d,'full_terms':len(poly),'top_terms':len(top),'full_sha256':digest(stable(ring.serial(poly)))})
 # Uniformly nonzero actual leaders, keeping all fixed numerals symbolic.
 v=ring.v;mul=ring.mul;add=ring.add;pw=ring.power;q=mul(v('Bm1'),v('Jrep'));k=add(v('eta'),v('zeta'));gamma=add(v('rho'),v('sigma'))
 C=q
 for name in ['F','Z','alpha']:C=add(C,v(name),-1)
 C=add(C,mul(v('twice_cell_bits'),v('x')),-1)
 transport=add(mul(v('w'),C),mul(v('transport_quotient'),q),-1)
 common=[(-1,[(k,2),('w',2),('s',4),(q,14)]),(8,[(gamma,1),(k,1),('w',2),('s',3),(q,11)]),(-4,[('delta',2),('w',5),('s',5),(q,20)])]
 aux=(1,[('i',2),(k,6),('w',4),('s',10),(q,34),('auxiliary_quotient',2),('f',2)]) if mode=='normalized' else(1,[(k,2),('w',2),('s',4),(q,14),('auxiliary_quotient',2),('f',4)])
 strong=(-1,[('i',2),(k,4),('w',2),('s',6),(q,20)]) if mode=='normalized' else(1,[('i',2),(k,4),('s',4),(q,12)])
 recipes=common+[aux,(-1,[('h',1),('w',1),('s',1),(q,4)]),(1,[(transport,1)]),strong]
 for name,(scalar,terms) in zip(FACTORS,recipes):
  expected=ring.c(scalar)
  for value,n in terms:expected=mul(expected,pw(v(value) if type(value)is str else value,n))
  assert tops[name][1]==expected
 return ring,tops,{'factors':factors,'full_factor_terms':sum(r['full_terms'] for r in factors),'weights':wanted,'uniform_nonzero_for_Bm1_positive':True}

def exact_output_leader(packet,ring,tops):
 env={n:(0 if n in FIXED else 1,ring.v(n)) for n in packet['free']}
 for name,op,a,b in packet['source']:
  if name in tops:env[name]=tops[name];continue
  da,pa=env[a] if type(a)is str else(0,ring.c(a));db,pb=env[b] if type(b)is str else(0,ring.c(b))
  if op=='*':out=(da+db,ring.mul(pa,pb))
  else:
   d=max(da,db);out=(d,ring.add(pa if da==d else{},pb if db==d else{},1 if op=='+' else -1))
  assert out[1],('unexpected leading cancellation',name)
  env[name]=out
 return env[packet['output']]

def canonical(ring,poly):
 return sorted((tuple((n,e[i]) for i,n in enumerate(ring.variables) if e[i]),value) for e,value in poly.items())

def rename_packet(p):
 def name(n):
  if type(n)is not str or not n.startswith('review_'):return n
  if n.startswith('review_g'):
   g,m=n[len('review_g'):].split('_m');return f'group_{g}_product_{m}'
  for prefix,suffix in [('review_res','residual'),('review_square','square')]:
   if n.startswith(prefix):return f'group_{n[len(prefix):]}_{suffix}'
  if n.startswith('review_sum'):return 'sos_sum_'+n[len('review_sum'):]
  return {'review_offset':'sos_plus_one','review_anchored':'anchor_scaled','review_output':'partition_output'}[n]
 return {'source':[[name(n),op,name(a),name(b)] for n,op,a,b in p['source']],'free':p['free'][:],'output':name(p['output'])}

def descriptor(mode,blocks,anchor,weights):
 op,M,A,d=theoretical(mode,blocks,anchor,weights)
 fold='none'
 if mode=='ordinary' and (6,)in blocks:fold='anchor_plus_one' if anchor==blocks.index((6,)) else 'squared_plus_one'
 return {'mode':mode,'groups':[list(b)for b in blocks],'anchor':anchor,'kind':'sos' if anchor is None else'anchor','group_weights':[sum(weights[i]for i in b)for b in blocks],'fold':fold,'M':M,'A':A,'operations':op,'exact_degree':d}

def census(parents):
 ps=list(partitions(set(range(7))));assert len(ps)==len(set(ps))==877
 # The subset recursion is independent; sort its completed partitions only to
 # reproduce the author's stream order, using the restricted-growth encoding.
 ps.sort(key=lambda p:tuple(next(j for j,b in enumerate(p)if i in b)for i in range(7)))
 assert sum(map(len,ps))==3263
 hist=Counter();folds=Counter();totals=Counter();group_counts=Counter(map(len,ps));stream=hashlib.sha256();minima={};combined={};plans={}
 for mode,parent in parents.items():
  weights=[22,18,32,60,7,2,34] if mode=='normalized' else[22,18,32,28,7,2,22]
  for blocks in ps:
   for anchor in [None]+list(range(len(blocks))):
    info=descriptor(mode,blocks,anchor,weights);p=rename_packet(emit(parent,mode,blocks,anchor));ld=ledger(p)
    assert [ld[k]for k in ['operations','M','A']]==[info[k]for k in ['operations','M','A']]
    proof=abstract_tail(p,blocks,anchor,mode)
    stream.update(stable({'plan':info,'source':p['source'],'output':p['output'],'proof':proof}));stream.update(b'\n')
    totals.update(gates=ld['operations'],M=ld['M'],A=ld['A'],plans=1)
    hist[mode,info['operations'],info['exact_degree']]+=1;folds[mode,info['fold']]+=1
    for key,out in [((mode,len(blocks),info['kind'],info['fold']),minima),(info['operations'],combined)]:
     if key not in out or info['exact_degree']<out[key]['plan']['exact_degree']:out[key]={'plan':info,'multiplicity':1}
     elif info['exact_degree']==out[key]['plan']['exact_degree']:out[key]['multiplicity']+=1
    plans[(mode,blocks,anchor)]=info
 assert totals['plans']==8280
 best=10**9;frontier=[]
 for op,minimum in sorted(combined.items()):
  if minimum['plan']['exact_degree']<best:frontier.append(minimum);best=minimum['plan']['exact_degree']
 return {'plans':plans,'totals':dict(totals),'partition_group_counts':{str(k):v for k,v in sorted(group_counts.items())},'source_stream_sha256':stream.hexdigest(),'histogram':[dict(mode=m,operations=o,exact_degree=d,count=n)for(m,o,d),n in sorted(hist.items())],'fold_counts':[dict(mode=m,fold=f,count=n)for(m,f),n in sorted(folds.items())],'minima':[v for k,v in sorted(minima.items())],'combined_minima':[v for k,v in sorted(combined.items())],'frontier':frontier}

def numeric_finalist(parent,p):
 counts=Counter();info=p['plan']
 for case in range(18):
  values={n:((case+5)*(i+7)%11)-5 for i,n in enumerate(p['free'])}
  if case>=12:values={n:Fraction(v,5) for n,v in values.items()}
  base=evaluate(parent,values);child=evaluate(p,values);products=[]
  for block in info['groups']:
   product=1
   for i in block:product*=base[FACTORS[i]]
   products.append(product)
  anchor=info['anchor'];S=sum((g-1)**2 for i,g in enumerate(products) if i!=anchor)
  want=S if anchor is None else products[anchor]-1 if len(products)==1 else products[anchor]*(1+S)-1
  assert child[p['output']]==want
  counts['whole_evaluations']+=1
  if case>=12:counts['rational_evaluations']+=1
 return dict(counts)

def authenticate(root,pins):
 out={}
 for name,h in pins.items():
  b=(root/name).read_bytes();assert digest(b)==h,('pin',name);out[name]=b
 return out

def review(root,author_root):
 blobs=authenticate(root,PINS);author_blobs=authenticate(author_root,AUTHOR);author=json.loads(author_blobs['complete_auxiliary_unit_partition_frontier.json'])
 assert author['source_sha256']==AUTHOR['complete_auxiliary_unit_partition_frontier.py'] and exact(author['parent_pins'],PINS)
 parents={}
 for mode,stem in [('normalized','complete85_auxiliary_bezout_projection'),('ordinary','complete86_ordinary_auxiliary_projection')]:
  receipt=json.loads(blobs[stem+'.json']);assert receipt['source_sha256']==PINS[stem+'.py'];parent=receipt['packet'];parents[mode]=parent
  assert parent['normalized']is(mode=='normalized') and len(parent['witnesses'])==18 and parent['fixed_numerals']==FIXED and parent['ordinary_input']=='x'
  assert all(PINS[name]==h for name,h in receipt['parent_pins'].items())
 assert parents['ordinary']['free']==parents['normalized']['free']
 assert {r[0]:r[1:]for r in core(parents['ordinary'])}['norm_strong']==['+','strong_difference',1]
 # The private +1 row has no other factor-core consumer.
 assert not [r for r in core(parents['ordinary'])if 'norm_strong'in r[2:]]
 coverage=census(parents);ac=author['census']
 for ours,theirs in [('source_stream_sha256','source_and_identity_stream_sha256'),('histogram','histogram'),('fold_counts','fold_counts'),('minima','minima_by_mode_group_kind_fold'),('combined_minima','combined_minima_by_operation')]:assert exact(coverage[ours],ac[theirs]),ours
 assert exact(coverage['frontier'],author['frontier'])
 assert coverage['totals']==dict(gates=ac['full_live_gates'],M=ac['M'],A=ac['A'],plans=author['grammar']['total_plans'])
 assert [(r['plan']['operations'],r['plan']['exact_degree']) for r in coverage['frontier']]==[(85,175),(86,131),(89,110),(91,80),(93,64)]
 cache={};factor_reports={}
 for mode,parent in parents.items():
  ring,tops,report=factor_data(parent,mode);cache[mode]=(ring,tops);factor_reports[mode]=report;c=core(parent);M=sum(r[1]=='*'for r in c)
  assert author['cores'][mode]=={'M':M,'A':len(c)-M,'operations':len(c),'factor_degrees':report['weights'],'source_sha256':digest(stable(c))}
 saved=[];numeric=Counter()
 assert len(author['forms'])==5
 for p,minimum in zip(author['forms'],coverage['frontier']):
  info=p['plan'];assert exact(info,minimum['plan']);mode=info['mode'];blocks=tuple(tuple(b)for b in info['groups']);anchor=info['anchor'];parent=parents[mode]
  rebuilt=rename_packet(emit(parent,mode,blocks,anchor))
  assert exact(p['source'],rebuilt['source']) and p['output']==rebuilt['output'] and p['free']==rebuilt['free']
  assert p['witnesses']==parent['witnesses'] and p['fixed_numerals']==FIXED and p['ordinary_input']=='x' and p['normalized'] is parent['normalized']
  assert p['positive_witnesses']==18 and p['full_positive_zero_set_unchanged'] is True
  assert p['full_polynomial_identity_to_parent'] is (len(blocks)==1 and anchor==0)
  ld=ledger(p);assert ld==p['ledger'];proof=abstract_tail(p,blocks,anchor,mode);assert proof==p['finalizer_identity_sha256']
  ring,tops=cache[mode];degree,leader=exact_output_leader(p,ring,tops)
  certificate=[{'monomial':[[n,k]for n,k in monomial],'coefficient':value} for monomial,value in canonical(ring,leader)]
  assert degree==info['exact_degree']==p['degree_certificate']['exact_degree']
  assert len(leader)==p['degree_certificate']['leading_monomials'] and exact(certificate,p['degree_certificate']['leading_polynomial'])
  numeric.update(numeric_finalist(parent,p))
  saved.append({'plan':info,'complete_source_sha256':digest(stable(p['source'])),'ledger':ld,'entire_leading_polynomial_sha256':digest(stable(certificate)),'leading_monomials':len(leader),'exact_degree':degree})
 # An arbitrary signed seven-factor product need not imply singleton units;
 # the semantic converse explicitly inherits each native parent's +1 theorem.
 abstract_units=[-1,-1,1,1,1,1,1];product=1
 for u in abstract_units:product*=u
 assert product==1 and sum((u-1)**2 for u in abstract_units)==8
 return {'status':'PASS','review_source_sha256':digest(Path(__file__).read_bytes()),'author_pins':AUTHOR.copy(),'dependency_pins':PINS.copy(),'census':{k:v for k,v in coverage.items()if k!='plans'},'actual_factor_expansions':factor_reports,'saved_finalists':saved,'supplementary_numeric':dict(numeric),'source_finalizer_identities':8280,'positive_zero_scope':'Same supplied positive integer tuple on each own valid fixed-program slice. Child groups imply original factor product1; converse inherits all seven factors+1 at parent zeros. Not an all-integer or real parent-zero equivalence.','scope':'Complete declared two-core SOS/one-anchor grammar with precisely the two ordinary singleton-Ns folds. All8280 sources reconstructed independently and source/proof stream matched; all five saved sources and full leaders audited. No global optimization claim, maintained API audit, historical Python execution, or materialized native universal zero.'}

def main():
 if not __debug__:raise RuntimeError('Assertions carry review checks; run without optimization')
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True);parser.add_argument('--author-root',type=Path);parser.add_argument('--output',type=Path);parser.add_argument('--expect',type=Path);args=parser.parse_args()
 result=review(args.root,args.author_root or args.root)
 assert exact(result,json.loads(json.dumps(result))),'type-exact JSON roundtrip'
 if args.expect:assert exact(result,json.loads(args.expect.read_text())),'type-exact saved review receipt'
 if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':result['status'],'totals':result['census']['totals'],'factor_monomials':sum(x['full_factor_terms']for x in result['actual_factor_expansions'].values()),'frontier':[(x['plan']['operations'],x['exact_degree'])for x in result['saved_finalists']]},sort_keys=True))
if __name__=='__main__':main()
