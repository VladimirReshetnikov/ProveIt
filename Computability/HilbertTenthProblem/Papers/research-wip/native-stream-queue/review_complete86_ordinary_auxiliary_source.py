#!/usr/bin/env python3
"""Independent literal-source and coefficient review; no author Python executes."""
import argparse, hashlib, json, random
from collections import Counter
from fractions import Fraction
from pathlib import Path

AUTHOR = {
 'complete86_ordinary_auxiliary_projection.py':'130c8a09570866f3b510f4092aef3ab7fd61154f6c8776fcdba870d80a59019d',
 'complete86_ordinary_auxiliary_projection.json':'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6',
 'complete86_ordinary_auxiliary_projection.md':'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570'}
PINS = {'../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39', 'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b', 'complete75_reversed_auxiliary89.md': '4eddb6627b6261b1d8f8617006e443908574c0b7b2d3fdda15ff85dc86bd9700', 'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e', 'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b', 'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45', 'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'review_complete85_auxiliary_bezout_math.py': 'ea1c7d39b2afc6c1a004facac777b6ad97af89c5c92309e489439928abcbdd65', 'review_complete85_auxiliary_bezout_math.json': '9cdbf027fe1da74975043f4c5ba022b04e0e73eb92166cf2a1ed2ec1cc258d49', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b'}

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
def authenticate(root,pins):
 out={}
 for name,pin in pins.items():
  b=(root/name).read_bytes();assert digest(b)==pin,('byte pin',name);out[name]=b
 return out

def independent_rewrite(old):
 # Independently derive the surviving definitions; schedule by dependency rank.
 removed={'of','aux_u_rhs','jc','linear_difference','norm_linear','eight_units','polynomial'}
 rows=[r[:] for r in old['source'] if r[0] not in removed]
 rows.extend([
 ['auxiliary_Tf','*','auxiliary_quotient','f'],
 ['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],
 ['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],
 ['auxiliary_R_f2','*','r_lhs','L16'],
 ['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],
 ['polynomial','-','seven_units',1]])
 free=[('auxiliary_quotient' if n=='j' else n) for n in old['free'] if n!='o']
 defs={r[0]:r[1:] for r in rows};depth={n:0 for n in free}
 def rank(n):
  if type(n)is int:return 0
  if n not in depth:depth[n]=1+max(rank(x) for x in defs[n][1:])
  return depth[n]
 return free,sorted(rows,key=lambda r:rank(r[0]))
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
def full_factor_proofs(old,new):
 od={r[0]:r[1:] for r in old['source']};nd={r[0]:r[1:] for r in new['source']}
 ring=Ring(new['free']+['independent_j']);child=ring.expression(nd)
 add,mul,power=ring.add,ring.mul,ring.power
 c,R,f,T=[child(n) for n in ['R10a','r_lhs','f','auxiliary_quotient']]
 restored_o=add(mul(c,T),mul(R,f),-1)
 parent=ring.expression(od,{'o':restored_o,'j':ring.v('independent_j')})
 expected_degrees=[22,18,32,28,7,2,22];summary=[];leaders=[]
 for name,wanted_degree in zip(FACTORS,expected_degrees):
  poly=child(name);assert parent(name)==poly,('entire factor identity',name)
  degree,leader=ring.top(poly);assert degree==wanted_degree;leaders.append(leader)
  summary.append({'factor':name,'degree':degree,'full_monomials':len(poly),'leading_monomials':len(leader),'full_polynomial_sha256':digest(stable(ring.serial(poly)))})
 assert parent('aux_u_rhs')==child('aux_u_rhs')
 assert parent('norm_linear')==add(add(child('norm_index'),add(child('aux_u_rhs'),R)),mul(c,ring.v('independent_j')),-1)
 # Compare every retained register structurally after the independently proved V cut.
 def DAG(rows):
  cache={'aux_u_rhs':('proved-cut','V')}
  def expr(n):
   if type(n)is int:return ('int',n)
   if n not in rows:return ('free',n)
   if n not in cache:
    op,a,b=rows[n];cache[n]=(op,expr(a),expr(b))
   return cache[n]
  return expr
 a,b=DAG(od),DAG(nd);common=(set(od)&set(nd))-{'polynomial'}
 assert all(a(n)==b(n) for n in common)
 q=mul(ring.v('Bm1'),ring.v('Jrep'));k=add(ring.v('eta'),ring.v('zeta'));g=add(ring.v('rho'),ring.v('sigma'))
 C=q
 for name in ['F','Z','alpha']:C=add(C,ring.v(name),-1)
 C=add(C,mul(ring.v('twice_cell_bits'),ring.v('x')),-1)
 transport=add(mul(ring.v('w'),C),mul(ring.v('transport_quotient'),q),-1)
 recipes=[(-1,[(k,2),('w',2),('s',4),(q,14)]),(8,[(g,1),(k,1),('w',2),('s',3),(q,11)]),(-4,[('delta',2),('w',5),('s',5),(q,20)]),(1,[(k,2),('w',2),('s',4),(q,14),(T,2),('f',4)]),(-1,[('h',1),('w',1),('s',1),(q,4)]),(1,[(transport,1)]),(1,[('i',2),(k,4),('s',4),(q,12)])]
 for got,(scalar,terms) in zip(leaders,recipes):
  want=ring.c(scalar)
  for value,exponent in terms:want=mul(want,power(ring.v(value) if type(value)is str else value,exponent))
  assert got==want
 whole=ring.c(1)
 for leader in leaders:whole=mul(whole,leader)
 want=ring.c(-32)
 for value,exponent in [(q,75),('h',1),(g,1),('delta',2),('i',2),(k,9),('w',12),('s',21),(T,2),('f',4),(transport,1)]:want=mul(want,power(ring.v(value) if type(value)is str else value,exponent))
 assert whole==want and len(whole)==120 and ring.top(whole)[0]==131
 monomial={'transport_quotient':1,'Jrep':76,'h':1,'rho':1,'delta':2,'i':2,'eta':9,'w':12,'s':21,'auxiliary_quotient':2,'f':4,'Bm1':76}
 assert whole[tuple(monomial.get(n,0) for n in ring.variables)]==32
 # Author serialization is checked only after our coefficient proof.
 author_serial=sorted((tuple((n,e[i]) for i,n in enumerate(ring.variables) if e[i]),v) for e,v in whole.items())
 return {'factors':summary,'factor_full_monomials':sum(x['full_monomials'] for x in summary),'retained_DAG_identities':len(common),'actual_auxiliary_and_linear_identities':2,'exact_whole_degree':131,'whole_leading_monomials':len(whole),'whole_leading_sha256':digest(stable(ring.serial(whole))),'author_leading_serial_sha256':digest(stable(author_serial)),'uniform_coefficient':'32*Bm1^76','uniform_witness_monomial':{k:v for k,v in monomial.items() if k!='Bm1'}}
def finalizers(old,new):
 ring=Ring(FACTORS+['norm_linear']);z=ring.c(1)
 for name in FACTORS:z=ring.mul(z,ring.v(name))
 old_tail=ring.expression({r[0]:r[1:] for r in old['source']})('polynomial')
 new_tail=ring.expression({r[0]:r[1:] for r in new['source']})('polynomial')
 assert new_tail==ring.add(z,ring.c(1),-1)
 assert old_tail==ring.add(ring.mul(z,ring.v('norm_linear')),ring.c(1),-1)
 return {'entire_paid_finalizers':2,'child_factors':FACTORS,'child_finalizer_gates':7,'parent_finalizer_gates':8,'cleared_correction':'Pparent+1=(Pchild+1)*(Nk+V+R-c*j)','rational_correction':'Pparent(restored)+1=(Pchild+1)*Nk for c != 0'}
def evaluate(p,values):
 env=dict(values)
 for n,op,a,b in p['source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b
  env[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return env
def numeric(old,new):
 rng=random.Random(1318647);counts=Counter();boundary=None
 for number in range(36):
  values={n:rng.randint(-3,5) for n in new['free']}
  # 12 genuinely rational source tuples; four c=0 cases retain cleared proof.
  if number>=24:values={n:Fraction(v,7) for n,v in values.items()}
  if number<4:values['eta']=values['zeta']=0
  child=evaluate(new,values);c,f,R,T=[child[n] for n in ['R10a','f','r_lhs','auxiliary_quotient']]
  restored={n:values[n] for n in old['free'] if n not in ['o','j']};restored.update(o=c*T-R*f,j=Fraction(number-9,5))
  parent=evaluate(old,restored)
  assert all(parent[n]==child[n] for n in FACTORS)
  assert parent['polynomial']+1==(child['polynomial']+1)*(child['norm_index']+child['aux_u_rhs']+R-c*restored['j'])
  counts['complete_cleared_corrections']+=1;counts['factor_values']+=7
  if number>=24:counts['rational_source_tuples']+=1
  if c:
   restored['j']=Fraction(child['aux_u_rhs']+R,c);parent=evaluate(old,restored)
   assert parent['polynomial']+1==(child['polynomial']+1)*child['norm_index']
   counts['complete_rational_pullbacks']+=1
  else:counts['zero_c_cleared_cases']+=1
 v={n:1 for n in new['free']};v.update(Bm1=15,Kconstant=83,twice_cell_bits=2,inner_bits=3,MC=1,MF=16,f=2)
 e=evaluate(new,v);j=Fraction(e['aux_u_rhs']+e['r_lhs'],e['R10a']);assert j.denominator>1
 boundary={'c':e['R10a'],'rational_j':[j.numerator,j.denominator],'positive_offzero_only':True}
 return {'counts':dict(counts),'offzero_nonintegrality':boundary}
def review(root,author_root):
 blobs=authenticate(root,PINS);ab=authenticate(author_root,AUTHOR);receipt=json.loads(ab['complete86_ordinary_auxiliary_projection.json'])
 assert exact(receipt['parent_pins'],PINS) and receipt['source_sha256']==AUTHOR['complete86_ordinary_auxiliary_projection.py']
 parents=json.loads(blobs['complete86_transport_quotient_shear.json'])['forms'];selected=[f['packet'] for f in parents if f['packet']['normalized'] is False];assert len(selected)==1
 old=selected[0];new=receipt['packet'];free,source=independent_rewrite(old)
 assert exact(new['source'],source) and exact(new['free'],free)
 od={r[0]:r[1:] for r in old['source']};nd={r[0]:r[1:] for r in new['source']}
 assert od['R16']==['*','A','f_square_minus_one'] and od['strong_difference']==['-','ic22','R16'] and od['norm_strong']==['+','strong_difference',1]
 assert [r[0] for r in old['source'] if 'o' in r[2:]]==['of']
 assert [r[0] for r in old['source'] if 'j' in r[2:]]==['jc']
 assert [r[0] for r in old['source'] if 'norm_linear' in r[2:]]==['eight_units']
 assert [r[0] for r in old['source'] if 'eight_units' in r[2:]]==['polynomial']
 assert sum(od[n]==nd[n] for n in set(od)&set(nd))==80
 assert set(od)-set(nd)=={'of','jc','linear_difference','norm_linear','eight_units'}
 assert {n for n in set(od)&set(nd) if od[n]!=nd[n]}=={'aux_u_rhs','polynomial'}
 parent_ledger=ledger(old);child_ledger=ledger(new)
 assert parent_ledger==dict(operations=87,M=47,A=40,naive_degree_upper=144)
 assert child_ledger==dict(operations=86,M=47,A=39,naive_degree_upper=141)==new['ledger']
 assert new['witnesses']==[n for n in free if n not in FIXED+['x']] and len(new['witnesses'])==18
 assert new['normalized'] is False and new['fixed_numerals']==FIXED and new['ordinary_input']=='x' and new['output']=='polynomial'
 assert new['factors']==FACTORS and new['exact_degree']==131 and new['factor_exact_degrees']==[22,18,32,28,7,2,22]
 assert new['full_positive_zero_bijection'] is True
 assert all(new[n] is False for n in ['full_integer_coordinate_bijection','whole_positive_orthant_map','full_polynomial_identity'])
 proof=full_factor_proofs(old,new)
 assert proof['author_leading_serial_sha256']==receipt['degree']['leading_form_sha256']
 return {'status':'PASS','review_source_sha256':digest(Path(__file__).read_bytes()),'author_pins':AUTHOR.copy(),'dependency_pins':PINS.copy(),'source':{'literal_rows_reconstructed':86,'unchanged_parent_definitions':80,'parent_ledger':parent_ledger,'child_ledger':child_ledger,'positive_witnesses':18,'full_liveness':True,'ordinary_strong_cones_guarded':True},'polynomial_proof':proof,'finalizers':finalizers(old,new),'numerical':numeric(old,new),'scope':'Independent actual-source, rational all-value pullback, complete paid finalizers and uniform exact degree audit. No author or historical Python executes. No public API audit, no independent reproof of the positive-zero rank theorem, and no complete positive universal zero is materialized.'}
def main():
 if not __debug__:raise RuntimeError('Assertions are proof checks; run without optimization')
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',required=True,type=Path);parser.add_argument('--author-root',type=Path);parser.add_argument('--output',type=Path);parser.add_argument('--expect',type=Path);args=parser.parse_args()
 result=review(args.root,args.author_root or args.root)
 if args.expect:assert exact(result,json.loads(args.expect.read_text())),'type-exact saved review receipt'
 if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':result['status'],'source':result['source'],'degree':result['polynomial_proof']['exact_whole_degree'],'numeric':result['numerical']['counts']},sort_keys=True))
if __name__=='__main__':main()
