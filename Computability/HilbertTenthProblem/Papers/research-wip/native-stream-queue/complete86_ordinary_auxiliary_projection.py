#!/usr/bin/env python3
"""Ordinary-strong auxiliary quotient: one complete source; pinned-data CLI only.
No author/ancestor Python is imported or executed.
"""
import argparse,copy,hashlib,json,random
from pathlib import Path
from collections import Counter
from fractions import Fraction
PINS={'../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39', 'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b', 'complete75_reversed_auxiliary89.md': '4eddb6627b6261b1d8f8617006e443908574c0b7b2d3fdda15ff85dc86bd9700', 'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e', 'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b', 'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45', 'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'review_complete85_auxiliary_bezout_math.py': 'ea1c7d39b2afc6c1a004facac777b6ad97af89c5c92309e489439928abcbdd65', 'review_complete85_auxiliary_bezout_math.json': '9cdbf027fe1da74975043f4c5ba022b04e0e73eb92166cf2a1ed2ec1cc258d49', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b'}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
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
def degree(p):
 defs={r[0]:r[1:]for r in p['source']}
 guards={'norm_main':['-','L15','Ac2'],'L15':['*','R14','R14'],'R14':['+','D1','gam'],'D1':['+','wn2','cam2'],'cam2':['*','R10a','R12'],
 'norm_input':['-','mu2','scaled_kappa2'],'mu2':['*','exponent_rhs','exponent_rhs'],'exponent_rhs':['+','exponent_partial','modulus_multiple'],'exponent_partial':['+','W','difference_multiple'],'difference_multiple':['*','index_rhs','R12'],
 'Ac2':['*','A','c2'],'c2':['*','R10a','R10a'],'scaled_kappa2':['*','A','kappa2'],'kappa2':['*','index_rhs','index_rhs'],'A':['+','a_square','a4m5'],'a_square':['*','R12','R12']}
 require(all(defs[n]==row for n,row in guards.items()),'literal norm cone guards')
 e={n:(0 if n in FIXED else 1,atom(n))for n in p['free']}
 for n,o,a,b in p['source']:
  av=e[a]if type(a)is str else(0,const(a));bv=e[b]if type(b)is str else(0,const(b))
  v=times(av,bv)if o=='*'else plus(av,bv,1 if o=='+'else-1)
  if n in ('norm_main','norm_input'):
   off='wn2'if n=='norm_main'else'W';shift='gam'if n=='norm_main'else'modulus_multiple';ordinate='R10a'if n=='norm_main'else'index_rhs'
   t=plus(e[off],e[shift]);v=plus(times(t,plus(t,times((0,const(2)),times(e['R12'],e[ordinate])))),times(e['a4m5'],times(e[ordinate],e[ordinate])),-1)
  e[n]=v
  require(bool(v[1]),'nonzero symbolic top form '+n)
 q=mul(atom('Bm1'),atom('Jrep'));k=add(atom('eta'),atom('zeta'));g=add(atom('rho'),atom('sigma'))
 c1=q
 for n in ('F','Z','alpha'):c1=add(c1,atom(n),-1)
 c1=add(c1,mul(atom('twice_cell_bits'),atom('x')),-1)
 t2=add(mul(atom('w'),c1),mul(atom('transport_quotient'),q),-1)
 wanted=const(-32)
 for poly,exp in [(q,75),(atom('h'),1),(g,1),(atom('delta'),2),(atom('i'),2),(k,9),(atom('w'),12),(atom('s'),21),(t2,1),(atom('auxiliary_quotient'),2),(atom('f'),4)]:wanted=mul(wanted,power(poly,exp))
 require(e['polynomial']==(131,wanted),'entire uniform homogeneous leading form')
 fd=[e[n][0]for n in FACTORS];require(fd==[22,18,32,28,7,2,22]and sum(fd)==131,'actual exact factor degrees')
 return dict(exact_degree=131,factor_degrees=fd,whole_leading_monomials=len(wanted),leading_form_sha256=sha(stable(sorted((list(m),c)for m,c in wanted.items()))),uniform_fixed_numeral_proof=True)

def evaluate(p,v):
 e=dict(v)
 for n,o,a,b in p['source']:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b
  e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def authenticate(root):
 blobs={}
 for name,pin in PINS.items():
  data=(root/name).read_bytes();require(sha(data)==pin,'fresh pin '+name);blobs[name]=data
 return blobs

def select_parent(blobs):
 data=json.loads(blobs['complete86_transport_quotient_shear.json'])
 matches=[f['packet']for f in data['forms']if f['packet']['normalized']is False]
 require(len(matches)==1,'unique actual ordinary parent')
 p=copy.deepcopy(matches[0]);require(p['output']=='polynomial'and p['exact_degree']==134,'ordinary parent binding')
 require(ledger(p)==dict(operations=87,M=47,A=40,naive_degree_upper=144),'complete ordinary parent ledger')
 require(p['free']==p['witnesses']+['x']+FIXED and len(p['witnesses'])==19,'parent interface')
 return p

def build(parent):
 remove={'of','jc','linear_difference','norm_linear','eight_units'}
 rows=[r[:]for r in parent['source']if r[0]not in remove and r[0]not in ('aux_u_rhs','polynomial')]
 rows += [['auxiliary_Tf','*','auxiliary_quotient','f'],
 ['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],
 ['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],
 ['auxiliary_R_f2','*','r_lhs','L16'],
 ['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],
 ['polynomial','-','seven_units',1]]
 free=[('auxiliary_quotient'if n=='j'else n)for n in parent['free']if n!='o']
 # Stable topological emission pays every row. The new V depends on the
 # already retained packing R, so the parent's original order is not valid.
 source=[];known=set(free)
 while rows:
  ready=[r for r in rows if all(type(v)is int or v in known for v in r[2:])]
  require(ready,'acyclic replacement source')
  for r in ready:source.append(r);known.add(r[0]);rows.remove(r)
 p=dict(source=source,free=free,witnesses=[n for n in free if n not in FIXED+['x']],ordinary_input='x',fixed_numerals=FIXED[:],normalized=False,output='polynomial',factors=FACTORS[:],witness_domain='strictly positive integers',full_positive_zero_bijection=True,full_integer_coordinate_bijection=False,whole_positive_orthant_map=False,full_polynomial_identity=False,coordinate={'new':'auxiliary_quotient','removed':['o','j'],'forward_on_parent_zeros':'T=(o+R*f)/c','inverse_on_child_zeros':{'o':'c*T-R*f','j':'(V+R)/c'},'rational_inverse_scope':'c != 0; integral and positive only on proved positive zeros'},scope='One complete ordinary-strong universal fixed-program source; full inherited compiler recipe required. Bounded pinned-data CLI; no maintained public API.')
 p['ledger']=ledger(p);require(p['ledger']==dict(operations=86,M=47,A=39,naive_degree_upper=141),'complete child ledger')
 p['exact_degree']=131;p['factor_exact_degrees']=[22,18,32,28,7,2,22]
 return p

def graph_proof(old,new):
 od={r[0]:r[1:]for r in old['source']};nd={r[0]:r[1:]for r in new['source']}
 uses=lambda n:[r[0]for r in old['source']if n in r[2:]]
 require(uses('o')==['of']and uses('j')==['jc'],'all removed coordinate consumers')
 require(uses('norm_linear')==['eight_units']and uses('eight_units')==['polynomial'],'omitted factor closure')
 require(od['R16']==['*','A','f_square_minus_one']and od['f_square_minus_one']==['-','L16',1]and od['strong_difference']==['-','ic22','R16']and od['norm_strong']==['+','strong_difference',1],'literal ordinary strong and auxiliary coefficient')
 removed=set(od)-set(nd);require(removed=={'of','jc','linear_difference','norm_linear','eight_units'},'exact removed row set')
 common=set(od)&set(nd);changed={n for n in common if od[n]!=nd[n]}
 require(changed=={'aux_u_rhs','polynomial'},'only declared common rows changed')
 # A cut at V is legitimate by the expanded local polynomial identity below.
 # Recursively compare every common retained expression, not just its name.
 def dag(p):
  defs={r[0]:r[1:]for r in p['source']};memo={'aux_u_rhs':('cut','V')}
  def get(v):
   if type(v)is int:return ('integer',v)
   if v not in defs:return ('supplied',v)
   if v not in memo:
    o,a,b=defs[v];memo[v]=(o,get(a),get(b))
   return memo[v]
  return get
 a,b=dag(old),dag(new)
 retained=sorted(common-{'polynomial'})
 require(all(a(n)==b(n)for n in retained),'all retained expression DAGs under proved V cut')
 for name in ('R10a','r_lhs','A','ic22','L16'):require(a(name)==b(name),'upstream cut independence '+name)
 def tail(p,ports):
  defs={r[0]:r[1:]for r in p['source']};memo={v:atom(v)for v in ports}
  def get(v):
   if type(v)is int:return const(v)
   if v not in memo:
    o,x,y=defs[v];x,y=get(x),get(y);memo[v]=mul(x,y)if o=='*'else add(x,y,1 if o=='+'else-1)
   return memo[v]
  return get('polynomial')
 product=const(1)
 for n in FACTORS:product=mul(product,atom(n))
 require(tail(new,FACTORS)==add(product,const(1),-1),'entire child product finalizer')
 require(tail(old,FACTORS+['norm_linear'])==add(mul(product,atom('norm_linear')),const(1),-1),'entire parent product finalizer')
 return dict(unchanged_rows=len(common)-2,retained_expression_identities=len(retained),removed_rows=sorted(removed),new_rows=sorted(set(nd)-set(od)),retained_factors=7,all_factor_and_output_consumers_checked=True)

def algebra():
 c,f,R,T,K,j=[atom(n)for n in ('c','f','R','T','K','j')]
 o=add(mul(c,T),mul(R,f),-1)
 V=add(mul(c,add(mul(T,f),const(1),-1)),mul(R,power(f,2)),-1)
 require(add(mul(o,f),c,-1)==V,'exact auxiliary identity')
 Nk=add(K,R,-1);Nl=add(add(V,mul(j,c),-1),K)
 residual=add(add(V,R),mul(j,c),-1)
 require(add(Nl,Nk,-1)==residual,'cleared omitted factor correction')
 require(add(V,R)==add(mul(c,add(mul(T,f),const(1),-1)),mul(R,add(power(f,2),const(1),-1)),-1),'rational restoration numerator')
 product=atom('retained_product');parent=add(mul(product,Nl),const(1),-1);child=add(product,const(1),-1)
 require(add(add(parent,const(1)),mul(add(child,const(1)),Nk),-1)==mul(add(child,const(1)),residual),'whole ring correction including c=0')
 # Both exact degree cancellations are instances of this all-value identity.
 x,a,b,g,h=[atom(n)for n in ('X','a','c','gamma','H')]
 left=add(power(sum_polys([x,mul(a,b),g]),2),mul(add(power(a,2),h),power(b,2)),-1)
 z=add(x,g);right=add(mul(z,add(z,mul(const(2),mul(a,b)))),mul(h,power(b,2)),-1)
 require(left==right,'all-value main/input norm factorization')
 return dict(auxiliary_identity=True,cleared_full_correction=True,rational_correction_for_nonzero_c=True,norm_factorization_identity=True,unconditional_integer_j=False)

def numerical(old,new):
 rng=random.Random(860131);count=Counter()
 for case in range(48):
  values={n:rng.randrange(-4,6)for n in new['free']}
  if case>=32:values={n:Fraction(v,3)for n,v in values.items()}
  e=evaluate(new,values);c,f,R,T=(e[n]for n in ('R10a','f','r_lhs','auxiliary_quotient'))
  restore={n:values[n]for n in old['free']if n not in ('o','j')};restore.update(o=c*T-R*f,j=Fraction(case-7,3)if case>=32 else case-7)
  p=evaluate(old,restore)
  require(all(p[n]==e[n]for n in FACTORS),'numeric seven retained factors')
  require(p['polynomial']+1-(e['polynomial']+1)*e['norm_index']==(e['polynomial']+1)*(e['aux_u_rhs']+R-restore['j']*c),'whole ring correction evaluation')
  count['ring_corrections']+=1;count['retained_factor_values']+=7
  if case>=32:count['rational_ring_corrections']+=1
  if c:
   restore['j']=Fraction(e['aux_u_rhs']+R,c);p=evaluate(old,restore)
   require(p['polynomial']+1==(e['polynomial']+1)*e['norm_index'],'whole rational pullback')
   count['rational_pullbacks']+=1
  else:count['zero_c_ring_corrections']+=1
 v={n:1 for n in new['free']};v.update(Bm1=15,Kconstant=83,twice_cell_bits=2,inner_bits=3,MC=1,MF=16,f=2)
 e=evaluate(new,v);c=e['R10a'];j=Fraction(e['aux_u_rhs']+e['r_lhs'],c)
 require(j.denominator>1,'positive off-zero tuple has noninteger rational restoration')
 count['positive_offzero_nonintegral_boundary']=1
 return dict(counts=dict(count),offzero_boundary={'assignment':v,'c':c,'R':e['r_lhs'],'o':c-e['r_lhs']*v['f'],'j_numerator':j.numerator,'j_denominator':j.denominator,'not_a_zero_fixture':True})

def pell(A,n):
 d=A*A-1;u,v=1,0;b,c=A,1
 while n:
  if n&1:u,v=u*b+d*v*c,u*c+v*b
  b,c=b*b+d*c*c,2*b*c;n//=2
 return u,v

def components():
 residues=0
 for a in range(4):
  d=(a+2)**2-1
  for i in range(4):
   for c in range(4):
    for f in range(4):
     require(((i*c*c)**2-d*(f*f-1)+1)%4!=3,'ordinary strong sign exclusion');residues+=1
 aux=0
 for S in range(4):
  for V in range(4):
   for y in range(4):require((S*S*(V*V-y*y)+y*y)%4!=3,'square-coefficient auxiliary sign');aux+=1
 cases=[]
 for A,p in [(2,4),(2,5),(3,4)]:
  d=A*A-1;D,c=pell(A,p);require(c>A*d*d,'actual large-c fixture')
  for mult in (1,2):
   m=mult*p*c;f,psi=pell(A,m);require((d*psi)%(c*c)==0,'ordinary supplied i integral')
   i=d*psi//(c*c);require((i*c*c)**2==d*(f*f-1)and(f*f-1)%(c*c)==0,'ordinary strong and restored j divisibility')
   require(f*f>4*c*c and f*f>d+c,'strict ordinary size margins')
   for R in range(1,d):
    T=R*f+1;V=c*(T*f-1)-R*f*f;o=c*T-R*f
    require(((V+R)%c)==0,'on-component j integer');j=(V+R)//c
    require(o>0 and j>0 and (o*f-c)==V and (o+R*f)//c==T,'component inverse maps')
    require((i*c*c)**2-R*f*f-c>0,'ordinary auxiliary gap')
   cases.append(dict(A=A,p=p,c=c,m=m,f_bits=f.bit_length(),i_bits=i.bit_length(),tested_R=d-1))
 return dict(strong_residue_cases=residues,auxiliary_residue_cases=aux,ordinary_rank_arithmetic_fixtures=cases,scope='Finite local ordinary Pell/congruence/map checks only; not auxiliary norm or complete compiler zeros, and not a numerical proof of the general rank theorem.')

def verify(root):
 blobs=authenticate(root);parent=select_parent(blobs);packet=build(parent)
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=copy.deepcopy(PINS),parent_selection=dict(file='complete86_transport_quotient_shear.json',normalized=False,parent_ledger=ledger(parent),parent_exact_degree=134),packet=packet,source_proof=graph_proof(parent,packet),identities=algebra(),degree=degree(packet),numerical=numerical(parent,packet),components=components(),scope='One complete ordinary-strong source, full paid product-minus-one finalizer and uniform degree131; positive-zero bijection proved in companion note under the complete inherited fixed-program recipe. No ancestor Python executed; no full native Pell zero materialized; rational off-zero pullback does not assert integral or positive restoration.')

def main():
 if not __debug__:raise RuntimeError('Run without optimized Python')
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:require(same(r,json.loads(a.expect.read_text())),'type-exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status='PASS',ledger=r['packet']['ledger'],degree=r['degree'],source_proof=r['source_proof'],numerical=r['numerical']['counts'])))
if __name__=='__main__':main()
