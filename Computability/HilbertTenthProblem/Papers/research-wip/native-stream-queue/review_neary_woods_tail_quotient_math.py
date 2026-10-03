#!/usr/bin/env python3
"""Independent U9 tail-offset bootstrap challenge, using frozen actual parent sources."""
import argparse,hashlib,json,random
from pathlib import Path
from fractions import Fraction
from collections import Counter
from itertools import product
if not __debug__:raise RuntimeError('run without -O')
PINS={'neary_woods_universal_product_scale253.py': 'eb3e8f41f79f69199bd7b620a2b8908e60915b3976898def9d59c25d92a4675e', 'neary_woods_universal_product_scale253.json': 'a32b58aee2baf3d6d1a66489784f9cc9f5ab2bac296b9a7eb0a116785a3eef1b', 'neary_woods_universal_product_scale253.md': '9b3b0566dd1365d9acf4b97b6b290b951d56eb51392e85e48f06f83b1604434f', 'neary_woods_universal_history_scale257.md': 'dcc467b4b00a013c315856a271307459b694b69d4bd2a66c925312a042247e42', 'neary_woods_universal_initial_bound254.md': '9e1a0fd5559dc72420a5123eb4f67753576f7b06d93aff6b7b650cd40dba1f90', 'neary_woods_universal_native_bound254.md': '93b723d6cbbe42e07a9e57979105cffa08f332f4e8d028e5b0aa34890e189952', 'neary_woods_universal_history_units260.md': '73d3787dcc10acc037f80699ec3f8bde1fb721613abac5ce489762aab339057c', 'neary_woods_universal_joint_and_coupled.md': '02333114dd0cc4396d0a82098e71fde02cc76654c5b5751041f1237732d77868', 'neary_woods_universal_mask_unit263.md': '74591b51fb6df498d49523f843a091484fd634de7693946c759d3cd1da9ff47b', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', 'review_group_projective_tail_quotient_math.py': 'e67d778f87df88660c62cff64c1069fa96ee44756421715c2099a3f44a98e805', 'review_group_projective_tail_quotient_math.json': 'd9b908590135ed29975f176f169257c6c55d99a9fa9196b7613870e28a02c3f7', 'review_group_projective_tail_quotient_math.md': 'f03c7b1c82583d0ae093c6c4cf10c9da9f44a92863b88613b773d335137b677d', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b

def plus(a,b,sgn=1):
 r=dict(a)
 for k,v in b.items():r[k]=r.get(k,0)+sgn*v
 return {k:v for k,v in r.items()if v}
def mul(a,b):
 r={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(x+y for x,y in zip(m,n));r[k]=r.get(k,0)+v*w
 return {k:v for k,v in r.items()if v}
def ring(n):
 return lambda v:({(0,)*n:v}if v else{}),lambda i:{tuple(int(i==j)for j in range(n)):1}

def algebra():
 C,V=ring(4);D,T,f,y=map(V,range(4));f2=mul(f,f);t2=mul(T,T);Ns=plus(f2,mul(D,t2),-1);oldT=mul(D,T)
 residual=plus(mul(oldT,oldT),mul(D,plus(f2,C(1),-1)),-1)
 need(residual==mul(C(-1),mul(D,plus(Ns,C(1),-1))),'normalized strong residual identity')
 need(mul(D,mul(D,t2))==mul(oldT,oldT),'literal normalized auxiliary coefficient')
 C,V=ring(5);q,S,Z,beta,A=map(V,range(5));beta_old=plus(plus(beta,Z),S,-1)
 need(mul(q,plus(S,beta_old))==mul(q,plus(Z,beta)),'full quotient substitution identity')
 # Independent index factorization with A denoting the already folded A+1.
 C,V=ring(4);q,A,B,Z=map(V,range(4));one=C(1);f1=plus(plus(A,one,-1),Z,-1);f2=plus(B,Z,-1);f0=plus(plus(plus(plus(q,f1,-1),f2,-1),Z,-1),one,-1)
 packed=plus(f0,mul(q,plus(f1,mul(q,plus(f2,mul(q,Z))))))
 qm=plus(q,one,-1);S=plus(A,mul(plus(q,one),plus(B,mul(qm,Z))))
 need(packed==mul(qm,S),'folded source native index')
 return 4

def fixed(v):return type(v)is dict and set(v)=={'fixed_numeral'}and type(v['fixed_numeral'])is str
def execute(rows,v,numerals):
 e=dict(v)
 for n,o,a,b in rows:
  a=a if type(a)is int else numerals[a['fixed_numeral']]if fixed(a)else e[a];b=b if type(b)is int else numerals[b['fixed_numeral']]if fixed(b)else e[b];e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def ancestors(rows,ports):
 d={n:(a,b)for n,o,a,b in rows};s=set();todo=list(ports)
 while todo:
  n=todo.pop()
  if type(n)is str and n not in s:
   s.add(n)
   if n in d:todo.extend(d[n])
 return s

def finalizer(rows,out,factors,ordinary):
 C,V=ring(len(factors)+len(ordinary));e={f:V(i)for i,f in enumerate(factors)}
 for n,o,a,b in rows:
  if n in factors:continue
  if o=='-'and[a,b]in ordinary:e[n]=V(len(factors)+ordinary.index([a,b]));continue
  if not all(type(v)is int or type(v)is str and v in e for v in(a,b)):continue
  aa=C(a)if type(a)is int else e[a];bb=C(b)if type(b)is int else e[b];e[n]=mul(aa,bb)if o=='*'else plus(aa,bb,1 if o=='+'else-1)
 p=C(1)
 for i in range(len(factors)):p=mul(p,V(i))
 s=C(1)
 for i in range(len(ordinary)):r=V(len(factors)+i);s=plus(s,mul(r,r))
 need(out in e and e[out]==plus(mul(p,s),C(1),-1),'whole product-times-positive-SOS source')


def source_checks(data):
 count=Counter();records=[];rng=random.Random(734901)
 need(len(data['canonical_sources'])==16,'all actual current parent contexts')
 for index,p in enumerate(data['canonical_sources']):
  rows=p['source'];d={n:(o,a,b)for n,o,a,b in rows};free=p['parameters']+p['auxiliaries'];norm='and__'in p['ledger']['normalized_prefixes'];need('and__'in p['ledger']['positive_scale_prefixes'],'actual supported joint positive-scale source')
  req={'and__bs_X_bound':('+','factored_pack_inner','and__bound_beta'),'and__wn2':('*','and__bs_X_bound','and__q'),
   'factored_pack_q_minus_one':('-','and__q',1),'factored_pack_q_plus_one':('+','and__q',1),'factored_pack_Z':('*','factored_pack_q_minus_one','and__F3'),
   'factored_pack_B':('+','and__padded_B','factored_pack_Z'),'factored_pack_scaled_B':('*','factored_pack_q_plus_one','factored_pack_B'),
   'factored_pack_inner':('+','factored_pack_A_plus_one','factored_pack_scaled_B'),'and__bs_packed':('*','factored_pack_q_minus_one','factored_pack_inner'),
   'and__q':('*','fusion_low_q','hist__top_history__87'),'and__F3':('+','fusion_low_F3','fusion_high_Z'),
   'and__bs_even':('*',2,'and__odd_half'),'and__bs_odd':('+','and__bs_even',1),'and__sn2':('*','and__bs_odd','and__q'),
   'and__R10b':('+','and__eta','and__zeta'),'and__ic2':('*','and__i','and__c2'),'and__ic22':('*','and__ic2','and__ic2'),
   'and__L16':('*','and__f','and__f'),'and__L17':('*','and__R16','and__aux_square_gap'),'and__P17':('+','and__L17','and__aux_y2')}
  need(all(d[k]==v for k,v in req.items()),'actual bounds/odd multiplier/strong and auxiliary cone')
  ordinary=[[a,b]for n,o,a,b in rows if n.startswith('loader_residual_')]
  factors=list(p['ledger']['degree']['factor_degree_bounds']);finalizer(rows,p['output'],factors,ordinary)
  if norm:
   need(d['and__normalized_strong_Q']==('*','and__A','and__ic22')and d['and__f_square_minus_one']==('-','and__L16','and__normalized_strong_Q')and d['and__R16']==('*','and__A','and__normalized_strong_Q'),'actual normalized variant')
   need('and__f_square_minus_one'in factors,'normalized norm is an actual unit factor');count['normalized_joint_sources']+=1
  else:
   need(d['and__f_square_minus_one']==('-','and__L16',1)and d['and__R16']==('*','and__A','and__f_square_minus_one'),'actual ordinary variant')
   need(['and__ic22','and__R16']in ordinary,'ordinary strong equation really squared in full output');count['ordinary_joint_sources']+=1
  need([n for n,o,a,b in rows if 'and__bound_beta'in(a,b)]==['and__bs_X_bound'],'only private witness consumer')
  offsets=ancestors(rows,['factored_pack_inner','factored_pack_Z']);need('and__bound_beta'not in offsets,'offset independence')
  child=[[n,o,'factored_pack_Z',b]if n=='and__bs_X_bound'else[n,o,a,b]for n,o,a,b in rows]
  nodes=set(d);ready=set(free);numeral_names=sorted({v['fixed_numeral']for n,o,a,b in rows for v in(a,b)if fixed(v)})
  for n,o,a,b in child:need(n not in ready and all(type(v)is int or fixed(v)or type(v)is str and v in ready for v in(a,b)),'closed complete changed source');ready.add(n)
  need(ancestors(child,[p['output']])==nodes|set(free),'all complete paid and free ports remain live')
  cc=Counter('M'if o=='*'else'A'for n,o,a,b in child);oldledger=p['ledger']['polynomial']
  need((len(child),cc['M'],cc['A'])==(oldledger['operations'],oldledger['multiplications'],oldledger['additions_subtractions']),'unchanged complete count')
  for k in range(4):
   v={n:rng.randrange(-2,4)for n in free}
   if k==3:v={n:Fraction(x,2)for n,x in v.items()};count['rational_cases']+=1
   numerals={n:rng.randrange(-2,4)for n in numeral_names};now=execute(child,v,numerals);oldv=dict(v);oldv['and__bound_beta']+=now['factored_pack_Z']-now['factored_pack_inner'];prior=execute(rows,oldv,numerals)
   need(all(now[n]==prior[n]for n in nodes),'all computed registers in whole signed pullback')
   count['whole_source_cases']+=1;count['computed_register_equalities']+=len(rows)
  ones={n:1 for n in free};off=execute(child,ones,{n:1 for n in numeral_names});oldbeta=1+off['factored_pack_Z']-off['factored_pack_inner']
  need(oldbeta<0 and off[p['output']]!=0,'positive offzero need not restore positive beta');count['offzero_negative_inverse_cases']+=1
  records.append({'saved_parent_index':index,'joint_strong':'normalized'if norm else'ordinary','normalized_prefixes':p['ledger']['normalized_prefixes'],'positive_scale_prefixes':p['ledger']['positive_scale_prefixes'],'bound_is_program_E':p['ledger']['bound_is_program_E'],'operations':len(rows),'M':cc['M'],'A':cc['A'],'witnesses':len(p['auxiliaries']),'ordinary_residuals':len(ordinary),'factor_count':len(factors),'named_fixed_numerals':numeral_names,'changed_source_sha256':sha(stable(child).encode())})
 count['source_contexts']=len(records)
 return dict(count),records

def bounds():
 cases=0
 for b in (32,64):
  for P in (b-2,b+1):
   T=P**9
   for q0 in (16,32,48):
    lows=[sorted({res,res+16*((q0-1-res)//16)})for res in(12,10,8)]
    for a0,b0,z0 in product(*lows):
     for H0,M0,Z in product((0,T-1),repeat=3):
      H=H0+2*T;M=M0+T;q=q0*b*T;A=a0+q0*H;B=b0+q0*M;F3=z0+q0*Z;fs=[q-A-B+F3-1,A-F3,B-F3,F3]
      need(min(fs)>0 and max(fs)<q and sum(fs)==q-1 and [x%16 for x in fs]==[1,4,2,8],'actual low/high product-scale margins')
      S=A+1+(q+1)*(B+(q-1)*F3);r=sum(v*q**i for i,v in enumerate(fs));need(r==(q-1)*S and r<q**3*(F3+1),'packed source scalar bounds')
      X=q*(1+(q-1)*F3);E=X*3*q;need(E>2*r+3 and q*q*((q-3)*F3-2*q)>=18432,'tail offset E margin before typing')
      need(S>(q-1)*F3 and q<r-2,'embedding and both shifted index ranges');cases+=1
 mods=0
 for A,T,f in product(range(4),repeat=3):
  D=A*A-1;ns=f*f-D*T*T;need(ns%4!=3,'normalized norm cannot minus one');mods+=1
 return {'low_high_pretyping_boundaries':cases,'normalized_mod4_cases':mods}

def verify(root):
 blobs={}
 for n,h in PINS.items():blobs[n]=(root/n).read_bytes();need(sha(blobs[n])==h,'pin '+n)
 data=json.loads(blobs['neary_woods_universal_product_scale253.json']);counts,forms=source_checks(data)
 return {'status':'PASS_BOUNDED_U9_TAIL_BOOTSTRAP_MATH','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'exact_local_ring_identities':algebra(),'counts':counts,'source_contexts':forms,'finite_boundaries':bounds(),'scope':'Independent pretyping, normalized/ordinary lemma conversion and both-index-sign positive-zero proof; all16 actual frozen parent layouts receive a bounded local recipe check. No maintained child API, new degree claim, historical builder/suite or materialized complete Pell zero.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.root);t=json.dumps(r,sort_keys=True,indent=2)+'\n';need(same(r,json.loads(t)),'exact JSON roundtrip')
 if a.output:a.output.write_text(t)
 else:need(same(r,json.loads(a.expect.read_text())),'fresh exact receipt')
 print(r['status'],r['counts'],r['finite_boundaries'])
