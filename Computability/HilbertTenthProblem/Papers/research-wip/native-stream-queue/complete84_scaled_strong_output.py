#!/usr/bin/env python3
"""Complete84 = Delta*complete85; pinned JSON only, no predecessor execution."""
import argparse
from collections import Counter
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path

PINS={
 'complete85_auxiliary_bezout_projection.py':'3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0',
 'complete85_auxiliary_bezout_projection.json':'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc',
 'complete85_auxiliary_bezout_projection.md':'d8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b',
 'review_complete85_auxiliary_bezout_source.py':'8c3095f10067bfd5bebfd86914698add2871f8b3b5b4005d284db6840a4eda69',
 'review_complete85_auxiliary_bezout_source.json':'6d746da58a1a0bc116db453bad4767f50fe8841485abb7c0bc29b650ac3f635c',
 'review_complete85_auxiliary_bezout_source.md':'d8e8720f5287ef1069ce46f52369c532fb551d9611935065aa56210295ab2cd9',
 'review_complete85_auxiliary_bezout_math.py':'ea1c7d39b2afc6c1a004facac777b6ad97af89c5c92309e489439928abcbdd65',
 'review_complete85_auxiliary_bezout_math.json':'9cdbf027fe1da74975043f4c5ba022b04e0e73eb92166cf2a1ed2ec1cc258d49',
 'review_complete85_auxiliary_bezout_math.md':'77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
}
OLD=[['ic2','*','i','c2'],['ic22','*','ic2','ic2'],['strong_difference','*','A','ic22'],['R16','*','A','strong_difference'],['norm_strong','-','L16','strong_difference']]
NEW=[['aux_coefficient_root','*','i','Ac2'],['R16','*','aux_coefficient_root','aux_coefficient_root'],['scaled_f_square','*','A','L16'],['norm_strong','-','scaled_f_square','R16']]
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
FINAL=[['norm_pair','*','norm_first','norm_main'],['norm_triple','*','norm_pair','norm_input'],['norm_four','*','norm_triple','norm_aux'],['norm_product','*','norm_four','norm_index'],['all_units','*','norm_product','norm_transport'],['seven_units','*','all_units','norm_strong']]

def require(ok,msg):
 if not ok:raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def typed_equal(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(typed_equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(typed_equal(x,y) for x,y in zip(a,b))
 return a==b

def schedule(rows,free,output):
 table={r[0]:r for r in rows};require(len(table)==len(rows),'duplicate register');require(not(set(table)&set(free)),'free collision')
 live=set()
 def visit(n):
  if not isinstance(n,str) or n in free:return
  require(n in table,'undefined register '+n)
  if n in live:return
  live.add(n);visit(table[n][2]);visit(table[n][3])
 visit(output);require(live==set(table),'dead gate')
 out=[];done=set(free)
 while len(out)<len(rows):
  size=len(out)
  for row in rows:
   n,op,a,b=row;require(op in ('*','+','-'),'bad opcode')
   if n not in done and all(not isinstance(x,str) or x in done for x in (a,b)):out.append(row);done.add(n)
  require(len(out)>size,'cycle')
 require({x for r in rows for x in r[2:] if isinstance(x,str)}&set(free)==set(free),'unused free port')
 return out

def evaluate(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
  e[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return e

def build(parent):
 table={r[0]:r for r in parent['source']}
 premises=[['c2','*','R10a','R10a'],['Ac2','*','A','c2'],['L16','*','f','f'],['wn2','*','w','q'],['sn2','*','s','n2'],['n2','*','Lbig','q'],['Lbig','*','q','q'],['UM','*','wn2','sn2'],['R12','+','UM','sn2'],['a_square','*','R12','R12'],['a4','*',4,'R12'],['a4m5','+','a4',3],['A','+','a_square','a4m5'],['q','+','repunit',1],['repunit','*','Bm1','Jrep']]
 require(all(table.get(r[0])==r for r in OLD+FINAL+premises),'literal parent premise')
 require(table['polynomial']==['polynomial','-','seven_units',1],'parent output')
 require(parent['normalized'] is True and len(parent['source'])==85 and parent['exact_degree']==175,'parent mode')
 require(parent['factor_exact_degrees']==[22,18,32,60,7,2,34],'parent exact degrees')
 require(len(parent['witnesses'])==18 and parent['ordinary_input']=='x','ordinary interface')
 oldnames={r[0] for r in OLD}
 for r in parent['source']:
  if r[0] not in oldnames:require(not(any(x in {'ic2','ic22','strong_difference'} for x in r[2:])),'private producer consumer')
 require([r[0] for r in parent['source'] if 'norm_strong' in r[2:]]==['seven_units'],'strong factor consumer')
 rows=[copy.deepcopy(r) for r in parent['source'] if r[0] not in oldnames and r[0]!='polynomial']+copy.deepcopy(NEW)+[['polynomial','-','seven_units','A']]
 rows=schedule(rows,parent['free'],'polynomial')
 retained={r[0]:r for r in rows if r[0] not in {x[0] for x in NEW} and r[0]!='polynomial'}
 require(len(retained)==79 and all(table[n]==r for n,r in retained.items()),'retained literal definitions')
 counts=Counter(r[1] for r in rows);require(len(rows)==84 and counts['*']==47 and counts['+']+counts['-']==37,'ledger')
 p={k:copy.deepcopy(parent[k]) for k in ('free','fixed_numerals','ordinary_input','witnesses')}
 p.update({'source':rows,'output':'polynomial','normalized':True,'witness_domain':'strictly positive integers','factors':FACTORS,'factor_values_at_positive_zeros':[1,1,1,1,1,1,'A'],'ledger':{'M':47,'A':37,'total':84,'core_M':41,'core_A':36,'core_total':77,'finalizer_M':6,'finalizer_A':1,'finalizer_total':7},'exact_degree':187,'factor_exact_degrees':[22,18,32,60,7,2,46],'full_polynomial_identity':False,'all_ring_relation':'F84=A*F85 on the identical supplied coordinates','same_positive_zero_tuples':True,'unrestricted_signed_zero_equivalence':False,'coordinate_map':'identity','scope':'Complete ordinary universal polynomial on the unchanged valid fixed-program recipe; no global circuit optimality claim.'})
 return p

N=8;ZERO=(0,)*N
def con(v):return {} if not v else {ZERO:v}
def var(k):return {tuple(int(j==k) for j in range(N)):1}
def add(a,b,sgn=1):
 o=dict(a)
 for m,c in b.items():
  o[m]=o.get(m,0)+sgn*c
  if not o[m]:del o[m]
 return o
def mul(a,b):
 o={}
 for x,c in a.items():
  for y,d in b.items():
   z=tuple(i+j for i,j in zip(x,y));o[z]=o.get(z,0)+c*d
 return {m:c for m,c in o.items() if c}
def local_proof():
 D,c,i,f=[var(j) for j in range(4)];c2=mul(c,c);Ac2=mul(D,c2);t=mul(i,c2);Q=mul(D,mul(t,t));K=mul(D,Q);Ns=add(mul(f,f),Q,-1);S=mul(i,Ac2);Knew=mul(S,S);scaled=add(mul(D,mul(f,f)),Knew,-1)
 require(Knew==K,'aux coefficient identity');require(scaled==mul(D,Ns),'scaled strong identity')
 atoms={name:var(k) for k,name in enumerate(FACTORS)};Delta=var(7)
 def final(scaled_form):
  env=dict(atoms)
  if scaled_form:env['norm_strong']=mul(Delta,env['norm_strong'])
  for n,op,a,b in FINAL:env[n]=mul(env[a],env[b])
  return add(env['seven_units'],Delta if scaled_form else con(1),-1)
 require(final(True)==mul(Delta,final(False)),'entire finalizer identity')
 return {'local_coefficient_identities':2,'whole_seven_factor_finalizer_identity':True,'retained_literal_rows':79,'relation':'F84=Delta*F85 over every commutative ring','positivity_used_for_identity':False}

def uni_add(a,b,prime,sgn=1):
 o=[0]*max(len(a),len(b))
 for j,x in enumerate(a):o[j]=x
 for j,x in enumerate(b):o[j]=(o[j]+sgn*x)%prime
 while len(o)>1 and o[-1]==0:o.pop()
 return o
def uni_mul(a,b,prime):
 o=[0]*(len(a)+len(b)-1)
 for j,x in enumerate(a):
  for k,y in enumerate(b):o[j+k]=(o[j+k]+x*y)%prime
 while len(o)>1 and o[-1]==0:o.pop()
 return o
def uni_eval(rows,values,prime):
 e=copy.deepcopy(values)
 for n,op,a,b in rows:
  a=e[a] if isinstance(a,str) else [a%prime];b=e[b] if isinstance(b,str) else [b%prime]
  e[n]=uni_mul(a,b,prime) if op=='*' else uni_add(a,b,prime,1 if op=='+' else -1)
 return e

def degree_check(parent,child):
 deg={x:0 if x in child['fixed_numerals'] else 1 for x in child['free']}
 for n,op,a,b in child['source']:
  a=deg[a] if isinstance(a,str) else 0;b=deg[b] if isinstance(b,str) else 0
  deg[n]=a+b if op=='*' else max(a,b)
 require(deg['A']==12 and deg['polynomial']==197,'literal upper degree')
 diagnostics=[]
 for B,prime in [(16,1000000007),(32,1000000009)]:
  numerals={'Bm1':B-1,'Kconstant':3,'twice_cell_bits':2,'inner_bits':1,'MC':5,'MF':7}
  values={x:[numerals[x]] if x in numerals else [0,1] for x in child['free']}
  a=uni_eval(parent['source'],values,prime);b=uni_eval(child['source'],values,prime)
  require(b['polynomial']==uni_mul(b['A'],a['polynomial'],prime),'entire coefficient multiplier identity')
  require(len(a['polynomial'])==176 and len(b['polynomial'])==188,'attained diagnostics')
  require([len(b[x])-1 for x in FACTORS]==[22,18,32,60,7,2,46],'diagnostic factor degrees')
  # Q=(B−1)t, k=2t, gamma=2t, and Ttransport=−5t² here.
  leading=(-32*2*(2**13)*5*pow(B-1,111,prime))%prime
  require(b['polynomial'][-1]==leading,'uniform leader specialization')
  diagnostics.append({'B':B,'prime':prime,'degree':187,'coefficient_sha256':sha(json.dumps(b['polynomial'],separators=(',',':')).encode()),'leading_coefficient':leading,'scope':'Full-source diagnostic coefficients; these numeral samples are not the uniform compiler-slice proof.'})
 return {'exact_degree':187,'gate_upper_degree':197,'Delta_degree':12,'uniform_leader':'32*Q^111*h*(rho+sigma)*delta^2*i^4*(eta+zeta)^13*w^18*s^31*Ttransport*T^2*f^2','nonzero_monomial':'Jrep^112*h*rho*delta^2*i^4*eta^13*w^18*s^31*transport_quotient*auxiliary_quotient^2*f^2','nonzero_coefficient':'-32*Bm1^112','proof':'Multiply the pinned parent uniform degree175 leader by Delta_top=w^2*s^2*Q^8; Bm1>0 on every inherited valid compiler slice. All supplied witnesses and x have degree1, fixed compiler numerals degree0.','diagnostics':diagnostics}

def verify(root):
 for name,pin in PINS.items():require(sha((root/name).read_bytes())==pin,'pin '+name)
 data=json.loads((root/'complete85_auxiliary_bezout_projection.json').read_text())
 inherited=data['parent_pins'];require(len(inherited)==12,'inherited pin inventory')
 for name,pin in inherited.items():require(sha((root/name).read_bytes())==pin,'inherited pin '+name)
 parent=data['packet'];child=build(parent);proof=local_proof();degree=degree_check(parent,child)
 samevalues=0
 for case in range(64):
  values={x:Fraction(((case+2)*(j+3))%19-9,1 if case<32 else j%3+1) for j,x in enumerate(parent['free'])}
  a=evaluate(parent['source'],values);b=evaluate(child['source'],values)
  require(b['polynomial']==b['A']*a['polynomial'],'whole numeric multiplier')
  require(b['R16']==a['R16'] and b['norm_strong']==a['A']*a['norm_strong'],'numeric cuts')
  for n in set(a)&set(b)-{'norm_strong','seven_units','polynomial'}:require(a[n]==b[n],'retained value '+n);samevalues+=1
 # Exact signed boundary: A=0 creates zeros; no unrestricted signed claim.
 values={x:1 for x in parent['free']};values.update({'Jrep':0,'w':0,'s':-1,'twice_cell_bits':2})
 a=evaluate(parent['source'],values);b=evaluate(child['source'],values)
 require(b['A']==0 and b['polynomial']==0 and a['polynomial']!=0,'signed zero-multiplier boundary')
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':copy.deepcopy(PINS),'inherited_pins':copy.deepcopy(inherited),'packet':child,'structural':proof,'degree':degree,'numeric':{'whole_ring_evaluations':64,'rational_assignments':32,'retained_value_equalities':samevalues,'signed_boundary':{'values':values,'Delta':0,'parent_output':int(a['polynomial']),'child_output':0,'scope':'Off-domain arithmetic fixture; no valid positive/compiler zero claim.'}},'scope':'One complete84 source, all84 paid rows and one full output; no predecessor execution or new enormous native Pell witness.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args()
 require(not(args.output and args.expect),'choose output or expect')
 receipt=verify(args.root)
 if args.expect:require(typed_equal(receipt,json.loads(args.expect.read_text())),'receipt mismatch')
 if args.output:args.output.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':'PASS','gates':84,'M':47,'A':37,'witnesses':18,'exact_degree':187,'upper_degree':197}))
if __name__=='__main__':main()
