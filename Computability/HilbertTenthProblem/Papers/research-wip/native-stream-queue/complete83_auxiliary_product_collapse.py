#!/usr/bin/env python3
"""Fresh product-only deletion audit; pinned predecessors are inert data only."""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

PINS = {
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete82_auxiliary_square_product_chart.py':'5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc',
 'complete82_auxiliary_square_product_chart.json':'7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a',
 'complete82_auxiliary_square_product_chart.md':'10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9',
 'complete82_all_input_outer_collapse.py':'00894d55c070aa60897012e9e6bbd069e7ab567f5629dba9cf99a6c43f95a871',
 'complete82_all_input_outer_collapse.json':'53e801aa2e4f3f1a105e5fbca453de7829d11a7ace4c7d915526fbc108863e8a',
 'complete82_all_input_outer_collapse.md':'7c645a49f617bb628b203a3cda3117d459944b39e595b339734ec0ed7c390725',
 'review_complete82_all_input_outer_collapse_math.md':'60ac7ffbae4d39d04868ea077361615961582240c687adb8b5191ca3aee29085',
 'review_complete85_auxiliary_bezout_math.md':'77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
FACTOR_DEGREES=[22,18,32,58,7,2,46]
def need(ok,s):
 if not ok:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def load(b):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(s):raise ValueError('noninteger JSON number '+s)
 return json.loads(b,object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def evaluate(rows,v,operation=None):
 e=dict(v)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[n]=operation(op,a,b) if operation else a*b if op=='*' else a+b if op=='+' else a-b
 return e
def build(data):
 parent=load(data['complete84_scaled_strong_output.json'])['packet']
 old=load(data['complete82_auxiliary_square_product_chart.json'])['packet']
 outer=load(data['complete82_all_input_outer_collapse.json'])['packet']
 need(old['source']==outer['source'],'outer proof uses same82 source')
 rows=parent['source'];rm={r[0]:r for r in rows}
 need(rm['auxiliary_Tf']==['auxiliary_Tf','*','auxiliary_quotient','f'],'deleted producer')
 need([r[0] for r in rows if 'auxiliary_quotient' in r[2:]]==['auxiliary_Tf'],'private quotient')
 need([r[0] for r in rows if 'auxiliary_Tf' in r[2:]]==['auxiliary_Tf_minus_one'],'single product consumer')
 source=copy.deepcopy([r for r in rows if r[0]!='auxiliary_Tf'])
 for r in source:
  if r[0]=='auxiliary_Tf_minus_one':r[2]='auxiliary_product'
 rename=lambda v:'auxiliary_product' if v=='auxiliary_quotient' else v
 p={'source':source,'free':[rename(v) for v in parent['free']],'witnesses':[rename(v) for v in parent['witnesses']],
    'fixed_numerals':parent['fixed_numerals'],'ordinary_input':'x','output':'polynomial','witness_domain':'strictly positive integers',
    'factors':FACTORS,'factor_exact_degrees':FACTOR_DEGREES,'exact_degree':185,'universal_soundness':'REFUTED_ALL_POSITIVE_INPUTS',
    'factor_values_on_constructed_zeros':[1,1,1,1,1,1,'A']}
 known=set(p['free']);deg={v:0 if v in p['fixed_numerals'] else 1 for v in known};producers={}
 for n,op,a,b in source:
  need(n not in known and op in ['*','+','-'],'source producer')
  need(all(type(t)is int or t in known for t in [a,b]),'source closure')
  ds=[0 if type(t)is int else deg[t] for t in [a,b]];deg[n]=sum(ds) if op=='*' else max(ds)
  known.add(n);producers[n]=[a,b]
 todo=[p['output']];live=set()
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo+=producers.get(n,[])
 need(set(producers)<=live and set(p['free'])<=live,'full liveness')
 m=sum(r[1]=='*' for r in source);a=len(source)-m
 p['ledger']={'M':m,'A':a,'total':len(source),'core_M':m-6,'core_A':a-1,'core_total':len(source)-7,'finalizer_M':6,'finalizer_A':1,'finalizer_total':7}
 p['gate_upper_degree']=deg[p['output']]
 need((m,a,len(p['witnesses']),p['gate_upper_degree'])==(46,37,18,195),'full ledger/interface')
 expected_old=[r for r in source if r[0]!='L16']
 expected_old=[[n,op,'auxiliary_Tf' if a=='auxiliary_product' else a,b] for n,op,a,b in expected_old]
 need(expected_old==old['source'],'entire82 source under square substitution')
 return p,parent,old

def formal(p,parent,old):
 memo={}
 def intern(key):
  if key not in memo:memo[key]=len(memo)
  return memo[key]
 def atom(x):return intern(('constant' if type(x)is int else 'variable',x))
 def op(o,a,b):
  if o in ['*','+'] and a>b:a,b=b,a
  return intern((o,a,b))
 def run(packet,replacements):
  env={x:atom(x) for x in packet['free']};env.update(replacements)
  for n,o,a,b in packet['source']:env[n]=op(o,atom(a) if type(a)is int else env[a],atom(b) if type(b)is int else env[b])
  return env
 a=run(parent,{});b=run(p,{'auxiliary_product':op('*',atom('auxiliary_quotient'),atom('f'))})
 need(all(a[n]==b[n] for n,_,_,_ in p['source']),'every retained84 expression under U=T*f')
 c=run(p,{});d=run(old,{'L16':op('*',atom('f'),atom('f')),'auxiliary_Tf':atom('auxiliary_product')})
 need(all(c[n]==d[n] for n,_,_,_ in old['source']),'every82 expression under F_aux=f*f')
 return {'parent84_expression_identities':83,'chart82_expression_identities':82,'all_ring_pullbacks':['F83prod(U=T*f)=F84','F83prod(f,U)=F82(F_aux=f*f,U_aux=U)'],'method':'Induction through every source row with exact shared formal-expression interning, no sampled equality proof.'}

def numeric(p,parent,old):
 rng=random.Random(20261003);cases=72
 for j in range(cases):
  v={x:Fraction(rng.randrange(-3,5),rng.randrange(1,5)) if j>=48 else rng.randrange(-3,5) for x in parent['free']}
  a=evaluate(parent['source'],v);v['auxiliary_product']=v['auxiliary_quotient']*v['f'];b=evaluate(p['source'],v)
  need(a['polynomial']==b['polynomial'],'numeric parent pullback')
  v['auxiliary_product']=Fraction(j-31,1+j%4);b=evaluate(p['source'],v)
  v['L16']=v['f']**2;v['auxiliary_Tf']=v['auxiliary_product'];c=evaluate(old['source'],v)
  need(b['polynomial']==c['polynomial'],'numeric chart pullback')
 return {'signed_assignments':48,'rational_assignments':24,'whole_output_equalities':2*cases,'scope':'Off-zero algebra checks, not compiler histories.'}

def dense(p,parent,old):
 receipts=[]
 for modulus,bm1 in [(1000003,15),(1000033,31)]:
  def op(o,a,b):
   a=[a] if type(a)is int else a;b=[b] if type(b)is int else b
   c=[0]*(len(a)+len(b)-1 if o=='*' else max(len(a),len(b)))
   if o=='*':
    for i,x in enumerate(a):
     for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%modulus
   else:
    for i,x in enumerate(a):c[i]=(c[i]+x)%modulus
    for i,x in enumerate(b):c[i]=(c[i]+(-x if o=='-' else x))%modulus
   while len(c)>1 and c[-1]==0:c.pop()
   return c
  fixed=dict(zip(p['fixed_numerals'],[bm1,7,8,5,2,19]))
  v={x:[fixed[x]] if x in fixed else [0,1] for x in p['free']}
  b=evaluate(p['source'],v,op);ds=[len(b[n])-1 for n in FACTORS]
  need(ds==FACTOR_DEGREES and len(b['polynomial'])==186,'dense exact degrees')
  v['L16']=op('*',v['f'],v['f']);v['auxiliary_Tf']=v['auxiliary_product'];c=evaluate(old['source'],v,op)
  need(b['polynomial']==c['polynomial'],'dense82 pullback')
  v['auxiliary_quotient']=[0,1];v['auxiliary_product']=op('*',v['auxiliary_quotient'],v['f'])
  b=evaluate(p['source'],v,op);a=evaluate(parent['source'],v,op)
  need(a['polynomial']==b['polynomial'],'dense84 pullback')
  receipts.append({'modulus':modulus,'diagnostic_numerals':fixed,'factor_degrees':ds,'candidate_degree':185,'parent_pullback_degree':len(a['polynomial'])-1})
 return {'full_source_coefficient_diagnostics':receipts,'uniform_degree_proof':'See companion leading-form proof; diagnostic numeral tuples are not asserted to be authentic compiler instances.'}

def pell(A,n):
 D=A*A-1
 def mul(a,b):return (a[0]*b[0]+D*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
 r=(1,0);b=(A,1)
 while n:
  if n%2:r=mul(r,b)
  n//=2
  if n:b=mul(b,b)
 return r
def aux_checks(p):
 cases=[]
 for A,index,Rs in [(2,3,range(1,6)),(3,3,range(1,6)),(5,3,[3,7]),(2,5,[3,7])]:
  Delta=A*A-1;D,c=pell(A,index);m=2*c*index;f,z=pell(A,m)
  need(c%2==1 and z%(c*c)==0,'positive c-square rank');i=z//(c*c);S=Delta*z
  for R in Rs:
   v=next(v for v in range(3,4*c+1,4) if (v-R)%c==0)
   numerator,y=pell(S,v);need(numerator%S==0,'odd Pell quotient');V=numerator//S
   need((V+R)%c==0 and (f*f-1)%c==0,'CRT integrality')
   need((V+R*f*f)%c==0,'product coordinate integrality');U=1+(V+R*f*f)//c
   need(min(f,i,U,y)>0 and V==c*(U-1)-R*f*f,'positive literal product')
   values={'f':f,'i':i,'auxiliary_product':U,'y_aux':y,'A':Delta,'R10a':c,'r_lhs':R,'Ac2':Delta*c*c,'aux_y2':y*y}
   source=p['source'];start=next(j for j,r in enumerate(source) if r[0]=='L16');end=next(j for j,r in enumerate(source) if r[0]=='norm_aux')+1
   e=evaluate(source[start:end],values)
   need(e['norm_strong']==Delta and e['norm_aux']==1,'literal compiled auxiliary factors')
   ub=U.to_bytes((U.bit_length()+7)//8,'big')
   cases.append({'Pell_parameter':A,'main_index':index,'c':c,'R':R,'strong_index':m,'auxiliary_index':v,'f_bits':f.bit_length(),'U_bits':U.bit_length(),'U_sha256_unsigned_big_endian':sha(ub),'f_divides_U':U%f==0,'literal_norm_strong':'Delta','literal_norm_aux':1})
 mod4=0
 for D in [0,3]:
  for c in range(4):
   for i in range(4):
    for f in range(4):
     for V in range(4):
      for y in range(4):
       S=i*D*c*c;na=S*S*(V*V-y*y)+y*y;ns=f*f-D*i*i*c**4
       need(na%4!=3 and ns%4!=3,'negative unit excluded');mod4+=1
 return {'positive_auxiliary_extensions':cases,'negative_unit_residue_cases':mod4,'scope':'Exact finite auxiliary components only. All-input full zeros are proved by the inherited outer construction and the new uniform extension, not by these examples.'}
def run(root):
 data={}
 for n,h in PINS.items():
  b=(root/n).read_bytes();need(sha(b)==h,'pin '+n);data[n]=b
 p,parent,old=build(data)
 return {'status':'PASS_REFUTED_ALL_INPUTS','source_sha256':sha(Path(__file__).read_bytes()),'dependency_pins':PINS,'predecessor_code_executed':False,'packet':p,'structural':formal(p,parent,old),'numeric':numeric(p,parent,old),'degree':dense(p,parent,old),'auxiliary':aux_checks(p),'theorem':'Every positive input has infinitely many full positive zeros on every inherited authentic compiler slice. Retaining f*f alone does not repair the square/product relaxation. No new universal bound.'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.root.resolve());s=json.dumps(r,indent=2,sort_keys=True)+'\n'
 if a.expect:need(a.expect.read_text()==s,'exact receipt replay')
 else:
  with a.output.open('x') as f:f.write(s)
 print(json.dumps({'status':r['status'],'ledger':r['packet']['ledger'],'exact_degree':185,'positive_auxiliary_checks':len(r['auxiliary']['positive_auxiliary_extensions'])}))
if __name__=='__main__':main()
