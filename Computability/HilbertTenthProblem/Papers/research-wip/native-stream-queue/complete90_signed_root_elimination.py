"""Fresh complete90 signed-root elimination; predecessors are authenticated inert data.
Standard library only. Universality uses the pinned reviewed signed-T positivity theorem.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete84_rational_root_scout.py':'7d7766f6536be28a3819d1764a4fbb31f70ce91f47a313fd22d57384787cde06',
 'complete84_rational_root_scout.json':'ab7e0a11e9cc04b961085a2dae6b94eff43761c155cdae2ace4a4b29a29348c2',
 'complete84_rational_root_scout.md':'18d60bed0230423e9093d021934ddafe9c4e40f2d01a13ffe71b85945a82ab0a',
 'complete84_signed_quotient_soundness_scout.md':'b2f1c37ebf68216e657006acaebbac0b27faedb325e1603983786085d580f44a',
 'complete84_signed_quotient_soundness_scout.json':'0e31841fce2a8db87c930c8f5fcfeeab3e3761547897c218d2c964e1dab906cf',
 'review_complete84_signed_quotient_soundness.md':'e392d0c0c904d64a007234ec2a2759921ac6bbb1f2ca058539c15dd6705486f8',
 'review_complete84_signed_quotient_soundness.json':'2551ffd6511d2e39254bed4c2f44ec270e71123ea5485389176cff37c59205a9',
}
APPEND=[
 ['er_ic2','*','i','c2'],['er_kS','*','er_ic2','aux_coefficient_root'],['er_D','+','er_kS',1],
 ['er_RD','*','r_lhs','er_D'],['er_b','+','R10a','er_RD'],['er_u','*','R10a','auxiliary_quotient'],
 ['er_u2','*','er_u','er_u'],['er_p','*','er_D','er_u2'],['er_b2','*','er_b','er_b'],
 ['er_P5a','*','norm_triple','norm_index'],['er_P5','*','er_P5a','norm_transport'],
 ['er_C','*','er_P5','R16'],['er_L','*','er_C','er_p'],['er_M','*','er_C','er_b2'],
 ['er_Pc','-','er_P5','er_C'],['er_Z','*','er_Pc','aux_y2'],['er_LM','+','er_L','er_M'],
 ['er_LMZ','+','er_LM','er_Z'],['er_alpha','-','er_LMZ',1],['er_alpha2','*','er_alpha','er_alpha'],
 ['er_prod','*','er_L','er_M'],['er_four','*',4,'er_prod'],['elimination_polynomial','-','er_alpha2','er_four'],
]

def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode()
def unique(pairs):
 out={}
 for k,v in pairs:
  need(k not in out,'duplicate JSON key');out[k]=v
 return out
def forbidden(s):raise ValueError('nonintegral/nonfinite JSON number: '+s)
def readjson(b):return json.loads(b,object_pairs_hook=unique,parse_float=forbidden,parse_constant=forbidden)
def typed_equal(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(typed_equal(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b) and all(typed_equal(x,y)for x,y in zip(a,b))
 return a==b

def cn(c):return {():c}if c else{}
def vr(n):return {(n,):1}
def plus(a,b,sign=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+sign*c
 return {m:c for m,c in out.items()if c}
def times(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items()if c}
def product(*args):
 p=cn(1)
 for a in args:p=times(p,a)
 return p
def power(a,n):
 p=cn(1)
 while n:
  if n%2:p=times(p,a)
  n//=2
  if n:a=times(a,a)
 return p
def encoded(p):return [[list(m),c]for m,c in sorted(p.items())]
def poly_record(p,full=False):
 e=encoded(p);r={'terms':len(e),'sha256':sha(canonical(e))}
 if full:r['coefficients']=e
 return r

def ledger(rows):
 c=Counter(r[1]for r in rows);return {'total':len(rows),'M':c['*'],'A':c['+']+c['-']}
def graph(rows,free,output):
 need(len(free)==len(set(free)),'duplicate supplied port');known=set(free);defs={}
 for row in rows:
  need(type(row)is list and len(row)==4,'row schema');n,o,a,b=row
  need(type(n)is str and n not in known and o in ('+','-','*'),'SSA or operation')
  need(all(type(x)is int or(type(x)is str and x in known)for x in(a,b)),'topological operands')
  defs[n]=row;known.add(n)
 reached=set();leaves=set();todo=[output]
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n in reached or n in leaves:continue
  if n in defs:reached.add(n);todo.extend(defs[n][2:])
  else:need(n in free,'unbound leaf');leaves.add(n)
 need(reached==set(defs),'dead paid row');need(leaves==set(free),'dead supplied port')
 return {'paid_rows_live':len(reached),'supplied_ports_live':len(leaves),'ledger':ledger(rows)}
def polys_at(rows,cuts,outputs):
 defs={r[0]:r for r in rows};memo=dict(cuts)
 def at(n):
  if type(n)is int:return cn(n)
  if n not in memo:
   need(n in defs,'unbound formal cut '+n);_,o,a,b=defs[n];a,b=at(a),at(b)
   memo[n]=times(a,b)if o=='*'else plus(a,b,1 if o=='+'else-1)
  return memo[n]
 return {n:at(n)for n in outputs}

def algebra(parent,child):
 Delta,c,R,i,T,y,f=map(vr,['Delta','c','R','i','T','y','f'])
 c2=power(c,2);S=product(Delta,i,c2);Q=power(S,2);D=plus(cn(1),product(Delta,power(i,2),power(c,4)))
 b=plus(c,product(R,D));u=product(c,T);P5=product(vr('Ntriple'),vr('Nindex'),vr('Ntransport'))
 E=plus(power(f,2),D,-1);V=plus(plus(product(c,T,f),c,-1),product(R,power(f,2)),-1)
 Na=plus(product(Q,plus(power(V,2),power(y,2),-1)),power(y,2));Ns=plus(product(Delta,power(f,2)),Q,-1)
 A=plus(plus(product(Q,plus(product(D,power(u,2)),power(b,2))),product(plus(Q,cn(1),-1),power(y,2)),-1),cn(1),-1)
 B=product(cn(2),Q,u,b);alpha=plus(product(P5,plus(A,cn(1))),cn(1),-1)
 resultant=plus(power(alpha,2),product(D,power(product(P5,B),2)),-1)
 cuts={'A':Delta,'R10a':c,'r_lhs':R,'i':i,'auxiliary_quotient':T,'y_aux':y,'f':f,
       'norm_triple':vr('Ntriple'),'norm_index':vr('Nindex'),'norm_transport':vr('Ntransport')}
 old=polys_at(parent,cuts,['c2','Ac2','aux_coefficient_root','R16','aux_u_rhs','norm_aux','norm_strong','polynomial'])
 for n,p in [('c2',c2),('Ac2',product(Delta,c2)),('aux_coefficient_root',S),('R16',Q),('aux_u_rhs',V),('norm_aux',Na),('norm_strong',Ns)]:need(old[n]==p,'actual parent binding '+n)
 need(old['polynomial']==plus(product(P5,Na,Ns),Delta,-1),'full parent finalizer')
 flipped={m:c*(-1)**(m.count('f')+m.count('T'))for m,c in old['polynomial'].items()}
 need(flipped==old['polynomial'],'entire parent simultaneous f,T sign symmetry')
 new=polys_at(child,cuts,['er_D','er_b','er_P5','er_C','er_L','er_M','er_Z','er_alpha','er_four','elimination_polynomial'])
 L=product(P5,Q,D,power(u,2));M=product(P5,Q,power(b,2));Z=product(P5,plus(cn(1),Q,-1),power(y,2))
 expected={'er_D':D,'er_b':b,'er_P5':P5,'er_C':product(P5,Q),'er_L':L,'er_M':M,'er_Z':Z,'er_alpha':alpha,
           'er_four':product(D,power(product(P5,B),2)),'elimination_polynomial':resultant}
 for n,p in expected.items():need(new[n]==p,'whole appended source identity '+n)
 rem=product(Q,plus(plus(power(u,2),product(cn(2),R,u,f),-1),plus(product(cn(2),R,b),product(power(R,2),E))))
 need(plus(Ns,Delta,-1)==product(Delta,E),'strong identity')
 need(plus(plus(Na,cn(1),-1),plus(A,product(B,f),-1),-1)==product(E,rem),'auxiliary E remainder')
 contracted=product(Delta,plus(product(P5,plus(plus(A,product(B,f),-1),cn(1))),cn(1),-1))
 need(plus(old['polynomial'],contracted,-1)==product(P5,Delta,E,plus(rem,Na)),'full E remainder')
 # The cancellation-safe six-term main/input norm is proved independently.
 X,a,z,g,H=map(vr,['X','a','z','g','H'])
 original=plus(power(plus(plus(X,product(a,z)),g),2),product(plus(power(a,2),H),power(z,2)),-1)
 six=plus(plus(plus(power(X,2),product(cn(2),X,g)),power(g,2)),product(H,power(z,2)),-1)
 six=plus(six,plus(product(cn(2),a,z,X),product(cn(2),a,z,g)))
 need(original==six,'universal six-term norm identity')
 return {'actual_auxiliary_and_finalizer_bindings':True,'full_appended_output_equals_resultant':True,
         'whole_parent_f_T_sign_symmetry':True,
         'full_parent_E_remainder':True,'six_term_norm_identity':poly_record(six,True),
         'formal_polynomials':{n:poly_record(p,True)for n,p in [('D',D),('b',b),('A_rat',A),('B_rat',B),('alpha',alpha),('output',resultant)]}}

def degrees(rows,free,fixed):
 defs={r[0]:r for r in rows}
 guards={
 'cam2':['*','R10a','R12'],'D1':['+','wn2','cam2'],'R14':['+','D1','gam'],'L15':['*','R14','R14'],
 'a_square':['*','R12','R12'],'A':['+','a_square','a4m5'],'c2':['*','R10a','R10a'],'Ac2':['*','A','c2'],
 'norm_main':['-','L15','Ac2'],'difference_multiple':['*','index_rhs','R12'],
 'exponent_partial':['+','W','difference_multiple'],'exponent_rhs':['+','exponent_partial','modulus_multiple'],
 'mu2':['*','exponent_rhs','exponent_rhs'],'kappa2':['*','index_rhs','index_rhs'],
 'scaled_kappa2':['*','A','kappa2'],'norm_input':['-','mu2','scaled_kappa2']}
 for n,t in guards.items():need(defs[n][1:]==t,'degree cut producer guard '+n)
 env={n:(0 if n in fixed else 1,vr(n))for n in free};naive={n:d for n,(d,_)in env.items()}
 def constant(k):return (0,cn(k))if k else(-1,{})
 def get(n):return constant(n)if type(n)is int else env[n]
 def add(a,b,s=1):
  if a[0]>b[0]:return a
  if b[0]>a[0]:return b if s==1 else(b[0],times(cn(-1),b[1]))
  p=plus(a[1],b[1],s);need(bool(p)or a[0]==-1,'unguarded highest cancellation');return(a[0],p)
 def mul(a,b):return(a[0]+b[0],times(a[1],b[1]))if a[1]and b[1]else(-1,{})
 def pr(*a):
  p=constant(1)
  for x in a:p=mul(p,x)
  return p
 def six(x,a,c,g,H):
  terms=[pr(x,x),pr(constant(2),x,g),pr(g,g),pr(constant(2),a,c,x),pr(constant(2),a,c,g),pr(constant(-1),H,c,c)]
  p=constant(0)
  for t in terms:p=add(p,t)
  return p
 for n,o,a,b in rows:
  da=0 if type(a)is int else naive[a];db=0 if type(b)is int else naive[b];naive[n]=da+db if o=='*'else max(da,db)
  if n=='norm_main':env[n]=six(get('wn2'),get('R12'),get('R10a'),get('gam'),get('a4m5'))
  elif n=='norm_input':env[n]=six(get('W'),get('R12'),get('index_rhs'),get('modulus_multiple'),get('a4m5'))
  else:env[n]=mul(get(a),get(b))if o=='*'else add(get(a),get(b),1 if o=='+'else-1)
 Q0=product(vr('Bm1'),vr('Jrep'));k0=plus(vr('eta'),vr('zeta'));g0=plus(vr('rho'),vr('sigma'))
 C1=plus(plus(plus(plus(Q0,vr('F'),-1),vr('Z'),-1),vr('alpha'),-1),product(vr('twice_cell_bits'),vr('x')),-1)
 transport=plus(product(vr('w'),C1),product(vr('transport_quotient'),Q0),-1)
 P5top=product(cn(-32),vr('h'),g0,power(vr('delta'),2),power(k0,3),power(vr('w'),10),power(vr('s'),13),power(Q0,49),transport)
 Rtop=product(power(Q0,3),plus(Q0,vr('F'),-1))
 Dtop=product(power(vr('i'),2),power(k0,4),power(vr('w'),2),power(vr('s'),6),power(Q0,20))
 Qtop=product(power(vr('i'),2),power(k0,4),power(vr('w'),4),power(vr('s'),8),power(Q0,28))
 top=product(power(P5top,2),power(Qtop,2),power(Rtop,4),power(Dtop,4))
 for n,d,p in [('er_P5',81,P5top),('r_lhs',4,Rtop),('er_D',34,Dtop),('R16',46,Qtop),('elimination_polynomial',406,top)]:need(env[n]==(d,p),'uniform highest form '+n)
 exps={'Bm1':252,'Jrep':252,'h':2,'rho':2,'delta':4,'i':12,'eta':30,'w':36,'s':66,'transport_quotient':2}
 mon=tuple(sorted(n for n,e in exps.items()for _ in range(e)))
 need(top.get(mon)==1024,'distinguished uniform monomial')
 need(all(env[n][0]==d for n,d in {'norm_first':22,'norm_main':18,'norm_input':32,'norm_index':7,'norm_transport':2,'er_C':127,'er_L':173,'er_M':203,'er_Z':129,'er_alpha':203,'er_four':376}.items()),'all exact degree ports')
 return {'exact_degree':406,'naive_gate_bound':naive['elimination_polynomial'],'fixed_numerals_have_degree_zero':True,
         'source_guards':guards,'per_row_degrees':{n:env[n][0]for n,_,_,_ in rows},
         'highest_forms':{n:poly_record(env[n][1])for n in ['norm_first','norm_main','norm_input','norm_index','norm_transport','er_P5','r_lhs','er_D','R16','elimination_polynomial']},
         'uniform_leader':'P5_top^2*Q_top^2*R_top^4*D_top^4',
         'distinguished_monomial':{'exponents_including_degree_zero_Bm1':exps,'coefficient':1024}}

def evaluate(rows,assignment):
 env=dict(assignment)
 for n,o,a,b in rows:
  a=a if type(a)is int else env[a];b=b if type(b)is int else env[b]
  env[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return env

def numeric(old,new,free,retained):
 rng=random.Random(9017406);records=[]
 for j in range(32):
  assignment={n:Fraction(rng.randint(-3,3),rng.randint(1,3))if j>=16 else rng.randint(-3,3)for n in free}
  assignment['f']=Fraction(rng.randint(-3,3),rng.randint(1,3))if j>=16 else rng.randint(-3,3)
  a=evaluate(old,assignment);b=evaluate(new,{n:assignment[n]for n in free})
  need(all(a[n]==b[n]for n in retained),'all67 retained numeric values')
  Delta,c,R,i,T,y=a['A'],a['R10a'],a['r_lhs'],a['i'],a['auxiliary_quotient'],a['y_aux']
  D=1+Delta*i*i*c**4;Q=(Delta*i*c*c)**2;bb=c+R*D;P5=a['norm_triple']*a['norm_index']*a['norm_transport']
  aa=Q*(c*c*D*T*T+bb*bb)-(Q-1)*y*y-1;B=2*Q*c*T*bb
  expected=(P5*(aa+1)-1)**2-D*(P5*B)**2
  need(b['elimination_polynomial']==expected,'full numeric field norm')
  def scalar(x):return [x.numerator,x.denominator]if type(x)is Fraction else[x,1]
  records.append({'case':j,'rational':j>=16,'assignment':{n:scalar(v)for n,v in assignment.items()},'output':scalar(expected)})
 # Illustrative local cuts only: these are expressly not native full zeros.
 diagnostic=[]
 for f,T in [(-3,81),(3,-81)]:
  Delta,c,R,i,y=8,1,1,1,255;Q=64;D=9;b=10;P5=1;A=Q*(c*c*D*T*T+b*b)-(Q-1)*y*y-1;B=2*Q*c*T*b
  V=c*T*f-c-R*f*f;Na=Q*V*V-(Q-1)*y*y;Ns=Delta*f*f-Q
  need(Na==1 and Ns==Delta and A==B*f and (P5*(A+1)-1)**2-D*(P5*B)**2==0,'local norm diagnostic')
  diagnostic.append({'Delta':Delta,'c':c,'R':R,'i':i,'T':T,'y':y,'f':f,'P5':P5,'native_full_tuple':False})
 return {'full_source_cases':records,'retained_value_comparisons':32*67,'local_only_zero_diagnostics':diagnostic}

def build(root):
 authenticated={}
 for name,pin in PINS.items():
  b=(root/name).read_bytes();need(sha(b)==pin,'dependency '+name);authenticated[name]=pin
 parent=readjson((root/'complete84_scaled_strong_output.json').read_bytes())['packet'];snapshot=canonical(parent)
 old=parent['source'];need(len(old)==84,'actual84 length');graph(old,parent['free'],parent['output'])
 f_consumers=[r for r in old if 'f'in r[2:]];T_consumers=[r for r in old if 'auxiliary_quotient'in r[2:]]
 need(f_consumers==[['L16','*','f','f'],['auxiliary_Tf','*','auxiliary_quotient','f']],'actual f sign consumers')
 need(T_consumers==[['auxiliary_Tf','*','auxiliary_quotient','f']],'actual T sign consumer')
 sound=readjson((root/'complete84_signed_quotient_soundness_scout.json').read_bytes())
 review=readjson((root/'review_complete84_signed_quotient_soundness.json').read_bytes())
 need(sound['source']['sha256']==PINS['complete84_scaled_strong_output.json'],'signed theorem actual source binding')
 need(review['status']=='PASS'and review['f_consumers']==f_consumers and review['T_consumers']==T_consumers,'accepted sign theorem consumer binding')
 need(all(PINS[n]==v for n,v in review['author_files'].items()),'signed theorem review pins')
 dependencies={n:{n}for n in parent['free']};retained=[];removed=[]
 for row in old:
  n,_,a,b=row;dependencies[n]=set().union(*(dependencies[x]for x in(a,b)if type(x)is str))
  (retained if 'f'not in dependencies[n]else removed).append(list(row))
 need(len(retained)==67 and len(removed)==17,'67+17 partition')
 free=[n for n in parent['free']if n!='f'];witnesses=[n for n in parent['witnesses']if n!='f']
 rows=[list(r)for r in retained]+[list(r)for r in APPEND];output='elimination_polynomial';audit=graph(rows,free,output)
 need(audit['ledger']=={'total':90,'M':52,'A':38},'complete90 count')
 need(len(witnesses)==17 and len(free)==24,'17 witnesses/24 total supplied')
 need(ledger(APPEND)=={'total':23,'M':16,'A':7},'23 complete appended rows')
 proofs=algebra(old,rows);degree=degrees(rows,free,parent['fixed_numerals']);checks=numeric(old,rows,free,[r[0]for r in retained])
 residues={str(d):sorted({(f*f-d*t*t)%4 for f in range(4)for t in range(4)})for d in [0,3]}
 need(all(3 not in s for s in residues.values()),'normalized strong negative unit excluded')
 need(canonical(parent)==snapshot,'inert parent object mutated')
 return {'status':'PASS complete universal90 via exact positive-zero projection and reviewed signed-T positivity',
  'source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':authenticated,
  'packet':{'source':rows,'output':output,'free':free,'witnesses':witnesses,'witness_domain':'strictly positive integers',
   'ordinary_input':parent['ordinary_input'],'fixed_numerals':list(parent['fixed_numerals']),
   'ledger':audit['ledger'],'exact_degree':406,'universal_polynomial_claimed':True,
   'same_retained_positive_zero_projection':True,'restored_positive_f_unique':True,
   'projection':'new zero iff exists a unique positive integer f with original F84 zero on the same retained supplied coordinates; algebra first proves the signed lift and the pinned sign theorem makes it positive',
   'positive_parent_zeros_included':True,'same_polynomial_as_parent':False},
  'structural':{'retained_literal_rows':retained,'removed_f_dependent_rows':removed,'appended_rows':APPEND,
   'retained_ledger':ledger(retained),'appended_ledger':ledger(APPEND),'liveness':audit,'parent_immutable':True,'f_consumers':f_consumers,'T_consumers':T_consumers},
  'algebra':proofs,'degree':degree,'numeric':checks,'mod4_strong_norm_residues':residues,
  'scope':{'full_native_zero_computed':False,'generic_rational_substitution_compiler':False,
   'signed_T_universality_audit_incorporated':True,'predecessor_code_executed_or_imported':False}}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args()
 result=build(args.root)
 if args.output:
  with args.output.open('x')as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
 else:need(typed_equal(result,readjson(args.expect.read_bytes())),'receipt mismatch')
 print('PASS: complete universal90=52M38A,17 positive witnesses; exact positive projection; degree406')
