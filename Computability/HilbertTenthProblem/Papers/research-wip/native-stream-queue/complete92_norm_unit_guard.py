"""Fresh complete92 construction. Frozen predecessors are read as bytes/JSON only."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib,json,random
from pathlib import Path

PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete90_signed_root_elimination.py':'5f41f627ef6649b7dc975f3500f99ede576b156fd787423408b2433a1cd0170c',
 'complete90_signed_root_elimination.json':'ed9595e1ec8077402efac9596a968a10823b20957e3f13740384ef997474cf22',
 'complete90_signed_root_elimination.md':'52211f6ab29781ea23a1fe07d8644f4012ca4740658b4e1f42b618a5fc0fb8ec',
 'complete84_signed_quotient_soundness_scout.md':'b2f1c37ebf68216e657006acaebbac0b27faedb325e1603983786085d580f44a',
 'complete84_signed_quotient_soundness_scout.json':'0e31841fce2a8db87c930c8f5fcfeeab3e3761547897c218d2c964e1dab906cf',
 'review_complete84_signed_quotient_soundness.md':'e392d0c0c904d64a007234ec2a2759921ac6bbb1f2ca058539c15dd6705486f8',
 'review_complete84_signed_quotient_soundness.json':'2551ffd6511d2e39254bed4c2f44ec270e71123ea5485389176cff37c59205a9',
}
TAIL=[
 ['ng_ic2','*','i','c2'],['ng_Dminus1','*','ng_ic2','aux_coefficient_root'],['ng_D','+','ng_Dminus1',1],
 ['ng_RD','*','r_lhs','ng_D'],['ng_b','+','R10a','ng_RD'],['ng_u','*','R10a','auxiliary_quotient'],
 ['ng_u2','*','ng_u','ng_u'],['ng_p','*','ng_D','ng_u2'],['ng_b2','*','ng_b','ng_b'],
 ['ng_P5a','*','norm_triple','norm_index'],['ng_P5','*','ng_P5a','norm_transport'],
 ['ng_sum','+','ng_p','ng_b2'],['ng_gap','-','ng_sum','aux_y2'],['ng_Qgap','*','R16','ng_gap'],
 ['ng_Aplus1','+','ng_Qgap','aux_y2'],['ng_A','-','ng_Aplus1',1],
 ['ng_Qp','*','R16','ng_p'],['ng_Qb2','*','R16','ng_b2'],['ng_cross','*','ng_Qp','ng_Qb2'],['ng_four','*',4,'ng_cross'],
 ['ng_A2','*','ng_A','ng_A'],['ng_K','-','ng_A2','ng_four'],['ng_unit','+','ng_K',1],
 ['ng_product','*','ng_P5','ng_unit'],['polynomial92','-','ng_product',1],
]
def require(ok,message):
 if not ok:raise ValueError(message)
def digest(b):return hashlib.sha256(b).hexdigest()
def packed(v):return json.dumps(v,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode()
def pairs(ps):
 d={}
 for k,v in ps:require(k not in d,'duplicate key');d[k]=v
 return d
def bad_number(s):raise ValueError('noninteger JSON number '+s)
def parse(raw):return json.loads(raw,object_pairs_hook=pairs,parse_float=bad_number,parse_constant=bad_number)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def literal(c):return {():c}if c else{}
def symbol(n):return {(n,):1}
def add(a,b,sgn=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+sgn*v
 return {m:v for m,v in c.items()if v}
def multiply(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(sorted(m+n));c[k]=c.get(k,0)+v*w
 return {m:v for m,v in c.items()if v}
def prod(*args):
 c=literal(1)
 for a in args:c=multiply(c,a)
 return c
def powpoly(a,k):
 c=literal(1)
 while k:
  if k&1:c=multiply(c,a)
  k//=2
  if k:a=multiply(a,a)
 return c
def coefficients(p):return [[list(m),v]for m,v in sorted(p.items())]
def summary(p,save=False):
 x=coefficients(p);d={'terms':len(x),'sha256':digest(packed(x))}
 if save:d['coefficients']=x
 return d

def ledger(rows):
 c=Counter(r[1]for r in rows);return {'total':len(rows),'M':c['*'],'A':c['+']+c['-']}
def audit(rows,free,out):
 known=set(free);require(len(known)==len(free),'duplicate free');defs={}
 for row in rows:
  require(type(row)is list and len(row)==4,'row schema');n,op,a,b=row
  require(type(n)is str and n not in known and op in('+','-','*'),'SSA schema')
  require(all(type(x)is int or(type(x)is str and x in known)for x in(a,b)),'topology')
  known.add(n);defs[n]=row
 used=set();leaves=set();stack=[out]
 while stack:
  n=stack.pop()
  if type(n)is int:continue
  if n in defs:
   if n not in used:used.add(n);stack.extend(defs[n][2:])
  else:require(n in free,'undefined leaf');leaves.add(n)
 require(used==set(defs)and leaves==set(free),'dead row or supplied port')
 return {'ledger':ledger(rows),'live_rows':len(used),'live_supplied':len(leaves)}
def expand(rows,cuts,targets):
 definitions={r[0]:r for r in rows};memo=dict(cuts)
 def visit(n):
  if type(n)is int:return literal(n)
  if n not in memo:
   require(n in definitions,'unbound cut '+n);_,op,a,b=definitions[n];a,b=visit(a),visit(b)
   memo[n]=multiply(a,b)if op=='*'else add(a,b,1 if op=='+'else-1)
  return memo[n]
 return {n:visit(n)for n in targets}

def identities(old,ninety,new):
 Delta,c,R,i,T,y,f=map(symbol,['Delta','c','R','i','T','y','f'])
 c2=powpoly(c,2);S=prod(Delta,i,c2);Q=powpoly(S,2);D=add(literal(1),prod(Delta,powpoly(i,2),powpoly(c,4)))
 b=add(c,prod(R,D));u=prod(c,T);P5=prod(symbol('Ntriple'),symbol('Nindex'),symbol('Ntransport'))
 A=add(add(prod(Q,add(prod(D,powpoly(u,2)),powpoly(b,2))),prod(add(Q,literal(1),-1),powpoly(y,2)),-1),literal(1),-1)
 B=prod(literal(2),Q,u,b);K=add(powpoly(A,2),prod(D,powpoly(B,2)),-1)
 target=add(prod(P5,add(K,literal(1))),literal(1),-1)
 E=add(powpoly(f,2),D,-1);V=add(add(prod(c,T,f),c,-1),prod(R,powpoly(f,2)),-1)
 Na=add(prod(Q,add(powpoly(V,2),powpoly(y,2),-1)),powpoly(y,2));Ns=add(prod(Delta,powpoly(f,2)),Q,-1)
 cuts={'A':Delta,'R10a':c,'r_lhs':R,'i':i,'auxiliary_quotient':T,'y_aux':y,'f':f,
 'norm_triple':symbol('Ntriple'),'norm_index':symbol('Nindex'),'norm_transport':symbol('Ntransport')}
 actual=expand(old,cuts,['c2','Ac2','aux_coefficient_root','R16','aux_u_rhs','norm_aux','norm_strong','polynomial'])
 expected={'c2':c2,'Ac2':prod(Delta,c2),'aux_coefficient_root':S,'R16':Q,'aux_u_rhs':V,'norm_aux':Na,'norm_strong':Ns,
 'polynomial':add(prod(P5,Na,Ns),Delta,-1)}
 require(actual==expected,'actual complete84/auxiliary binding')
 child=expand(new,cuts,['ng_D','ng_b','ng_P5','ng_A','ng_four','ng_K','polynomial92'])
 require(child=={'ng_D':D,'ng_b':b,'ng_P5':P5,'ng_A':A,'ng_four':prod(D,powpoly(B,2)),'ng_K':K,'polynomial92':target},'complete92 field norm/unit')
 F90=expand(ninety,cuts,['elimination_polynomial'])['elimination_polynomial']
 correction=prod(add(P5,literal(1),-1),add(prod(literal(2),P5,A),literal(1),-1))
 require(add(F90,prod(P5,target),-1)==correction,'exact whole90/92 correction')
 rem=prod(Q,add(add(powpoly(u,2),prod(literal(2),R,u,f),-1),add(prod(literal(2),R,b),prod(powpoly(R,2),E))))
 require(add(add(Na,literal(1),-1),add(A,prod(B,f),-1),-1)==prod(E,rem),'auxiliary strong-ideal remainder')
 require(add(Ns,Delta,-1)==prod(Delta,E),'scaled strong identity')
 contracted=prod(Delta,add(prod(P5,add(add(A,prod(B,f),-1),literal(1))),literal(1),-1))
 require(add(actual['polynomial'],contracted,-1)==prod(P5,Delta,E,add(rem,Na)),'whole84 E remainder')
 require({m:v*(-1)**(m.count('f')+m.count('T'))for m,v in actual['polynomial'].items()}==actual['polynomial'],'full parent sign symmetry')
 a=symbol('a');actual_delta=expand(old,{'R12':a},['A'])['A'];require(actual_delta==prod(add(a,literal(1)),add(a,literal(3))),'actual discriminant')
 # Algebraic cancellation guard, independent of degrees or zero equations.
 X,z,g,H=map(symbol,['X','z','g','H'])
 left=add(powpoly(add(add(X,prod(a,z)),g),2),prod(add(powpoly(a,2),H),powpoly(z,2)),-1)
 right=add(add(add(powpoly(X,2),prod(literal(2),X,g)),powpoly(g,2)),prod(H,powpoly(z,2)),-1)
 right=add(right,add(prod(literal(2),a,z,X),prod(literal(2),a,z,g)));require(left==right,'six-term norm')
 return {'all_complete_source_identities':True,'whole90_92_relation':'F90=P5*F92+(P5-1)*(2*P5*A_rat-1)',
 'formal_polynomials':{n:summary(p,True)for n,p in [('D',D),('A_rat',A),('B_rat',B),('K',K),('F92',target),('correction90_92',correction)]},
 'norm_cancellation':summary(right,True),'full_parent_sign_symmetry':True}

def highest(rows,free,fixed):
 ds={r[0]:r[1:]for r in rows}
 guards={'cam2':['*','R10a','R12'],'D1':['+','wn2','cam2'],'R14':['+','D1','gam'],'L15':['*','R14','R14'],
 'a_square':['*','R12','R12'],'A':['+','a_square','a4m5'],'c2':['*','R10a','R10a'],'Ac2':['*','A','c2'],'norm_main':['-','L15','Ac2'],
 'difference_multiple':['*','index_rhs','R12'],'exponent_partial':['+','W','difference_multiple'],'exponent_rhs':['+','exponent_partial','modulus_multiple'],
 'mu2':['*','exponent_rhs','exponent_rhs'],'kappa2':['*','index_rhs','index_rhs'],'scaled_kappa2':['*','A','kappa2'],'norm_input':['-','mu2','scaled_kappa2']}
 require(all(ds[k]==v for k,v in guards.items()),'all actual cancellation cones')
 values={n:(0 if n in fixed else 1,symbol(n))for n in free};naive={n:v[0]for n,v in values.items()}
 def const(n):return (0,literal(n))if n else(-1,{})
 def v(n):return const(n)if type(n)is int else values[n]
 def plus(a,b,s=1):
  if a[0]>b[0]:return a
  if b[0]>a[0]:return b if s==1 else(b[0],multiply(literal(-1),b[1]))
  p=add(a[1],b[1],s);require(p or a[0]==-1,'unexpected leading cancellation');return(a[0],p)
 def mul(a,b):return (a[0]+b[0],multiply(a[1],b[1]))if a[1]and b[1]else(-1,{})
 def term(*aa):
  p=const(1)
  for a in aa:p=mul(p,a)
  return p
 def norm(X,a,c,g,H):
  result=const(0)
  for t in [term(X,X),term(const(2),X,g),term(g,g),term(const(2),a,c,X),term(const(2),a,c,g),term(const(-1),H,c,c)]:result=plus(result,t)
  return result
 for n,op,a,b in rows:
  da=0 if type(a)is int else naive[a];db=0 if type(b)is int else naive[b];naive[n]=da+db if op=='*'else max(da,db)
  if n=='norm_main':values[n]=norm(v('wn2'),v('R12'),v('R10a'),v('gam'),v('a4m5'))
  elif n=='norm_input':values[n]=norm(v('W'),v('R12'),v('index_rhs'),v('modulus_multiple'),v('a4m5'))
  else:values[n]=mul(v(a),v(b))if op=='*'else plus(v(a),v(b),1 if op=='+'else-1)
 q0=prod(symbol('Bm1'),symbol('Jrep'));k0=add(symbol('eta'),symbol('zeta'));g0=add(symbol('rho'),symbol('sigma'))
 C1=add(add(add(add(q0,symbol('F'),-1),symbol('Z'),-1),symbol('alpha'),-1),prod(symbol('twice_cell_bits'),symbol('x')),-1)
 tr=add(prod(symbol('w'),C1),prod(symbol('transport_quotient'),q0),-1)
 ptop=prod(literal(-32),symbol('h'),g0,powpoly(symbol('delta'),2),powpoly(k0,3),powpoly(symbol('w'),10),powpoly(symbol('s'),13),powpoly(q0,49),tr)
 qtop=prod(powpoly(symbol('i'),2),powpoly(k0,4),powpoly(symbol('w'),4),powpoly(symbol('s'),8),powpoly(q0,28))
 rtop=prod(powpoly(q0,3),add(q0,symbol('F'),-1));dtop=prod(powpoly(symbol('i'),2),powpoly(k0,4),powpoly(symbol('w'),2),powpoly(symbol('s'),6),powpoly(q0,20))
 atop=prod(qtop,powpoly(rtop,2),powpoly(dtop,2));ktop=powpoly(atop,2);top=prod(ptop,ktop)
 for n,degree,poly in [('ng_P5',81,ptop),('R16',46,qtop),('r_lhs',4,rtop),('ng_D',34,dtop),('ng_A',122,atop),('ng_K',244,ktop),('polynomial92',325,top)]:require(values[n]==(degree,poly),'actual exact top '+n)
 expected_degrees={'norm_first':22,'norm_main':18,'norm_input':32,'norm_index':7,'norm_transport':2,'ng_b':38,'ng_p':46,'ng_b2':76,'ng_four':214}
 require(all(values[n][0]==d for n,d in expected_degrees.items()),'factor/cross degrees')
 exp={'Bm1':202,'Jrep':202,'h':1,'rho':1,'delta':2,'i':12,'eta':27,'w':26,'s':53,'transport_quotient':1}
 mon=tuple(sorted(n for n,k in exp.items()for _ in range(k)));require(top.get(mon)==32,'uniform distinguished coefficient')
 return {'exact_degree':325,'naive_bound':naive['polynomial92'],'cancellation_guards':guards,
 'per_row_degrees':{n:values[n][0]for n,_,_,_ in rows},'highest_components':{n:summary(values[n][1])for n in ['norm_first','norm_main','norm_input','norm_index','norm_transport','ng_P5','R16','r_lhs','ng_D','ng_A','ng_K','polynomial92']},
 'distinguished_monomial':{'exponents_with_fixed_Bm1':exp,'coefficient':32},'leader':'P5_top*Q_top^2*R_top^4*D_top^4'}

def evaluate(rows,assignment):
 env=dict(assignment)
 for n,op,a,b in rows:
  a=a if type(a)is int else env[a];b=b if type(b)is int else env[b]
  env[n]=a*b if op=='*'else a+b if op=='+'else a-b
 return env

def numeric(old,ninety,new,free,names):
 randomizer=random.Random(9217325);cases=[]
 for index in range(24):
  assignment={n:Fraction(randomizer.randint(-3,3),randomizer.randint(1,3))if index>=16 else randomizer.randint(-3,3)for n in free}
  child=evaluate(new,assignment);p90=evaluate(ninety,assignment);p84=evaluate(old,dict(assignment,f=randomizer.randint(-3,3)))
  require(all(child[n]==p84[n]==p90[n]for n in names),'all67 retained numeric values')
  Delta,c,i,R,T,y=child['A'],child['R10a'],child['i'],child['r_lhs'],child['auxiliary_quotient'],child['y_aux']
  D=1+Delta*i*i*c**4;Q=(Delta*i*c*c)**2;b=c+R*D;A=Q*(c*c*D*T*T+b*b)-(Q-1)*y*y-1;B=2*Q*c*T*b;P5=child['norm_triple']*child['norm_index']*child['norm_transport']
  target=P5*(A*A-D*B*B+1)-1;require(child['polynomial92']==target,'complete92 numeric')
  require(p90['elimination_polynomial']==P5*target+(P5-1)*(2*P5*A-1),'complete90/92 numeric relation')
  def scalar(v):return [v.numerator,v.denominator]if type(v)is Fraction else[v,1]
  cases.append({'case':index,'rational':index>=16,'assignment':{n:scalar(v)for n,v in assignment.items()},'output':scalar(target)})
 return {'full_source_cases':cases,'retained_comparisons':24*67,'native_zero_fixture_claimed':False}

def build(root):
 for name,h in PINS.items():require(digest((root/name).read_bytes())==h,'dependency pin '+name)
 p84=parse((root/'complete84_scaled_strong_output.json').read_bytes())['packet'];p90=parse((root/'complete90_signed_root_elimination.json').read_bytes())['packet']
 snapshots=[packed(p84),packed(p90)];old=p84['source'];ninety=p90['source'];audit(old,p84['free'],p84['output']);audit(ninety,p90['free'],p90['output'])
 dependencies={n:{n}for n in p84['free']};kept=[];removed=[]
 for row in old:
  n,_,a,b=row;dependencies[n]=set().union(*(dependencies[x]for x in(a,b)if type(x)is str));(kept if 'f'not in dependencies[n]else removed).append(list(row))
 require(len(kept)==67 and len(removed)==17 and kept==ninety[:67],'actual67 closure/90 prefix')
 free=[n for n in p84['free']if n!='f'];witnesses=[n for n in p84['witnesses']if n!='f'];require(free==p90['free']and witnesses==p90['witnesses'],'same supplied interface')
 rows=[list(r)for r in kept]+[list(r)for r in TAIL];check=audit(rows,free,'polynomial92')
 require(check['ledger']=={'total':92,'M':52,'A':40}and len(witnesses)==17,'complete count')
 require(ledger(TAIL)=={'total':25,'M':16,'A':9},'complete tail count')
 fcons=[r for r in old if 'f'in r[2:]];tcons=[r for r in old if 'auxiliary_quotient'in r[2:]]
 require(fcons==[['L16','*','f','f'],['auxiliary_Tf','*','auxiliary_quotient','f']]and tcons==[fcons[1]],'actual sign consumers')
 author=parse((root/'complete84_signed_quotient_soundness_scout.json').read_bytes());review=parse((root/'review_complete84_signed_quotient_soundness.json').read_bytes())
 require(author['source']['sha256']==PINS['complete84_scaled_strong_output.json']and review['status']=='PASS','accepted signed theorem binding')
 require(review['f_consumers']==fcons and review['T_consumers']==tcons and all(PINS[n]==h for n,h in review['author_files'].items()),'sign theorem review coupling')
 formal=identities(old,ninety,rows);degree=highest(rows,free,p84['fixed_numerals']);tests=numeric(old,ninety,rows,free,[r[0]for r in kept])
 require(snapshots==[packed(p84),packed(p90)],'inert parents mutated')
 # Finite residue evidence supplements the all-integer proofs in the companion.
 residue={'K_plus_one':sorted({(a*a-d*(2*b)**2+1)%4 for a in range(4)for d in range(4)for b in range(4)}),
 'auxiliary_norm':sorted({(s*s*v*v-(s*s-1)*y*y)%4 for s in range(4)for v in range(4)for y in range(4)}),
 'strong_norm':sorted({(f*f-d*t*t)%4 for d in [0,3]for f in range(4)for t in range(4)})}
 require(residue['K_plus_one']==[1,2]and residue['auxiliary_norm']==[0,1]and 3 not in residue['strong_norm'],'mod4 exclusions')
 return {'status':'PASS complete92 universal17-witness degree325 construction','source_sha256':digest(Path(__file__).read_bytes()),'pins':PINS,
 'packet':{'source':rows,'free':free,'witnesses':witnesses,'ordinary_input':p84['ordinary_input'],'fixed_numerals':list(p84['fixed_numerals']),
 'output':'polynomial92','ledger':check['ledger'],'exact_degree':325,'universal_polynomial_claimed':True,
 'same_positive_zero_tuples_as90':True,'same_polynomial_as90':False,'unique_positive_f_restoration':'A_rat/B_rat',
 'witness_domain':'strictly positive integers; inherited valid fixed-program recipe'},
 'structure':{'retained_literal_rows':kept,'removed_f_dependent_parent_rows':removed,'appended_source':TAIL,'retained_ledger':ledger(kept),'tail_ledger':ledger(TAIL),
 'liveness':check,'parents_immutable':True,'direct_f_consumers':fcons,'direct_T_consumers':tcons},
 'algebra':formal,'degree':degree,'numeric':tests,'mod4_evidence':residue,
 'scope':{'frozen_helpers_executed_or_imported':False,'generic_root_eliminator':False,'global_optimality':False,'full_native_zero_computed':False}}

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True);group=parser.add_mutually_exclusive_group(required=True);group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path);args=parser.parse_args()
 result=build(args.root)
 if args.output:
  with args.output.open('x')as stream:json.dump(result,stream,sort_keys=True,indent=2);stream.write('\n')
 else:require(exact(result,parse(args.expect.read_bytes())),'receipt mismatch')
 print('PASS complete92=52M40A,17 positive witnesses,exact degree325')
