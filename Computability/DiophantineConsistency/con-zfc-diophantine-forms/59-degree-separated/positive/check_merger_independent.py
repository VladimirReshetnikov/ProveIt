#!/usr/bin/env python3
"""Independent exact norm identity, unit guard, DAG and bounded diagnostics.
No builder or other checker is imported. Number-theoretic proofs are separate.
"""
import collections,fractions,hashlib,itertools,json,math
from pathlib import Path
R=Path(__file__).resolve().parent

def require(x,s):
 if not x:raise ValueError(s)
# Polynomial ring Z[x,p,r,d,Z,sqrt(p),sqrt(r)] modulo the two square relations.
def add(a,b,k=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+k*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out=collections.defaultdict(int)
 for m,c in a.items():
  for n,d in b.items():
   z=[v+w for v,w in zip(m,n)]
   z[1]+=z[5]//2;z[2]+=z[6]//2;z[5]%=2;z[6]%=2
   out[tuple(z)]+=c*d
 return {m:c for m,c in out.items() if c}
def const(c):return {(0,)*7:c} if c else {}
def var(i):m=[0]*7;m[i]=1;return {tuple(m):1}
def scale(a,k):return {m:k*c for m,c in a.items() if k*c}
def sq(a):return mul(a,a)
def norm_identity():
 x,p,r,d,Z,sp,sr=[var(i) for i in range(7)]
 product=const(1)
 for ep,er in itertools.product([-1,1],repeat=2):
  factor=add(mul(d,sq(add(add(x,sp,ep),sr,er))),Z,-1)
  product=mul(product,factor)
 M=add(mul(d,add(add(sq(x),p),r)),Z,-1)
 C0=add(sq(M),scale(mul(sq(d),add(mul(sq(x),add(r,p,-1)),mul(p,r),-1)),4))
 B=add(scale(mul(d,p),2),M,-1)
 expected=add(sq(C0),scale(mul(mul(mul(sq(d),sq(x)),r),sq(B)),16),-1)
 require(product==expected,'four-factor norm identity')
 require(all(m[5:]==(0,0) for m in product),'radicals did not cancel')
 return len(product)
def dag_check(name,expected_ops):
 data=json.loads((R/name).read_text());seen=set(data['witnesses']+data['fixed_numerals']);require(len(data['witnesses'])==12,'witness count')
 for gate in data['source']:
  n,op,a,b=gate;require(op in ['+','-','*'],'operation');require(n not in seen,'duplicate register')
  require(all(isinstance(z,int) or z in seen for z in [a,b]),'unbound operand');seen.add(n)
 live={data['output']} if 'output'in data else {z for pair in data['comparisons'] for z in pair if isinstance(z,str)}
 for n,op,a,b in reversed(data['source']):
  require(n in live,'dead gate');live.update(z for z in [a,b] if isinstance(z,str))
 require(set(data['witnesses']+data['fixed_numerals'])<=live,'dead leaf')
 require(len(data['source'])==expected_ops,'operation count')
 return {'file':name,'operations':expected_ops,'all_gates_and_inputs_live':True,'sha256':hashlib.sha256((R/name).read_bytes()).hexdigest()}
def evaldag(data,vals):
 env=dict(vals)
 for n,op,a,b in data['source']:
  a=a if isinstance(a,int) else env[a];b=b if isinstance(b,int) else env[b]
  env[n]=a+b if op=='+'else a-b if op=='-'else a*b
 return env

def literal_formula(vals):
 J,F,al,z,f0,T,s,w,eta,zeta,gamma,t=[vals[n]for n in ['J','F','alpha','z','f0','T','s','w','eta','zeta','gamma','t']]
 beta,K0,MC,MF=[vals[n] for n in ['beta','K0','MC','MF']]
 q=beta*J+1;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;Delta=a*a+H;ell=E*k*Y;A=ell*(ell+k)+1
 U=4*q**4;C=q-F-al;Rc=((q-1)*(q-F)+al)*(q*q-1)+(MC+q*MF)*J;Dstar=U*(X+a*c)+H*(U*gamma-k+Rc+1)
 f=f0+1;Q=Delta*(f*f-1);d=Q-1;V=c*(T*f-1)-Rc*f*f;Eaux=Q*V*V-1;M2=2*f*ell
 xx=c*c*t;p=Q;r=c**4*f*f*A;Z=c**4*M2*M2*Eaux;M=d*(xx*xx+p+r)-Z;C0=M*M+4*d*d*(xx*xx*(r-p)-p*r)
 Ninner=C0*C0-16*d*d*xx*xx*r*(2*d*p-M)**2
 Nmain=Dstar*Dstar-U*U*(Delta*c*c+1);Nt=(K0+w)*C+q-F-z*(q-1)
 return Nt*(Nmain+1)*(Ninner+1)-1,Nmain,Ninner

def main():
 terms=norm_identity();unit_checks=0
 # Every possible square residue mod4 excludes -2, for each norm.
 for x in range(4):
  require((x*x)%4!=2,'square is -2 modulo4');unit_checks+=1
 product=json.loads((R/'ordinary_merger_product.json').read_text())
 literal_cases=0
 for j in range(1,17):
  vals={n:1+(j*(i+3))%9 for i,n in enumerate(product['witnesses']+product['fixed_numerals'])}
  env=evaldag(product,vals);P,M,I=literal_formula(vals)
  require(env[product['output']]==P and env['Nmain']==M and env['Ninner']==I,'independent literal formula mismatch');literal_cases+=1
 # Diagnostic only: finite rational-square candidates in the saturation lemma.
 rational_cases=0;square_hits=0
 for K in range(2,201):
  for V in range(1,401):
   frac=fractions.Fraction(K*K*V*V-1,K*K-1);a=math.isqrt(frac.numerator);b=math.isqrt(frac.denominator);rational_cases+=1
   if a*a==frac.numerator and b*b==frac.denominator:
    square_hits+=1;require(b==1,'counterexample to rational-Pell saturation')
 dags=[dag_check(f,n) for f,n in [('ordinary_merger_product.json',102),('ordinary_merger_system.json',95),('ordinary_merger_shifted_system.json',94),('ordinary_merger_sos.json',103)]]
 result={'status':'PASS','exact_formal_radical_norm_identity':True,'expanded_integer_polynomial_terms':terms,'mod4_unit_guard_residues_checked':unit_checks,'independent_literal_circuit_evaluations':literal_cases,'DAGs':dags,'rational_Pell_diagnostic_cases':rational_cases,'rational_Pell_square_hits':square_hits,'diagnostic_scope':'Finite saturation tests are diagnostics only. The universal lemma requires the independent mathematical proof in INDEPENDENT_REVIEW.md. Degree claims are not certified by this checker.'}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
