#!/usr/bin/env python3
"""Independent exact counts and high precision analytic diagnostics; not interval certificates."""
import argparse,math,json
from validation import domain, integer, require, load_pinned_json, write_json, require_diagnostic_digit_limit
from fractions import Fraction
from pathlib import Path
import mpmath as mp
import sympy as sy
ROOT=Path(__file__).resolve().parent

def fubini(N):
 integer("N",N)
 f=[1]
 for n in range(1,N+1): f.append(sum(math.comb(n,k)*f[n-k] for k in range(1,n+1)))
 return f

def stirling1_unsigned(n):
 integer("n",n)
 a=[1]
 for k in range(n):
  b=[0]*(len(a)+1)
  for j,x in enumerate(a): b[j]+=k*x; b[j+1]+=x
  a=b
 return a

def h_stirling(d,n,f):
 domain(d,n)
 if len(f)<=d*n or any(type(x) is not int for x in f):
  raise ValueError("Fubini table must contain integer entries through d*n")
 if n==0:return 1
 a=stirling1_unsigned(n)
 q=sum((-1)**(n-j)*a[j]*f[d*j] for j in range(1,n+1))
 out,rem=divmod(q,math.factorial(n))
 if rem:raise ArithmeticError('noninteger count')
 return out

def h_inclusion(d,n):
 domain(d,n)
 total=0
 for v in range(d*n+1):
  total+=sum((-1)**(v-k)*math.comb(v,k)*math.comb(k**d,n) for k in range(v+1))
 return total

def amplitude(d,n,z,absolute=False):
 domain(d,n,1)
 if type(absolute) is not bool:raise ValueError("absolute must be bool")
 if not mp.isfinite(z):raise ValueError("z must be finite")
 a=stirling1_unsigned(n); N=d*n
 return mp.fsum([((-1)**(n-j) if not absolute else 1)*mp.mpf(a[j])*mp.factorial(d*j)/mp.factorial(N)*z**(d*(n-j)) for j in range(1,n+1)])

def sector_relative(d,n,m):
 domain(d,n,1)
 if type(m) is not int:raise ValueError("m must be an integer")
 z=mp.log(2)+2*mp.pi*1j*m
 return (mp.log(2)/z)**(d*n+1)*amplitude(d,n,z)

def tail_bound(d,n,M,envelope=False):
 domain(d,n,1)
 integer("M",M,1)
 if type(envelope) is not bool:raise ValueError("envelope must be bool")
 a=mp.log(2); R=mp.sqrt(a*a+(2*mp.pi*M)**2)
 K=1+R*R/(4*mp.pi**2*M*(d-1))
 A=mp.exp(mp.e**d/(2*d**d)*R**d*n**(2-d)*(1-mp.mpf(1)/n)) if envelope else amplitude(d,n,R,True)
 return 2*K*(a/R)**(d*n+1)*A

def ss(x):return mp.nstr(x,25)

OEIS_DIGEST="940423ca7e8250d98aadf26d2aa6571461fe75ec6bf9752c13ac2ce5473aefe0"
COEFFICIENT_DIGEST="b48f6fda72cf2193531f4e9039c00fc9a6025ae27d43ad3d4550692986a5ae72"

def load_oeis(path):
 return load_pinned_json(path,OEIS_DIGEST,"OEIS reference")

def load_coefficients(path):
 return load_pinned_json(path,COEFFICIENT_DIGEST,"Hierarchy coefficients")

def run(coefficients_path=ROOT/'hierarchy_coefficients.json',oeis_path=ROOT/'oeis_reference.json',output=ROOT/'check_results.json'):
 require_diagnostic_digit_limit()
 coeff=load_coefficients(coefficients_path)
 reference=load_oeis(oeis_path)
 result={'description':'Numerical checks, not interval certificates','exact_counts':{},'sector_diagnostics':[],'expansion_diagnostics':[]}
 f=fubini(4*160)
 known={int(d):v["terms"] for d,v in reference.items()}
 for d in [2,3,4]:
  vals=[]
  for n in range(9):
   a=h_stirling(d,n,f); b=h_inclusion(d,n)
   if a!=b:raise ArithmeticError((d,n,a,b))
   vals.append(a)
  if vals!=known[d]:raise ArithmeticError(('OEIS mismatch',d))
  result['exact_counts'][str(d)]=vals
 for d,n in [(2,1),(3,1),(4,1),(2,10),(2,30),(2,80),(2,160),(3,10),(3,30),(4,10),(4,30)]:
  mp.mp.dps=6*d*n+80
  exact=mp.mpf(h_stirling(d,n,f))
  B=mp.factorial(d*n)/(2*mp.factorial(n)*mp.log(2)**(d*n+1))
  for M in sorted(set([1,2,3,math.ceil(n**(1-1/d))])):
   partial=mp.re(mp.fsum(sector_relative(d,n,m) for m in range(-M+1,M)))
   err=abs(exact/B-partial); bound=tail_bound(d,n,M)
   if not err<bound:raise ArithmeticError(('tail failed',d,n,M,ss(err),ss(bound)))
   result['sector_diagnostics'].append({'d':d,'n':n,'M':M,'relative_error':ss(err),'positive_polynomial_bound':ss(bound),'envelope_bound':ss(tail_bound(d,n,M,True)),'error_over_bound':ss(err/bound)})
 z=sy.Symbol('z')
 for d in [2,3,4]:
  expr=[sy.sympify(a,locals={'z':z}) for a in coeff[str(d)]]
  funcs=[sy.lambdify(z,a,'mpmath') for a in expr]
  for m in [0,1]:
   for n in [40,80,160]:
    mp.mp.dps=150
    zz=mp.log(2)+2*mp.pi*1j*m
    A=amplitude(d,n,zz)
    lead=mp.exp(-zz**2/8) if d==2 else mp.mpf(1)
    for order in [1,2,3,4]:
     approx=lead*sum(funcs[r](zz)/n**r for r in range(order+1))
     delta=(A-approx)/lead
     result['expansion_diagnostics'].append({'d':d,'m':m,'n':n,'order':order,'scaled_residual':ss(delta*n**(order+1))})
 write_json(output,result)
 print(json.dumps({'status':'PASS','independent_exact_cases':27,'sector_checks':len(result['sector_diagnostics']),'expansion_diagnostics':len(result['expansion_diagnostics'])}))
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--coefficients',type=Path,default=ROOT/'hierarchy_coefficients.json')
 parser.add_argument('--oeis',type=Path,default=ROOT/'oeis_reference.json')
 parser.add_argument('--output',type=Path,default=ROOT/'check_results.json')
 args=parser.parse_args()
 run(args.coefficients,args.oeis,args.output)
