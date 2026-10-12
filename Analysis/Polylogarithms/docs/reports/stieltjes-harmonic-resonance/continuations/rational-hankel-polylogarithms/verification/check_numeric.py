"""Floating-point diagnostics. These are not interval certificates or proofs."""
from pathlib import Path
from functools import lru_cache
from itertools import permutations
import json
import mpmath as mp
import sympy as S
from compiler import z
if not __debug__:raise RuntimeError('Do not run verification with -O.')
root=Path(__file__).resolve().parents[1]
mp.mp.dps=60
checks=[]

def record(name,a,b,tol=mp.mpf('1e-48')):
 e=abs(a-b)/max(1,abs(a),abs(b));assert e<tol,(name,e)
 checks.append({'name':name,'left':mp.nstr(a,62),'right':mp.nstr(b,62),'scaled_residual':mp.nstr(e,12),'tolerance':str(tol)})
 print(name,mp.nstr(e,6),flush=True)

@lru_cache(None)
def hw_series(word,n):
 if not word:return (mp.mpf(1),)+(mp.mpf(0),)*n
 t=hw_series(word[1:],n);a=[mp.mpf(0)]*(n+1)
 if word[0]==0:
  for k in range(1,n+1):a[k]=t[k]/k
 else:
  acc=mp.mpf(0)
  for k in range(1,n+1):acc+=t[k-1];a[k]=acc/k
 return tuple(a)

def hw(word,x,n=360):
 return mp.fsum(c*x**k for k,c in enumerate(hw_series(tuple(word),n)))

def eval_formula(entries,x):
 ans=mp.mpf(0)
 for e in entries:
  fun=S.lambdify(z,S.sympify(e['coefficient']),modules='mpmath')
  ans+=fun(x)*hw(e['word'],x)
 return ans

def direct_gen(r,poles,x,n=320,polynomial=()):
 vals=[mp.mpf(0)]*(2*r-1);ans=mp.mpf(0)
 for m in range(1,n+1):
  w=sum(mp.mpf(c)*mp.mpf(m)**t for t,c in enumerate(polynomial))
  w+=sum(mp.mpf(c)/mp.mpf(m+a)**ell for a,ell,c in poles)
  for j in range(2*r-1):vals[j]+=mp.mpf(m)**j*w
  if m>=r:ans+=mp.det(mp.matrix([[vals[i+j] for j in range(r)] for i in range(r)]))*x**m
 return ans

examples={e['name']:e for e in json.loads((root/'data'/'compiled_examples.json').read_text())}
for name,r,poles,poly in [('triple-pole-r2',2,[(0,3,1)],()),('three-simple-r3',3,[(0,1,1),(1,1,1),(2,1,1)],()),('separated-two-r2',2,[(0,1,1),(3,1,-2)],()),('shifted-double-r2',2,[(1,2,1)],()),('polynomial-plus-pole',2,[(1,1,2)],(1,1))]:
 x=mp.mpf('0.37')
 record('compiled-'+name,direct_gen(r,poles,x,polynomial=poly),eval_formula(examples[name]['generator'],x))

def li2(a,b,x,n=270):
 h=mp.mpf(0);ans=mp.mpf(0)
 for k in range(1,n+1):
  ans+=x**k*mp.power(k,-a)*h
  h+=mp.power(k,-b)
 return ans

def spectral(s,x):
 return (li2(s,s-2,x)+li2(s-2,s,x)-2*li2(s-1,s-1,x))/(1-x)

def spectral_direct(s,x,n=270):
 h=[mp.mpf(0)]*3;ans=mp.mpf(0)
 for m in range(1,n+1):
  for j in range(3):h[j]+=mp.power(m,j-s)
  ans+=(h[0]*h[2]-h[1]**2)*x**m
 return ans
for ss in [mp.mpf('2.7'),mp.mpc('3.2','0.4')]:
 record('complex-spectral-'+str(ss),spectral_direct(ss,mp.mpf('.4')),spectral(ss,mp.mpf('.4')))

for q in range(4):
 for n in [1,4,9]:
  lhs=mp.fsum(mp.log(k)**q/k for k in range(1,n+1))
  rhs=mp.stieltjes(q)-mp.stieltjes(q,n+1)
  record(f'Stieltjes-difference-q{q}-M{n}',lhs,rhs)

for q in range(4):
 x=mp.mpf('.4');Ls=[[mp.mpf(0)]*3 for _ in range(q+1)];ans=mp.mpf(0)
 for m in range(1,270):
  for a in range(q+1):
   for j in range(3):Ls[a][j]+=mp.log(m)**a/mp.mpf(m)**(j+1)
  term=mp.fsum(mp.binomial(q,a)*(Ls[a][2]*Ls[q-a][0]-Ls[a][1]*Ls[q-a][1]) for a in range(q+1))
  ans+=term*x**m
 rhs=(-1)**q*mp.diff(lambda s:spectral(s,x),mp.mpf(3),q)
 record(f'all-order-Stieltjes-generator-q{q}',ans,rhs)

# An independent ordinary Mellin integral for each depth-two zeta value.
def mzv2(a,b):
 f=lambda t:t**(a-1)*mp.polylog(b,mp.exp(-t))/mp.expm1(t)
 return mp.quad(f,[0,mp.mpf('.3'),1,4,12,mp.inf])/mp.gamma(a)
v41=mzv2(4,1);v23=mzv2(2,3);v32=mzv2(3,2)
record('Euler-height-one',v41,2*mp.zeta(5)-mp.zeta(2)*mp.zeta(3))
record('Euler-zeta23',v23,mp.mpf(9)/2*mp.zeta(5)-2*mp.zeta(2)*mp.zeta(3))
record('Euler-zeta32',v32,3*mp.zeta(2)*mp.zeta(3)-mp.mpf(11)/2*mp.zeta(5))
record('harmonic-determinant-endpoint',v41+v23-2*v32,mp.mpf(35)/2*mp.zeta(5)-9*mp.zeta(2)*mp.zeta(3))

# Shifted double-pole Euler primitive, kept jointly at the origin.
def double_integrand(x):
 L=-mp.log1p(-x)
 return ((3*x-2)*mp.polylog(2,x)+(1-x)*(3*L-L**2)-x)/(2*x*x)
record('shifted-double-pole-endpoint',mp.quad(double_integrand,[0,mp.mpf('.2'),mp.mpf('.7'),1]),(5*mp.zeta(3)-3*mp.zeta(2)-1)/2)

(root/'data'/'numeric_checks.json').write_text(json.dumps({'working_decimal_precision':mp.mp.dps,'truncation_settings':{'cutoff_determinants':320,'hyperlog_taylor_degree':360,'spectral_nested_series':270,'Stieltjes_generator_cutoff':269,'Mellin_integral_breakpoints':['0','0.3','1','4','12','infinity']},'kind':'floating-point diagnostics, not interval certificates','checks':checks,'largest_scaled_residual':mp.nstr(max(mp.mpf(c['scaled_residual']) for c in checks),12)},indent=2))
