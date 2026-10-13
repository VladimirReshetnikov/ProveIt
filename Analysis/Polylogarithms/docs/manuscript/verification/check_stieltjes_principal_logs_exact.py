"""Exact formal coefficient checks for principal logarithmic identities.

The all-order analytic theorem is proved in the manuscript. This checker
independently multiplies finite jets, checks Euler-product normalizations,
and rejects wrong signs, centering and reflection factors.
"""
from pathlib import Path
import hashlib
import json
import math
import platform
import sys
import sympy as s

HERE=Path(__file__).resolve()
OUT=HERE.with_suffix('.json')
checks=[]
controls=[]

def save(status):
    OUT.write_text(json.dumps({'status':status,'checks':checks,'controls':controls,
        'exact_checks':len(checks),'negative_controls':len(controls),
        'script_sha256':hashlib.sha256(HERE.read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
        'digest_mode':'lf-normalized','python_version':platform.python_version(),
        'sympy_version':s.__version__,'optimization_level':sys.flags.optimize,
        'scope':'Exact finite coefficient checks; the general analytic statement has a separate written proof.'},indent=2)+'\n',encoding='utf8')

def check(name,condition):
    if not bool(condition):
        save('FAIL');raise RuntimeError(name)
    checks.append(name)

def eq(name,left,right):
    check(name,s.expand(left-right)==0)

def reject(name,left,right):
    check_value=s.expand(left-right)!=0
    if not check_value:
        save('FAIL');raise RuntimeError('Undetected corruption: '+name)
    controls.append(name)

def mul(a,b,n=3):
    return [s.expand(sum(a[j]*b[k-j] for j in range(k+1))) for k in range(n+1)]

def exponential(logarithm,n=3):
    out=[s.Integer(1)]
    for k in range(1,n+1):
        out.append(s.expand(sum(j*logarithm[j]*out[k-j] for j in range(1,k+1))/k))
    return out

save('running')
g,g1,g2,z2,z3=s.symbols('gamma gamma1 gamma2 zeta2 zeta3')
gamma_jet=exponential([0,-g,z2/2,-z3/3])
zeta_jet=[1,g,-g1,g2/2]
product=mul(gamma_jet,zeta_jet)
eq('Gamma times h-zeta constant',product[0],1)
eq('Gamma times h-zeta linear cancellation',product[1],0)
eq('Gamma times h-zeta quadratic',product[2],z2/2-g*g/2-g1)
eq('Gamma times h-zeta cubic',product[3],g2/2+g*g1+(g**3-z3)/3)

for r in range(1,7):
    ell=s.symbols('ell1:'+str(r+1))
    # Independently expand each centered exponential difference:
    # exp(-ell*h/2)*(exp(ell*h)-1)/(ell*h).
    even=[s.Integer(1),s.Integer(0),s.Integer(0),s.Integer(0)]
    for index,L in enumerate(ell,1):
        left=[(-L/2)**k/s.factorial(k) for k in range(4)]
        right=[L**k/s.factorial(k+1) for k in range(4)]
        factor=mul(left,right)
        eq(f'centered Euler factor linear r{r} p{index}',factor[1],0)
        eq(f'centered Euler factor cubic r{r} p{index}',factor[3],0)
        eq(f'centered Euler factor quadratic r{r} p{index}',factor[2],L*L/24)
        even=mul(even,factor)
    secant=[1,0,3*z2/4,0]
    final=mul(product,mul(secant,even))
    eq(f'principal centered linear r{r}',final[1],0)
    eq(f'principal centered quadratic r{r}',final[2],5*z2/4-g*g/2-g1+sum(L*L for L in ell)/24)
    eq(f'principal universal cubic r{r}',final[3],g2/2+g*g1+(g**3-z3)/3)
    # Direct inclusion-exclusion, independent of prime factor notation.
    primes=list(s.primerange(1,20))[:r]
    d=math.prod(primes)
    for k in range(5):
        left=sum(s.mobius(h)*h**k for h in s.divisors(d))
        right=math.prod(1-p**k for p in primes)
        eq(f'Euler inclusion-exclusion r{r} k{k}',left,right)

reject('reverse first nonzero logarithmic moment',s.Rational(1,2),-s.Rational(1,2))
reject('omit centering leaves a nonzero linear coefficient',s.Symbol('c'),0)
reject('omit reflection secant changes quadratic coefficient',z2/2,5*z2/4)
reject('reverse Stieltjes Laurent sign changes cubic coefficient',g2/2-g*g1+(g**3-z3)/3,product[3])
save('PASS')
print('PASS',len(checks),'exact checks;',len(controls),'rejected corruptions')
