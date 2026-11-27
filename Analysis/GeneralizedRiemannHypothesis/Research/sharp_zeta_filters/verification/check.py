#!/usr/bin/env python3
"""Reproduce finite illustrative checks; not a certified zero computation or proof."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb, exp, log, sqrt
import csv, json
import mpmath as mp
import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent

def mul(a,b):
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return out

# Exact generating-series check, including a repeated characteristic root and
# a root of modulus strictly less than one (normalization in Lemma 3.1).
roots=[Q(1), Q(1), Q(-1), Q(1,2), Q(1,2)]
n=len(roots)
D=[Q(1)]
for z in roots: D=mul(D,[Q(1),-z])
a=[Q(3),Q(-7),Q(2),Q(8),Q(1)]
for k in range(n,80): a.append(-sum(D[j]*a[k-j] for j in range(1,n+1)))
b=mul(D,a)[:n]
assert all(v==0 for v in mul(D,a)[n:len(a)])
# Reciprocal coefficients as sums of complete homogeneous symmetric monomials.
h=[Q(1)]
for k in range(1,80): h.append(-sum(D[j]*h[k-j] for j in range(1,min(n,k)+1)))
assert all(abs(v)<=comb(k+n-1,n-1) for k,v in enumerate(h))
assert mul(b,h)[:80]==a
assert all(abs(v)<=n*2**n*comb(k+n-1,n-1)*max(map(abs,a[:n])) for k,v in enumerate(a))

# Constant margin in Lemma 3.2: use logs to avoid underflow. The proof
# analytically bounds D_n by exp(-184 n) for every integer n >= 1.
constant_tests=[]
for n in [1,2,3,10,100,1000,10**6,10**9]:
    H=log(16*sqrt(n)); h0=H/2
    logD=log(512*n*n/(h0*(512*n-n/H-.5)))+n*log(16*exp(1))+.5*H-256*n+64*sqrt(n)
    assert logD < -100*n
    constant_tests.append({'n':n,'log_D_over_n':logD/n})

# Numerical illustrations: positive symmetric atomic quadrature from known
# approximate zeros. Only simple moment constraints at those numerical
# ordinates are imposed; this is NOT an exhaustive or rigorous zero census.
mp.mp.dps=35
zeros=[float(mp.im(mp.zetazero(k))) for k in range(1,13)]
xi0=float(mp.mpf('0.5')*mp.mpf('0.5')*(-mp.mpf('0.5'))*mp.pi**(-mp.mpf('0.25'))*mp.gamma(mp.mpf('0.25'))*mp.zeta(mp.mpf('0.5')))
target=1/(2*xi0)
examples=[]
with (HERE/'quadrature_nodes.csv').open('w', newline='') as f:
    writer=csv.writer(f); writer.writerow(['number_of_ordinates','nonnegative_node','pair_mass'])
    for count in [4,8,12]:
        gammas=np.array(zeros[:count]); B=gammas[-1]
        H=log(16*sqrt(2*count+3)); nodes=np.linspace(0,H,1801)
        A=np.vstack([np.ones(len(nodes)),np.cosh(nodes/2),np.cos(gammas[:,None]*nodes[None,:])]); rhs=np.array([1,target]+[0]*count)
        # Minimize the second moment, with no assertion of optimality in width.
        sol=linprog(nodes**2,A_eq=A,b_eq=rhs,bounds=(0,None),method='highs')
        assert sol.success,sol.message
        nz=np.where(sol.x>1e-13)[0]; residual=float(np.max(np.abs(A@sol.x-rhs)))
        assert residual<1e-7 and np.min(sol.x)>=-1e-12
        for j in nz: writer.writerow([count,format(nodes[j],'.17g'),format(sol.x[j],'.17g')])
        examples.append({'ordinates':count,'last_ordinate':B,'theoretical_half_width_for_this_moment_count':H,'max_used_node':float(nodes[nz[-1]]),'nonnegative_nodes':len(nz),'max_moment_residual':residual,'mass':float(sum(sol.x))})

# Numerical checks of the theta Fourier normalization. The truncation
# [0,3] and 8 summands suffice for this illustrative precision.
def phi(t):
    return sum((4*mp.pi**2*m**4*mp.exp(mp.mpf('4.5')*t)-6*mp.pi*m*m*mp.exp(mp.mpf('2.5')*t))*mp.exp(-mp.pi*m*m*mp.exp(2*t)) for m in range(1,9))
def xi(z):
    s=mp.mpf('0.5')+1j*z
    return s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)/2
checks=[]
for y in [0,1,10]:
    numerical=2*mp.quad(lambda t:phi(t)*mp.cos(y*t),[0,0.5,1,2,3]); exact=xi(y)
    error=abs(numerical-exact); assert error<mp.mpf('1e-23')
    checks.append({'y':y,'absolute_error':str(error)})

result={'status':'finite recurrence exact over Q; other checks numerical and illustrative, not certified proofs',
        'exact_recurrence_terms_checked':len(a),'constant_tests':constant_tests,
        'theta_transform_checks':checks,'xi_at_half':xi0,'target_cosh_moment':target,
        'approximate_ordinates':zeros,'quadrature_examples':examples}
(HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
