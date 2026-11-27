#!/usr/bin/env python3
"""Reproducible sanity checks; numerical examples are not used in the proof."""
import json
import math
import sympy as sp
import mpmath as mp

mp.mp.dps = 65
z = sp.symbols('z')
# Exact rational example alpha=1, beta=2, each twice.
p = sp.expand((1+z+z*z)**2/9)
assert p.subs(z,1) == 1
assert sp.rem(p, 1+z+z*z, z) == 0
assert sp.rem(sp.diff(p,z), 1+z+z*z, z) == 0
assert [p.coeff(z,j) for j in range(5)] == [sp.Rational(k,9) for k in [1,2,3,2,1]]

# Exact symmetric multi-cluster example: center 12, frequencies 10, 12, 14,
# orders (1,2,1). delta*N/kappa=2/3<1, cos(pi/6)=sqrt(3)/2.
p2=sp.expand((1+z)**2*(1+sp.sqrt(3)*z+z*z)/(4*(2+sp.sqrt(3))))
assert sp.simplify(p2.subs(z,1)-1)==0
assert sp.simplify(p2.subs(z,-1))==0 and sp.simplify(sp.diff(p2,z).subs(z,-1))==0
assert sp.rem(p2,z*z+sp.sqrt(3)*z+1,z)==0

def fmt(x): return mp.nstr(x, 25)

def solve_cluster(spec):
    """Numerically solve all complex moment equations with left endpoint 0."""
    freqs=[(mp.mpf(f),m) for f,m in spec]
    n=sum(m for _,m in freqs)
    k=sum(f*m for f,m in freqs)/n
    guess=[mp.mpf(math.comb(n,j))/2**n for j in range(n+1)] + [j*mp.pi/k for j in range(1,n+1)]
    def equations(*args):
        w=args[:n+1]; t=(mp.mpf(0),)+args[n+1:]
        result=[sum(w)-1]
        for f,m in freqs:
            for d in range(m):
                v=sum(wj*tj**d*mp.exp(mp.j*f*tj) for wj,tj in zip(w,t))
                result.extend([v.real,v.imag])
        return result
    sol=list(mp.findroot(equations,guess,tol=mp.mpf('1e-56'),maxsteps=100))
    w=sol[:n+1]; t=[mp.mpf(0)]+sol[n+1:]
    assert min(w)>0 and all(t[j]<t[j+1] for j in range(n))
    res=max(map(abs,equations(*sol)))
    assert res<mp.mpf('1e-48')
    return {'frequencies_and_orders':spec,'nodes':[fmt(v) for v in t], 'weights':[fmt(v) for v in w],
            'max_moment_residual':fmt(res),'diameter':fmt(t[-1]),'N_pi_over_mean':fmt(n*mp.pi/k),
            'difference':fmt(t[-1]-n*mp.pi/k)}

results={'exact_pair_weights':[str(p.coeff(z,j)) for j in range(5)],
         'exact_symmetric_cluster_weights':[str(sp.simplify(p2.coeff(z,j))) for j in range(5)],
         'numerical_nonsymmetric_clusters':[solve_cluster([('0.98',1),('1.00',1),('1.05',1)]),
             solve_cluster([('0.98',2),('1.01',1),('1.06',1)])]}
# Illustrative first two positive zeta zero ordinates (mpmath, not certified).
a=mp.zetazero(1).imag; b=mp.zetazero(2).imag
T=2*mp.pi/(a+b); c=mp.cos(T*a); w=[1,-4*c,2+4*c*c,-4*c,1]; w=[v/sum(w) for v in w]
results['zeta_example']={'ordinates':[fmt(a),fmt(b)],'grid_spacing':fmt(T),'diameter':fmt(4*T),
 'individual_convolution_diameter':fmt(2*mp.pi*(1/a+1/b)), 'weights':[fmt(v) for v in w],
 'status':'Illustrative numerical values only; theorem holds for exact ordinates.'}
print(json.dumps(results,indent=2))
