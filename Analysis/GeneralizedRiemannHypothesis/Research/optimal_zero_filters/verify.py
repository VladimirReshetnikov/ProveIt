#!/usr/bin/env python3
"""Numerical illustrations only; the proofs in paper.tex are analytic."""
import json
import mpmath as mp
mp.mp.dps = 65

def fmt(x):
    return mp.nstr(x, 32)

def poly_mul(p,q):
    a=[mp.mpf(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): a[i+j]+=x*y
    return a

def filter_pair(m):
    a,b=[mp.im(mp.zetazero(j)) for j in (1,2)]
    h=2*mp.pi/(a+b)
    p=[mp.mpf(1)]
    for _ in range(m): p=poly_mul(p,[1,-2*mp.cos(a*h),1])
    # Direct Mellin averaging for beta=1/2 (not the untilted Fourier weights).
    w=[c*mp.exp(-j*h/2) for j,c in enumerate(p)]
    w=[c/sum(w) for c in w]
    nodes=[j*h for j in range(2*m+1)]
    error=max(abs(sum(wj*t**k*mp.exp((mp.mpf('0.5')+1j*g)*t) for wj,t in zip(w,nodes)))
              for g in (a,b) for k in range(m))
    assert error < mp.mpf('1e-58')
    return {'m':m,'gamma1':fmt(a),'gamma2':fmt(b),'width':fmt(2*m*h),
            'scale_ratio':fmt(mp.exp(2*m*h)), 'separate_filter_width':fmt(m*mp.pi*(1/a+1/b)),
            'nodes':[fmt(t) for t in nodes], 'weights':[fmt(x) for x in w], 'max_jet_residual':fmt(error)}

def solve_triple(e):
    # Dimensionless h=1. At e=0, a=(2pi/3,pi,4pi/3)i.
    # Move a single frequency and a single real part; this breaks mirror symmetry.
    a=[2j*mp.pi/3+e/3,1j*(mp.pi+e),4j*mp.pi/3]
    def eq(*v):
        w=v[:4]; t=(mp.mpf(0),)+v[4:]
        out=[sum(w)-1]
        for aj in a:
            r=sum(wj*mp.exp(aj*tj) for wj,tj in zip(w,t))
            out.extend([mp.re(r),mp.im(r)])
        return tuple(out)
    guess=(mp.mpf(1)/6,mp.mpf(1)/3,mp.mpf(1)/3,mp.mpf(1)/6,1,2,3)
    sol=list(mp.findroot(eq,guess,tol=mp.mpf('1e-60'),maxsteps=50))
    w=sol[:4]; t=[mp.mpf(0)]+sol[4:]
    assert min(w)>0 and all(x<y for x,y in zip(t,t[1:]))
    residual=max(abs(r) for r in eq(*sol))
    assert residual<mp.mpf('1e-55')
    # Build the dual using SVD of the 6x6 homogeneous system (numerical diagnostic).
    def row(x,der=False):
        v=[]
        for aj in a:
            z=mp.exp(aj*x)*(aj if der else 1)
            v.extend([mp.re(z),mp.im(z)])
        return v
    # Discard evaluation at 0 using the positive weighted row relation.
    M=mp.matrix([row(x) for x in t[1:]]+[row(x,True) for x in t[1:-1]])
    # Set last coefficient to 1, solve other five (pivot by trying all choices).
    v=None
    for j in range(6):
        cols=[k for k in range(6) if k!=j]
        try:
            z=mp.lu_solve(mp.matrix([[M[r,k] for k in cols] for r in range(5)]),mp.matrix([-M[r,j] for r in range(5)]))
        except ZeroDivisionError: continue
        v=[mp.mpf(0)]*6; v[j]=mp.mpf(1)
        for k,val in zip(cols,z): v[k]=val
        break
    assert v is not None
    def g(x): return sum(a*b for a,b in zip(v,row(x)))
    if g(t[-1]/7)<0: v=[-z for z in v]
    grid_min=min(g(t[-1]*j/400) for j in range(401))
    # Not an interval proof: exact certificate positivity follows from the analytic local theorem.
    assert grid_min > -mp.mpf('1e-50')
    return {'epsilon':fmt(e),'width':fmt(t[-1]),'linear_prediction':fmt(3-e/mp.pi),
            'scaled_quadratic_error':fmt((t[-1]-3+e/mp.pi)/e**2),
            'nodes':[fmt(x) for x in t], 'weights':[fmt(x) for x in w],
            'max_moment_residual':fmt(residual),'sampled_dual_minimum':fmt(grid_min)}

if __name__=='__main__':
    data={'note':'High-precision numerical checks, not interval certificates or proof of global optimality.',
          'zeta_pairs':[filter_pair(m) for m in (1,2,3,5)],
          'perturbed_triple':[solve_triple(mp.mpf(x)) for x in ('0.01','0.001','0.0001','-0.001')]}
    print(json.dumps(data,indent=2))
