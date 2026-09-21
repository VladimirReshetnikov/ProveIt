#!/usr/bin/env python3
"""Reproducible algebraic and numerical checks for the accompanying article.

Requires Python 3.10+, SymPy, NumPy.  These are checks, not a formal proof.
Run: python verify_results.py
"""
from __future__ import annotations
import math
import sys
import numpy as np
import sympy as sp


def symbolic_checks() -> None:
    x, r, u, v, a, b = sp.symbols('x r u v a b', real=True)
    rho2 = (x-u)**2 + (r-v)**2
    s = sp.log(rho2)/2
    ell = x*a+b
    P = ((r-v)*a/rho2 + s*a/r + (x-u)*ell/(r*rho2))/sp.pi
    Q = ((x-u)*a/rho2 + s*ell/r**2 - (r-v)*ell/(r*rho2))/sp.pi
    checks = {
        'Vekua equation 1': sp.diff(P,x)-sp.diff(Q,r)-2*Q/r,
        'Vekua equation 2': sp.diff(Q,x)+sp.diff(P,r),
        'closed omega': (sp.diff(Q,x)+sp.diff(P,r))/2,
        'closed theta': (sp.diff(r*P-x*Q,x)-sp.diff(x*P+r*Q,r))/2,
    }
    z, p, aa, bb = sp.symbols('z p a b')
    H_expected = aa/(2*sp.pi*sp.I*(z-p))-(p*aa+bb)/(2*sp.pi*sp.I*(z-p)**2)
    F = (z*aa+bb)*sp.log(z-p)/(2*sp.pi*sp.I)
    checks['second derivative of affine-log primitive'] = sp.diff(F,z,2)-H_expected
    checks['first residue of second derivative'] = sp.residue(H_expected,z,p)-aa/(2*sp.pi*sp.I)
    checks['first moment residue of second derivative'] = sp.residue(z*H_expected,z,p)+bb/(2*sp.pi*sp.I)
    for label, expr in checks.items():
        value = sp.simplify(expr)
        if value != 0:
            raise AssertionError(f'{label}: nonzero symbolic residual {value}')
        print(f'PASS: {label}; exact residual 0')


def generator(x: np.ndarray, r: np.ndarray, p: complex,
              a: np.ndarray, b: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Quaternion-valued coefficients P,Q of the branch-free generator."""
    x = np.asarray(x, dtype=float)
    r = np.asarray(r, dtype=float)
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    if a.shape != (4,) or b.shape != (4,):
        raise ValueError('Quaternion coefficients must have shape (4,).')
    rho2 = (x-p.real)**2+(r-p.imag)**2
    if np.any(r <= 0) or np.any(rho2 <= 0):
        raise ValueError('Require r>0 and z != p.')
    s = np.log(rho2)/2
    ell = x[..., None]*a+b
    P = (((r-p.imag)/rho2)[...,None]*a
         +(s/r)[...,None]*a
         +((x-p.real)/(r*rho2))[...,None]*ell)/np.pi
    Q = (((x-p.real)/rho2)[...,None]*a
         +(s/r**2)[...,None]*ell
         -((r-p.imag)/(r*rho2))[...,None]*ell)/np.pi
    return P, Q


def periods(center: complex, radius: float, p: complex,
            a: np.ndarray, b: np.ndarray, reflected: bool = False,
            n: int = 16384) -> tuple[np.ndarray, np.ndarray]:
    t = 2*np.pi*np.arange(n)/n
    x, r = center.real+radius*np.cos(t), center.imag+radius*np.sin(t)
    dx, dr = -radius*np.sin(t), radius*np.cos(t)
    P,Q = generator(x,r,p,a,b)
    if reflected:
        Pm,Qm = generator(x,r,p.conjugate(),a,b)
        P,Q = P-Pm,Q-Qm
    omega = (-P*dx[:,None]+Q*dr[:,None])/2
    theta = ((x[:,None]*P+r[:,None]*Q)*dx[:,None]
             +(r[:,None]*P-x[:,None]*Q)*dr[:,None])/2
    return 2*np.pi*np.mean(omega,axis=0),2*np.pi*np.mean(theta,axis=0)


def qmul(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return np.r_[a[0]*b[0]-np.dot(a[1:],b[1:]),
                 a[0]*b[1:]+b[0]*a[1:]+np.cross(a[1:],b[1:])]


def spherical_norm(P: np.ndarray,Q: np.ndarray) -> np.ndarray:
    """Exact supremum over imaginary units, without angular sampling."""
    scalar = P[...,0]*Q[...,0]+np.sum(P[...,1:]*Q[...,1:],axis=-1)
    prod_norm_squared = np.sum(P*P,axis=-1)*np.sum(Q*Q,axis=-1)
    imag_norm = np.sqrt(np.maximum(0.,prod_norm_squared-scalar**2))
    return np.sqrt(np.sum(P*P,axis=-1)+np.sum(Q*Q,axis=-1)+2*imag_norm)


def numerical_checks() -> None:
    p=complex(0.3,1.7)
    one=np.array([1.,0.,0.,0.]); zero=np.zeros(4)
    ag=np.array([1.,-2.,.5,3.]); bg=np.array([-.4,1.,2.,-1.])
    cases=[('first period generator',p,.2,one,zero,False,one,zero),
           ('second period generator',p,.2,zero,one,False,zero,one),
           ('general quaternion pair',p,.2,ag,bg,False,ag,bg),
           ('reflected generator',p,.2,ag,bg,True,ag,bg),
           ('zero winding circle',complex(2.,1.7),.2,ag,bg,False,zero,zero)]
    print('\nPeriod quadrature (16384-point periodic trapezoid):')
    for label,center,radius,a,b,refl,expected_a,expected_b in cases:
        got_a,got_b=periods(center,radius,p,a,b,refl)
        error=max(np.max(np.abs(got_a-expected_a)),np.max(np.abs(got_b-expected_b)))
        if not error < 2e-11:
            raise AssertionError(f'{label}: error {error:g}')
        print(f'PASS: {label}; max component error {error:.3e}')
        print('  omega =',np.array2string(got_a,precision=12))
        print('  theta =',np.array2string(got_b,precision=12))
    beta=(p.real*ag+bg)/p.imag
    expected=float(spherical_norm(beta[None,:],ag[None,:])[0]/np.pi)
    print('\nCritical-growth asymptotic, general quaternion residue pair:')
    print(f'Predicted limit: {expected:.12f}')
    t=2*np.pi*np.arange(2048)/2048
    errors=[]
    for rho in [1e-2,1e-3,1e-4,1e-5,1e-6]:
        x=p.real+rho*np.cos(t); r=p.imag+rho*np.sin(t)
        P,Q=generator(x,r,p,ag,bg)
        got=rho*np.max(spherical_norm(P,Q))
        error=abs(got-expected); errors.append(error)
        print(f'rho={rho:.0e}: scaled maximum={got:.12f}; error={error:.3e}')
    if not (errors[-1]<1e-4 and errors[-1]<errors[0]):
        raise AssertionError('Critical-growth convergence check failed.')
    print('PASS: sampled radial convergence to the proved asymptotic constant')


def main() -> int:
    print('VERIFICATION OF GLOBAL FUETER PRIMITIVES AND SPHERICAL PRINCIPAL PARTS')
    print(f'Python {sys.version.split()[0]}, SymPy {sp.__version__}, NumPy {np.__version__}\n')
    symbolic_checks()
    numerical_checks()
    print('\nAll checks passed. Analytical proofs are in the article; this is not formal verification.')
    return 0

if __name__=='__main__':
    raise SystemExit(main())
