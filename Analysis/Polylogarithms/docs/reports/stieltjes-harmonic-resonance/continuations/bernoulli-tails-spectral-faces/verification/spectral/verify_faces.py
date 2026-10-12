#!/usr/bin/env python3
"""Independent numerical checks of the simplex face decomposition.

The spectral side is a finite ordinary sum plus an asymptotic Hurwitz tail.
The triple-face side uses Gamma values in geometric quadrature, not that tail.
Edge integrals use integrated polynomial expansions for stable endpoints.
These are numerical diagnostics, not interval certificates.
"""
import itertools
import json
from pathlib import Path
import mpmath as mp
import numpy as np
from scipy.special import loggamma, roots_legendre

mp.mp.dps = 65
A = mp.mpf(2)
MASSES = tuple(map(mp.mpf, ('0.2', '0.7', '1.3')))
R = len(MASSES)


def zeta_prime(s, a):
    return mp.diff(lambda u: mp.zeta(u, a), s)


def convolution(a, b, maxdegree):
    out = [mp.mpf(0)] * (maxdegree + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i+j <= maxdegree:
                out[i+j] += x*y
    return out


def direct_delta3(head=70, degree=15):
    total=mp.mpf(0)
    for n in range(head):
        x=A+n
        ls=[mp.log1p(B/x**2) for B in MASSES]
        var=sum((ls[i]-ls[j])**2 for i,j in itertools.combinations(range(R),2))
        total -= 6*R*mp.log(x)*var+R**2*sum(l**3 for l in ls)-sum(ls)**3
    rows=[[mp.mpf(0)]+[(-1)**(k+1)*B**k/k for k in range(1,degree+1)] for B in MASSES]
    variance=[mp.mpf(0)]*(degree+1)
    for i,j in itertools.combinations(range(R),2):
        d=[rows[i][k]-rows[j][k] for k in range(degree+1)]
        sq=convolution(d,d,degree)
        variance=[x+y for x,y in zip(variance,sq)]
    row_sum=[sum(row[k] for row in rows) for k in range(degree+1)]
    cube_sum=convolution(convolution(row_sum,row_sum,degree),row_sum,degree)
    indiv_cubes=[convolution(convolution(row,row,degree),row,degree) for row in rows]
    cubic=[R**2*sum(row[k] for row in indiv_cubes)-cube_sum[k] for k in range(degree+1)]
    for k in range(2,degree+1):
        total += 6*R*variance[k]*zeta_prime(2*k,A+head)-cubic[k]*mp.zeta(2*k,A+head)
    return total


def coefficients(degree):
    first=[mp.mpf(0)]
    second=[mp.mpf(0)]
    for n in range(1,degree+1):
        sign=(-1)**n
        zz=mp.zeta(2*n,A)
        zp=zeta_prime(2*n,A)
        first.append(sign*zz/n)
        second.append(sign*(2*mp.harmonic(n-1)*zz+4*zp)/n)
    return first,second


def edge_integrals(coef, B, C):
    """Return ∫H/(u(1-u)) and ∫H log(u(1-u))/(u(1-u))."""
    degree=len(coef)-1
    b=[sum(coef[n]*mp.binomial(n,k)*C**(n-k)*(B-C)**k
            for n in range(k,degree+1)) for k in range(degree+1)]
    I=mp.mpf(0); J=mp.mpf(0)
    for k in range(2,degree+1):
        h=mp.harmonic(k-1)
        h2=sum(mp.mpf(1)/j**2 for j in range(1,k))
        I -= b[k]*h
        J += b[k]*(h*h+3*h2)/2
    return I,J


def gamma_first(B):
    """Remove the mass-independent constant, which every H_S kills."""
    return 2*np.real(loggamma(float(A)+1j*np.sqrt(B)))-2*float(mp.loggamma(A))


def triangle_gamma(order):
    nodes, weights=roots_legendre(order)
    us=(nodes+1)/2
    ws=weights/2
    u=us[:,None]
    v=us[None,:]
    w=ws[:,None]*ws[None,:]
    base=np.stack(np.broadcast_arrays(np.ones_like(u*v),u,u*v),axis=-1)
    t=base/np.sum(base,axis=-1)[...,None]
    ans=0.0
    Bs=np.array([float(x) for x in MASSES])
    vertices=gamma_first(Bs)
    for perm in itertools.permutations(range(3)):
        b=Bs[list(perm)]
        vert=vertices[list(perm)]
        value=gamma_first(np.sum(t*b,axis=-1))+np.sum(t*vert,axis=-1)
        for i,j in itertools.combinations(range(3),2):
            tij=t[...,i]+t[...,j]
            arg=(t[...,i]*b[i]+t[...,j]*b[j])/tij
            value -= tij*gamma_first(arg)
        ans += np.sum(w*value/(u*v))
    return float(ans)


def polynomial_triangle(order=64):
    nodes,weights=roots_legendre(order)
    us=(nodes+1)/2; ws=weights/2
    u=us[:,None];v=us[None,:];w=ws[:,None]*ws[None,:]
    t=np.stack(np.broadcast_arrays(np.ones_like(u*v),u,u*v),axis=-1)
    t/=np.sum(t,axis=-1)[...,None]
    ans=0.0
    Bs=np.array([float(x) for x in MASSES])
    for perm in itertools.permutations(range(3)):
        b=Bs[list(perm)]
        # Stable algebraic form of H_3(B^2).
        H=np.prod(t,axis=-1)*sum((b[i]-b[j])**2/(t[...,i]+t[...,j])
                               for i,j in itertools.combinations(range(3),2))
        ans+=np.sum(w*H/(u*v))
    expected=sum((Bs[i]-Bs[j])**2 for i,j in itertools.combinations(range(3),2))
    return float(ans),float(expected)


def zerojet_partial_fraction_check():
    """Compare rational Dirichlet moment and fractional-coefficient residues."""
    r=3; h=4
    masses=MASSES
    def M(s):
        # Exact polynomial coefficient convolution.
        coeff=[mp.mpf(1)]+[mp.mpf(0)]*h
        for B in masses:
            row=[mp.rf(s,k)*B**k/mp.factorial(k) for k in range(h+1)]
            coeff=convolution(coeff,row,h)
        return mp.factorial(h)*coeff[h]/mp.rf(r*s,h)
    # Differentiate at a nonzero point and compare partial fractions there.
    s0=mp.mpf('0.07')
    residues=[]
    for j in range(1,h):
        coeff=[mp.mpf(1)]+[mp.mpf(0)]*h
        for B in masses:
            row=[mp.rf(-mp.mpf(j)/r,k)*B**k/mp.factorial(k) for k in range(h+1)]
            coeff=convolution(coeff,row,h)
        residues.append((-1)**j*mp.factorial(h)*coeff[h]/(mp.factorial(j)*mp.factorial(h-1-j)))
    errors=[]
    for m in (1,2,3,5):
        lhs=-mp.diff(M,s0,m)
        rhs=sum(-mp.factorial(m)*(-r)**m*residues[j-1]/(r*s0+j)**(m+1)
                for j in range(1,h))
        errors.append(mp.nstr(abs(lhs-rhs),6))
    return errors


def main():
    direct1=direct_delta3(55,13)
    direct2=direct_delta3(85,17)
    out={'a':str(A),'masses':[str(x) for x in MASSES],
         'direct_delta3_55_13':mp.nstr(direct1,55),
         'direct_delta3_85_17':mp.nstr(direct2,55),
         'direct_tail_stability':mp.nstr(abs(direct1-direct2),6)}
    face_values=[]
    for degree in (42,64):
        first,second=coefficients(degree)
        I2=sum(edge_integrals(second,B,C)[0] for B,C in itertools.combinations(MASSES,2))
        J1=sum(edge_integrals(first,B,C)[1] for B,C in itertools.combinations(MASSES,2))
        row={'degree':degree,'sum_pair_I_E2':mp.nstr(I2,45),'sum_pair_J_E1':mp.nstr(J1,45)}
        if degree==64:
            quad=[]
            for order in (24,48,96,192):
                triple=triangle_gamma(order)
                result=-3*R*I2-6*J1-6*mp.mpf(triple)
                quad.append({'order':order,'triple_gamma_integral':triple,
                             'delta3_faces':mp.nstr(result,30),
                             'difference_from_spectral':mp.nstr(abs(result-direct2),8)})
            row['quadrature']=quad
        face_values.append(row)
    out['face_formula']=face_values
    pq,pe=polynomial_triangle()
    out['quadratic_face_identity']={'quadrature':pq,'exact':pe,'error':abs(pq-pe)}
    out['zerojet_partial_fractions_errors_at_s_0_07']=zerojet_partial_fraction_check()
    path=Path(__file__).with_name('verification_faces.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
