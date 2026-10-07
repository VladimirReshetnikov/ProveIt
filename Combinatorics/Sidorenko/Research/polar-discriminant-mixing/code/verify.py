#!/usr/bin/env python3
"""Exact finite checks for Exact restriction laws and Fourier cancellation.

Run: python code/verify.py
Requires Python >=3.10 and NumPy. All pass/fail comparisons are exact integers
or fractions. Direct field enumeration uses F_3 only. Values q=9,25 in the
formula sweep are symbolic prime-power evaluations, not arithmetic modulo q.
These finite checks supplement, and do not replace, the mathematical proofs.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import prod
import sys
import numpy as np
from exact_formulas import b, gb, p, mu, rho, moments, variances, grassmann_variances, common_moments


def sym_matrices(n: int, q: int = 3) -> np.ndarray:
    """Enumerate all symmetric matrices over a prime field, using integer lifts."""
    if q != 3:
        raise ValueError('This independent enumerator is deliberately restricted to F_3.')
    ij = list(combinations(range(n), 2)) + [(i, i) for i in range(n)]
    vals = np.array(list(product(range(q), repeat=len(ij))), dtype=np.int64)
    mats = np.zeros((len(vals), n, n), dtype=np.int64)
    for col, (i, j) in enumerate(ij):
        mats[:, i, j] = vals[:, col]
        mats[:, j, i] = vals[:, col]
    return mats


def determinants(mats: np.ndarray, q: int = 3) -> np.ndarray:
    """Exact Leibniz determinant; only sizes <=4 are used."""
    n = mats.shape[-1]
    out = np.zeros(mats.shape[:-2], dtype=np.int64)
    for perm in permutations(range(n)):
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(n) for j in range(i+1,n))
        term = np.ones(out.shape, dtype=np.int64)
        for i in range(n):
            term *= mats[..., i, perm[i]]
        out += sign * term
    return out % q


def statistics(mats: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    det = determinants(mats)
    return (det != 0).astype(np.int64), np.array([0, 1, -1], dtype=np.int64)[det]


def rank_mod(a: np.ndarray, q: int = 3) -> int:
    a = a.copy() % q
    rank = 0
    for col in range(a.shape[1]):
        piv = next((i for i in range(rank, len(a)) if a[i,col]), None)
        if piv is None:
            continue
        a[[rank,piv]] = a[[piv,rank]]
        a[rank] = (a[rank] * pow(int(a[rank,col]), -1, q)) % q
        for i in range(len(a)):
            if i != rank:
                a[i] = (a[i] - a[i,col] * a[rank]) % q
        rank += 1
        if rank == len(a):
            break
    return rank


def all_rref(n: int, k: int, q: int = 3):
    for pivots in combinations(range(n), k):
        free = [(i,j) for i in range(k) for j in range(n)
                if j not in pivots and j > pivots[i]]
        for values in product(range(q), repeat=len(free)):
            mat = np.zeros((k,n), dtype=np.int64)
            for i,j in enumerate(pivots):
                mat[i,j] = 1
            for ij,v in zip(free, values):
                mat[ij] = v
            yield mat


def exact_joint(r: int, s: int, t: int, xi: int, eta: int, q: int = 3) -> F:
    a, z = r-t, s-t
    eps = -1 if q % 4 == 3 else 1
    answer = F(0)
    for k in range(t+1):
        weight = F(gb(t,k,q), q**(b(t)-b(t-k)))
        aa, az = rho(k,a,q)*p(a-k,q), rho(k,z,q)*p(z-k,q)
        ba, bz = eps**k*rho(k,a,q)*mu(a-k,q), eps**k*rho(k,z,q)*mu(z-k,q)
        answer += weight * (p(t-k,q)*(aa*az+xi*eta*ba*bz)
                 + mu(t-k,q)*(xi*ba*az+eta*aa*bz))/4
    return answer


def charpoly_coefficients(mats: np.ndarray, q: int = 3) -> np.ndarray:
    """Exact det(t I - A), coefficients in ascending order; used only at n=4."""
    n = mats.shape[-1]
    out = np.zeros((len(mats),n+1),dtype=np.int64)
    for perm in permutations(range(n)):
        sign = (-1)**sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
        term = np.zeros_like(out)
        term[:,0] = 1
        for i in range(n):
            nxt = (-mats[:,i,perm[i],None]*term)%q
            if i == perm[i]:
                nxt[:,1:] = (nxt[:,1:]+term[:,:-1])%q
            term = nxt
        out = (out+sign*term)%q
    return out


def run() -> None:
    count = 0
    for q in (3,5,7,9,11,25):
        for r in range(1,17):
            avg, delta, same = variances(r,q)
            N = 2*prod(q**j+1 for j in range(1,r))
            assert delta[0] == 4*p(r,q)/N/q**((r+1)//2)
            assert delta[1] == 4*p(r,q)/N/q**(r//2)
            assert delta[2] == (4*mu(r,q)/N/q**(r//2) if r%2==0 else 0)
            assert all(same[j] == avg[j]+delta[j]/4 for j in range(3))
            if r >= 2:
                assert avg[0] <= F(192,q**(2*r-2))
                assert avg[1] <= F(12,q**(r-1))
                for xi in (-1,1):
                    assert (avg[0]+avg[1]+2*xi*avg[2])/4 <= F(40,q**(r-1))
            for t in range(r+1):
                kj,kd,_ = moments(r,t,q)
                assert 0 <= kj <= F(64,q**(2*(r-t)+1))
                assert 0 <= kd <= F(4,q**(r-t))
            # Classical alternating Gaussian sum, independently obtained from
            # the signed common-generator intersection expansion.
            signed_sum = sum((F((-1)**a*gb(r,a,q),q**(a*(r+1-a)))
                              for a in range(r+1)),F(0))
            assert signed_sum == p(r,q)
            lam,pairs,zsquare = common_moments(r,q)
            eps = -1 if q%4==3 else 1
            m = r//2
            scalar = (-eps)**m*q**(m*m) if r%2==0 else (-1)**(m+1)*q**(m*(m+1))
            index = 1 if r%2==0 else 0
            assert F(scalar*scalar,(N//2)**2)*zsquare == delta[index]
            count += 1
    print(f'PASS: exact rational identities/bounds and rare-event moment identities for {count} (r,q) pairs; r=1..16, q=3,5,7,9,11,25.')
    gr_count = 0
    for q in (3,5,7,9,11,25):
        for r in range(1,11):
            for n in (2*r,2*r+3):
                jj,dd,jd = grassmann_variances(n,r,q)
                assert 0 <= jj <= F(384,q**n)
                assert 0 <= dd <= F(20,q**(n-r))
                for xi in (-1,1):
                    assert 0 <= (jj+dd+2*xi*jd)/4 <= F(80,q**(n-r))
                gr_count += 1
    print(f'PASS: exact Grassmannian bounds for {gr_count} (n,r,q) triples.')

    for n in (1,2,3):
        mats = sym_matrices(n)
        J,D = statistics(mats)
        assert F(int(J.sum()),len(J)) == p(n,3)
        assert F(int(D.sum()),len(D)) == mu(n,3)
        print(f'PASS: F_3 symmetric {n}x{n} enumeration: {len(J)} matrices; E[J]={p(n,3)}, E[D]={mu(n,3)}.')
        # All nonsingular Fourier frequencies, checked in Z[zeta_3].
        A = mats[J==1]
        traces = np.einsum('aij,bji->ab', A, mats) % 3
        coeff = {}
        for label, values, exponent in [('D',D,b(n)-n//2),('J',J,b(n)-(n+1)//2)]:
            c = np.stack([((traces==j)*values).sum(axis=1) for j in range(3)],axis=1)
            norm = (c*c).sum(axis=1)-c[:,0]*c[:,1]-c[:,0]*c[:,2]-c[:,1]*c[:,2]
            assert np.all(norm == 3**exponent)
            coeff[label] = c[:,:2]-c[:,2,None]
        if n%2==0:
            _,disc = statistics(A)
            assert np.array_equal(coeff['J'], disc[:,None]*coeff['D'])
        print(f'PASS: exact cyclotomic Fourier magnitudes at all {len(A)} nonsingular frequencies in dimension {n}.')

    # Conditional extensions with a one-dimensional new block.
    for t in (1,2):
        mats = sym_matrices(t+1)
        J,D = statistics(mats)
        groups: dict[tuple[int,...], list[int]] = defaultdict(lambda:[0,0,0])
        for C,j,d in zip(mats[:,:t,:t],J,D):
            rec = groups[tuple(int(x) for x in C.ravel())]
            rec[0] += 1; rec[1] += int(j); rec[2] += int(d)
        for key,(total,js,ds) in groups.items():
            C = np.array(key,dtype=np.int64).reshape(t,t)
            rank = rank_mod(C)
            k = t-rank
            # Find a nonsingular principal minor of maximal rank.
            sigma = 1
            if rank:
                sigma = None
                for inds in combinations(range(t),rank):
                    block = C[np.ix_(inds,inds)][None,:,:]
                    _,disc = statistics(block)
                    if disc[0]:
                        sigma = int(disc[0]); break
                assert sigma is not None
            assert F(js,total) == rho(k,1,3)*p(1-k,3)
            assert F(ds,total) == sigma*(-1)**k*rho(k,1,3)*mu(1-k,3)
        print(f'PASS: every conditional extension of each of {len(groups)} leading {t}x{t} blocks over F_3.')

    for r,s,t in [(2,2,0),(2,2,1),(2,3,1),(2,2,2)]:
        n = r+s-t
        mats = sym_matrices(n)
        u = list(range(r))
        v = list(range(t))+list(range(r,n))
        _,du = statistics(mats[:,u,:][:,:,u])
        _,dv = statistics(mats[:,v,:][:,:,v])
        for xi,eta in product((-1,1), repeat=2):
            actual = F(int(((du==xi)&(dv==eta)).sum()),len(mats))
            assert actual == exact_joint(r,s,t,xi,eta)
        print(f'PASS: all four joint-sign probabilities for (r,s,t)=({r},{s},{t}), {len(mats)} ambient forms.')

    # Independent geometry and full ambient enumeration for the split 4-space.
    H = np.block([[np.zeros((2,2),dtype=np.int64),np.eye(2,dtype=np.int64)],
                  [np.eye(2,dtype=np.int64),np.zeros((2,2),dtype=np.int64)]])
    subspaces = list(all_rref(4,2))
    generators = [U for U in subspaces if np.all((U@H@U.T)%3==0)]
    assert len(subspaces)==130 and len(generators)==8
    family = np.array([(-1)**(rank_mod(np.vstack([generators[0],U]))-2) for U in generators])
    assert int((family==1).sum())==int((family==-1).sum())==4
    for U in generators:
        counts = [sum(4-rank_mod(np.vstack([U,V]))==t for V in generators) for t in range(3)]
        assert counts == [3,4,1]
    mats = sym_matrices(4)
    jcols,dcols,zcols = [],[],[]
    for U in generators:
        restricted = np.einsum('ai,nij,bj->nab',U,mats,U)%3
        j,d = statistics(restricted)
        jcols.append(j); dcols.append(d)
        zcols.append(np.all(restricted==0,axis=(1,2)).astype(np.int64))
    Js,Ds = np.stack(jcols,axis=1),np.stack(dcols,axis=1)
    Zs = np.stack(zcols,axis=1)
    avg,delta,_ = variances(2,3)
    js,ds,jd,dd = Js.sum(axis=1),Ds.sum(axis=1),Js@family,Ds@family
    size = len(mats)
    assert F(int((js*js).sum()),size*64)-p(2,3)**2 == avg[0]
    assert F(int((ds*ds).sum()),size*64)-mu(2,3)**2 == avg[1]
    assert F(int((js*ds).sum()),size*64)-p(2,3)*mu(2,3) == avg[2]
    assert F(int((jd*jd).sum()),size*16) == delta[0]
    assert F(int((dd*dd).sum()),size*16) == delta[1]
    assert F(int((jd*dd).sum()),size*16) == delta[2]
    print(f'PASS: all {size} ambient quadratic forms, all 8 hyperbolic generators; exact average and family-contrast covariance matrices.')
    print(f'  q=3, r=2: Var(Jbar)={avg[0]}, Var(Dbar)={avg[1]}, Cov={avg[2]}.')
    print(f'  q=3, r=2: E[Delta_J^2]={delta[0]}, E[Delta_D^2]={delta[1]}, E[Delta_J Delta_D]={delta[2]}.')
    C,Z = Zs.sum(axis=1),Zs@family
    assert np.array_equal(dd,3*Z)
    lam,pairs,zsquare = common_moments(2,3)
    assert F(int(C.sum()),size) == lam
    assert F(int((C*(C-1)).sum()),size) == pairs
    assert F(int((Z*Z).sum()),size) == zsquare
    aq = F((3**2-1)*(3**3-3+1),3**7)
    bq = F((3-1)**2*(3+1),4*3**7)
    law = {-2:bq,-1:aq,0:1-2*aq-2*bq,1:aq,2:bq}
    histogram = {int(z):int(count) for z,count in zip(*np.unique(Z,return_counts=True))}
    for z,prob in law.items():
        assert F(histogram.get(z,0),size) == prob
    print(f'PASS: pointwise even-rank identity and complete rank-two law; histogram of Z: {histogram}.')
    supported = mats[C>0]
    T = np.einsum('ij,njk->nik',H,supported)%3
    coeff = charpoly_coefficients(T)
    assert np.all(coeff[:,4]==1)
    aa = coeff[:,3]*2%3
    bb = (coeff[:,2]-aa*aa)*2%3
    assert np.all(coeff[:,1]==(2*aa*bb)%3)
    assert np.all(coeff[:,0]==bb*bb%3)
    print(f'PASS: square-characteristic-polynomial obstruction for all {len(supported)} forms with a common generator.')

    # Odd-rank pointwise identity on a completely enumerated 9-dimensional slice
    # of Sym_6: Q=[[0,B],[B^T,C]], B diagonal, C any symmetric 3 by 3.
    H6 = np.block([[np.zeros((3,3),dtype=np.int64),np.eye(3,dtype=np.int64)],
                   [np.eye(3,dtype=np.int64),np.zeros((3,3),dtype=np.int64)]])
    g6 = [U for U in all_rref(6,3) if np.all((U@H6@U.T)%3==0)]
    assert len(g6)==80
    s6 = np.array([(-1)**(rank_mod(np.vstack([g6[0],U]))-3) for U in g6])
    assert int((s6==1).sum()) == 40
    bottom = sym_matrices(3)
    slice_q = np.zeros((27*len(bottom),6,6),dtype=np.int64)
    for block_index,diag in enumerate(product(range(3),repeat=3)):
        sl = slice(block_index*len(bottom),(block_index+1)*len(bottom))
        B = np.diag(diag)
        slice_q[sl,:3,3:] = B
        slice_q[sl,3:,:3] = B
        slice_q[sl,3:,3:] = bottom
    jcontrast = np.zeros(len(slice_q),dtype=np.int64)
    zcontrast = np.zeros(len(slice_q),dtype=np.int64)
    for U,sgn in zip(g6,s6):
        restriction = np.einsum('ai,nij,bj->nab',U,slice_q,U)%3
        J,_ = statistics(restriction)
        jcontrast += sgn*J
        zcontrast += sgn*np.all(restriction==0,axis=(1,2))
    assert np.array_equal(jcontrast,9*zcontrast)
    assert np.any(zcontrast != 0)
    print(f'PASS: odd-rank pointwise identity on all {len(slice_q)} forms in the specified Sym_6 slice, using all 80 generators.')
    print('ALL CHECKS PASSED. No floating-point pass/fail checks; no Monte Carlo; no proof-assistant certification.')

if __name__ == '__main__':
    if not __debug__:
        sys.exit('Verification requires assertions. Rerun without Python -O or -OO.')
    run()
