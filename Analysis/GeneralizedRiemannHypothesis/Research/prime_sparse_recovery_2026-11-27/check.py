#!/usr/bin/env python3
"""Reproducible numerical example, not a formal proof or rigorous interval certificate.
Requires Python 3, numpy, scipy, sympy.  All random draws use a fixed seed.
"""
import numpy as np
from sympy import factorint, primitive_root, primerange, totient
from itertools import product
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, eye, hstack, vstack
from math import gcd


def local_chars(p, a):
    """Primitive local characters as (label, array on Z/p**a)."""
    q = p**a
    if p == 2 and a == 1:
        return []
    if p == 2 and a == 2:
        return [('sign', np.array([0,1,0,-1], dtype=complex))]
    if p == 2:
        n = 2**(a-2)
        ret = []
        for b in range(2):
            for j in range(1,n,2):
                v = np.zeros(q, complex)
                for l in range(n):
                    z = np.exp(2j*np.pi*j*l/n)
                    u = pow(5,l,q)
                    v[u] = z
                    v[-u % q] = (-1)**b*z
                ret.append((f'{b}:{j}',v))
        return ret
    n = int(totient(q))
    g = int(primitive_root(q))
    units = np.array([pow(g,l,q) for l in range(n)])
    ret = []
    for j in range(1,n):
        if a>1 and j%p==0:
            continue
        v = np.zeros(q,complex)
        v[units] = np.exp(2j*np.pi*j*np.arange(n)/n)
        ret.append((str(j),v))
    return ret


def primitive_dictionary(Q, primes):
    cols = [np.ones(len(primes),complex)]
    labels = [(1,'trivial')]
    for q in range(2,Q+1):
        fac = [(int(p),int(a)) for p,a in factorint(q).items()]
        local = [local_chars(p,a) for p,a in fac]
        for group in product(*local):
            v = np.ones(len(primes),complex)
            for (p,a),(_,table) in zip(fac,group):
                v *= table[primes%(p**a)]
            labels.append((q,','.join(name for name,_ in group)))
            cols.append(v)
    # Independent count: number of primitive characters = (mu * phi)(q).
    from sympy import mobius, divisors
    expected = sum(int(sum(mobius(q//d)*totient(d) for d in divisors(q)))
                   for q in range(1,Q+1))
    assert len(cols)==expected
    return np.column_stack(cols),labels


def real_decoder(A,y,k,m):
    """LP form of the complex theorem restricted to real unknowns and data."""
    n,d = A.shape
    As = csr_matrix(A)
    I,J = eye(d),eye(n)
    zdn = csr_matrix((d,n)); znd = csr_matrix((n,d))
    B = vstack([hstack([I,-I,zdn]), hstack([-I,-I,zdn]),
                hstack([As,znd,-J]), hstack([-As,znd,-J])],format='csr')
    b = np.r_[np.zeros(2*d),y,-y]
    obj = np.r_[np.zeros(d),np.ones(d),np.full(n,2*k/m)]
    res = linprog(obj,A_ub=B,b_ub=b,bounds=[(None,None)]*d+[(0,None)]*(d+n),method='highs')
    assert res.success,res.message
    return res.x[:d]


def main():
    Q,k,x = 31,2,40000
    rng = np.random.default_rng(20261127)
    pool = np.array(list(primerange(x,2*x)), dtype=np.int64)
    u = pool/x
    weights = np.log(pool)*30*(u-1)**2*(2-u)**2
    M = 1600
    probabilities = M*weights/weights.sum()
    assert probabilities.max() <= 1
    primes = pool[rng.random(len(pool)) < probabilities]
    m=len(primes)
    A,labels=primitive_dictionary(Q,primes)
    G=A.conj().T@A/m
    mu=float(np.max(np.abs(G-np.eye(A.shape[1]))))
    print(f'Q={Q}, k={k}, prime interval=[{x},{2*x}], pool={len(pool)}, selected={m}')
    print(f'primitive dictionary columns={A.shape[1]}, observed coherence={mu:.10f}')
    print(f'certified by theorem if coherence upper bound exact: e+2t < {m*(1/(2*k)-mu):.3f}')
    # Real-character LP example; full complex dictionary coherence was measured above.
    real_idx=np.flatnonzero(np.max(np.abs(A.imag),axis=0)<1e-9)
    Ar=np.rint(A[:,real_idx].real)
    c=np.zeros(len(real_idx)); c[1]=1.25; c[-1]=-0.8
    budget=m*(1/(2*k)-mu)
    assert budget>0
    e=int(budget*.20); t=int(budget*.30)
    order=rng.permutation(m); E=order[:e]; T=order[e:e+t]
    keep=np.ones(m,bool); keep[E]=False
    y=Ar@c; y[T]+=rng.choice([-1,1],size=t)*50
    margin=1-2*k*mu-2*k*e/m-4*k*t/m
    assert margin>0
    out=real_decoder(Ar[keep],y[keep],k,m)
    err=np.linalg.norm(out-c,1)
    print(f'real subdictionary size={len(real_idx)}, support={labels[real_idx[1]]}, {labels[real_idx[-1]]}')
    print(f'erasures={e}, corruptions={t}, margin={margin:.8f}, noiseless LP coefficient l1 error={err:.3g}')
    assert err<1e-7
    noise=rng.normal(0,.005,size=m); yn=y+noise
    out=real_decoder(Ar[keep],yn[keep],k,m)
    err=float(np.linalg.norm(out-c,1)); bound=4*k*np.linalg.norm(noise[keep],1)/(m*margin)
    print(f'noisy LP coefficient l1 error={err:.8g}; theorem upper bound={bound:.8g}')
    assert err<=bound+1e-7
    # Universal sharpness witness: q=17, subgroup of order 4, twist by exponent 1.
    q=17; g=int(primitive_root(q)); n=q-1
    logs={pow(g,j,q):j for j in range(n)}
    classes=np.array([logs[int(p%q)]%(2*k) if p%q else -1 for p in primes])
    counts=np.array([(classes==j).sum() for j in range(2*k)])
    j0=int(counts.argmin()); D=np.flatnonzero(classes==j0)
    theta_cols=[labels.index((q,str(1+j*n//(2*k)))) for j in range(2*k)]
    v=np.exp(2j*np.pi*j0/(2*k)); a=v**(-np.arange(2*k))
    f=A[:,theta_cols[:k]]@a[:k]; h=A[:,theta_cols[k:]]@(-a[k:])
    assert np.max(np.abs((f-h)[classes!=j0]))<1e-10
    assert np.allclose(np.abs((f-h)[D]),2*k)
    e0=len(D)%2; t0=(len(D)-e0)//2
    y_collision=f.copy(); y_collision[D[e0:e0+t0]]=h[D[e0:e0+t0]]
    active=np.ones(m,bool); active[D[:e0]]=False
    assert np.sum(np.abs(y_collision[active]-f[active])>1e-8)==t0
    assert np.sum(np.abs(y_collision[active]-h[active])>1e-8)==t0
    print(f'q=17 sharpness coset counts={counts.tolist()}, minimum distance witness={len(D)} <= floor(m/4)={m//4}')
    print(f'collision: {e0} erased and {t0} corruptions for each of two distinct 2-sparse vectors')
    np.savetxt('sample_primes.txt',primes,fmt='%d')
    print('All numerical and combinatorial assertions passed.')

if __name__=='__main__':
    main()
