#!/usr/bin/env python3
"""Reproducible checks for single-phase extraction and offset stability.

The graph checks use integers only. Fourier checks use floating point and are
regression tests, not machine-checked proofs. Run from any working directory.
"""
from __future__ import annotations
import json
import math
import platform
from pathlib import Path
from typing import Iterator
import numpy as np

SEED = 20261006
RNG = np.random.default_rng(SEED)
ROOT = Path(__file__).resolve().parents[1]


def compositions(total: int, length: int) -> Iterator[tuple[int, ...]]:
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, length - 1):
                yield (first,) + rest


def edges_for_cycles(m: int, components: int = 1) -> list[tuple[int, int]]:
    if m < 3:
        raise ValueError('Use the separate order-two check.')
    return [(c*m+i, c*m+(i+1) % m) for c in range(components) for i in range(m)]


def exact_graph_checks() -> dict:
    rows = []
    total = 0
    equalities = 0
    for m, comp, denominator in [(m, 1, 8) for m in range(2, 10)] + [(4,2,6),(5,2,6)]:
        count = eq = 0
        n = m*comp
        edges = edges_for_cycles(m, comp) if m >= 3 else [(2*c,2*c+1) for c in range(comp)]
        nbr = [set() for _ in range(n)]
        for i,j in edges:
            nbr[i].add(j); nbr[j].add(i)
        M = denominator
        for w in compositions(M, n):
            f = sum(w[i]*w[j] for i,j in edges)
            if m == 2:
                # Actual directed offset energy is twice the edge polynomial.
                assert 4*f <= M*M
            elif m == 3:
                assert 3*f <= M*M
            else:
                d = [sum(w[j] for j in nbr[i]) for i in range(n)]
                second = sum(w[i]*d[i]*d[i] for i in range(n))
                edge_gap = sum(w[i]*w[j]*(M-d[i]-d[j]) for i,j in edges)
                assert edge_gap == M*f-second
                variance = M*second-4*f*f
                assert edge_gap >= 0 and variance >= 0
                assert M*M*f-4*f*f == M*edge_gap+variance
                assert 4*f <= M*M
                if f:
                    candidates = [(i,j) for i,j in edges if w[i]*w[j] and
                                  (M-d[i]-d[j])*M <= M*M-4*f]
                    assert candidates
                if 4*f == M*M:
                    eq += 1
                    support = {i for i in range(n) if w[i]}
                    if m == 4:
                        assert any(support <= set(range(c*m,(c+1)*m)) and
                                   sum(w[c*m+i] for i in [0,2])*2 == M
                                   for c in range(comp))
                    else:
                        assert any(w[v]*2 == M and support <= ({v} | nbr[v])
                                   for v in range(n))
            count += 1
        rows.append(dict(order=m, components=comp, denominator=M,
                         distributions=count, triangle_free_equalities=eq))
        total += count; equalities += eq
    # Exact obstruction: P4 endpoint masses t, central masses 1/2-t.
    sharp = []
    from fractions import Fraction as F
    for den in [8,16,32,64,128]:
        t=F(1,den)
        p=[t,F(1,2)-t,F(1,2)-t,t,F(0)]
        energy=sum(p[i]*p[(i+1)%5] for i in range(5))
        assert F(1,4)-energy == t*t
        # Every 3-vertex star misses at least t of this distribution.
        missing=min(1-sum(p[j] for j in {(i-1)%5,i,(i+1)%5}) for i in range(5))
        assert missing == t
        sharp.append(dict(t=str(t), deficit=str(t*t), minimum_missing_mass=str(missing)))
    return dict(status='PASS', arithmetic='exact Python integers and Fraction',
                distributions=total, equality_cases=equalities, cases=rows,
                sharpness=sharp)


def fourier_checks() -> dict:
    max_error=0.0
    min_slack=float('inf')
    trials=0
    # Mixed functions, arbitrary weights, all cyclic offsets in each sample.
    for N in [2,3,4,5,6,7,8,9,11,12,15,16,21,25]:
        x=np.arange(N)
        chars=np.exp(2j*np.pi*np.outer(x,x)/N) # frequency, point
        for _ in range(14):
            u=(RNG.normal(size=N)+1j*RNG.normal(size=N))/3
            v=(RNG.normal(size=N)+1j*RNG.normal(size=N))/3
            w=RNG.random(N)*(RNG.random(N)>.25)
            uh=np.fft.fft(u)/N; vh=np.fft.fft(v)/N
            shifted=u[(x[:,None]+x[None,:])%N] # s,h
            windows=np.array([(shifted*(w*np.conj(chars[r]))).sum(axis=1)
                              for r in x])
            L=(np.abs(windows)*np.abs(v)[None,:]).mean(axis=1)
            H=float(L.max())
            for mu in x:
                chi=chars[mu]
                A=(shifted*np.conj(v)[:,None]*np.conj(chi)[:,None]).mean(axis=0)
                a=uh*np.conj(vh[(x-mu)%N])
                A2=a@chars
                K=(windows*(np.conj(v)*np.conj(chi))[None,:]).mean(axis=1)
                E=float(np.sum(w*np.abs(A)**2))
                D=float(np.sum(np.abs(a)))
                identity=np.vdot(a,K)
                gap_terms=float(np.sum(np.abs(a)*(H-L)) +
                                np.sum(np.abs(a)*L-np.real(np.conj(a)*K)))
                err=max(np.max(np.abs(A-A2)),abs(identity-E),abs(gap_terms-(D*H-E)))
                max_error=max(max_error,float(err))
                slack=D*H-E
                min_slack=min(min_slack,slack)
                assert slack >= -1e-10 and err < 1e-10
                trials+=1
    # Auto-ambiguity Parseval and exact offset ceilings, random power spectra.
    cap_trials=0
    for N in [2,3,4,5,6,7,8,9,10,12,15,21,25]:
        x=np.arange(N); chars=np.exp(2j*np.pi*np.outer(x,x)/N)
        for _ in range(20):
            f=RNG.normal(size=N)+1j*RNG.normal(size=N)
            fh=np.fft.fft(f)/N; sigma=float(np.mean(np.abs(f)**2))
            p=np.abs(fh)**2/sigma
            shifted=f[(x[:,None]+x[None,:])%N]
            for mu in x:
                order=N//math.gcd(int(mu),N)
                cap={1:1.,2:.5,3:1/3}.get(order,.25)
                A=(shifted*np.conj(f)[:,None]*np.conj(chars[mu])[:,None]).mean(axis=0)
                E=float(np.mean(np.abs(A)**2))/sigma**2
                formula=float(np.sum(p*p[(x-mu)%N]))
                max_error=max(max_error,abs(E-formula))
                assert abs(E-formula)<1e-10 and E <=cap+1e-10
                cap_trials+=1
    return dict(status='PASS', arithmetic='numpy complex128; tolerance 1e-10',
                mixed_extraction_trials=trials, offset_cap_trials=cap_trials,
                max_identity_error=max_error, minimum_extraction_slack=min_slack)


def balanced_checks() -> dict:
    trials=0; max_phase_error=0.0; min_slack=float('inf')
    for N in [3,5,7,9,11,15,21,25,27]:
        x=np.arange(N); chars=np.exp(2j*np.pi*np.outer(x,x)/N)
        for _ in range(45):
            size=int(RNG.integers(1,N))
            Aset=np.zeros(N); Aset[RNG.choice(N,size,replace=False)]=1
            delta=size/N; f=Aset-delta
            sigma=delta*(1-delta); B=max(delta,1-delta)
            lam=int(RNG.integers(N)); mu=int(RNG.integers(N))
            q=(lam*pow(2,-1,N)*x*x)%N
            g=f*np.exp(-2j*np.pi*q/N)
            w=RNG.random(N)*(RNG.random(N)>.35); T=float(w.sum())
            if T == 0: continue
            direct=np.array([np.mean(f*np.roll(f,int(h))*
                       np.exp(-2j*np.pi*((lam*h+mu)%N)*x/N)) for h in x])
            shifted=g[(x[:,None]+x[None,:])%N]
            amb=(shifted*np.conj(g)[:,None]*np.conj(chars[mu])[:,None]).mean(axis=0)
            phase=np.exp(-2j*np.pi*((lam*pow(2,-1,N)*x*x+mu*x)%N)/N)
            max_phase_error=max(max_phase_error,float(np.max(np.abs(direct-phase*amb))))
            energy=float(np.sum(w*np.abs(direct)**2))
            scores=[]
            for r in x:
                vals=(shifted*(w*np.conj(chars[r]))).sum(axis=1)
                scores.append(float(np.mean(np.abs(f)*np.abs(vals))))
            r=int(np.argmax(scores))
            vals=(shifted*(w*np.conj(chars[r]))).sum(axis=1)
            lower=energy/(B*sigma)
            slack=float(np.mean(np.abs(vals))-lower)
            min_slack=min(min_slack,slack)
            assert slack>=-1e-10
            assert 1/(B*sigma)>=27/4-1e-12
            trials+=1
    # Even-modulus quadratic refinements and the N=2 obstruction.
    for N in [2,4,6,8,10,12]:
        x=np.arange(N)
        for lam in range(N):
            q=lam*x*x/(2*N)
            for h in range(N):
                expected=lam*x*h/N
                residual=q[(x+h)%N]-q-q[h]-expected
                assert np.max(np.abs(np.exp(2j*np.pi*residual)-1))<1e-10
    f=np.array([1,1j]); coeff=np.fft.fft(f)/2
    assert np.allclose(np.abs(coeff),1/np.sqrt(2))
    return dict(status='PASS', weighted_balanced_trials=trials,
                maximum_chirp_sign_error=max_phase_error,
                minimum_common_phase_slack=min_slack,
                even_modulus_refinement='PASS', N2_classical_obstruction='PASS')


def stability_checks() -> dict:
    count=0; worst=0.0
    for m in [5,6,7,8,11,17]:
        for components in [1,2,3]:
            n=m*components
            edges=edges_for_cycles(m,components)
            nbr=[[] for _ in range(n)]
            for i,j in edges: nbr[i].append(j); nbr[j].append(i)
            for _ in range(80):
                t=float(RNG.uniform(0,0.14)); p=np.zeros(n)
                p[:4]=[t,.5-t,.5-t,t]
                noise=float(RNG.uniform(0,.004))
                p=(1-noise)*p+noise*RNG.dirichlet(np.ones(n))
                F=sum(p[i]*p[j] for i,j in edges); eps=.25-F
                if not 0 < eps <= 1/16: continue
                d=np.array([sum(p[j] for j in nbr[i]) for i in range(n)])
                e=min(((i,j) for i,j in edges if p[i]*p[j]>0),
                      key=lambda ij:1-d[ij[0]]-d[ij[1]])
                i,j=e
                left=next(k for k in nbr[i] if k!=j)
                right=next(k for k in nbr[j] if k!=i)
                path=[left,i,j,right]
                removed=sum(p[k] for k in range(n) if k not in path)
                assert removed<=4*eps+1e-12
                # Remove smaller endpoint, retain a 3-vertex star.
                if p[left] <= p[right]: center=j; leaves=[i,right]
                else: center=i; leaves=[left,j]
                q=np.zeros(n); q[center]=.5
                s=p[leaves].sum()
                if s: q[leaves]=p[leaves]/(2*s)
                else: q[leaves[0]]=.5
                l1=float(np.abs(p-q).sum())
                hell=float(np.sum((np.sqrt(p)-np.sqrt(q))**2))
                bound=8*eps+4*math.sqrt(3*eps)
                assert l1 <=bound+1e-10
                assert hell <=l1+1e-10
                assert math.sqrt(hell)<=3*eps**.25+1e-10
                worst=max(worst,l1/bound); count+=1
    return dict(status='PASS', constructive_stability_trials=count,
                maximum_l1_to_bound_ratio=worst)



def short_stability_checks() -> dict:
    """Test the four short-orbit repair constructions, including extra orbits."""
    rng = np.random.default_rng(SEED + 1)
    rows = []
    for m in [1, 2, 3, 4]:
        count = 0
        worst = 0.0
        cap = {1: 1., 2: .5, 3: 1/3, 4: .25}[m]
        squared_constant = {1: 2., 2: 5., 3: 10., 4: 9.}[m]
        for components in [2, 3, 5]:
            n = m * components
            for _ in range(120):
                p = np.zeros(n)
                if m == 1:
                    p[0] = 1
                elif m == 2:
                    t = float(rng.uniform(-.1, .1))
                    p[:2] = [.5+t, .5-t]
                elif m == 3:
                    t = float(rng.uniform(-.1, .1))
                    p[:3] = [1/3+t, 1/3-t, 1/3]
                else:
                    t = float(rng.uniform(-.1, .1))
                    a, b = rng.random(2)
                    p[:4] = [(.5+t)*a, (.5-t)*b,
                             (.5+t)*(1-a), (.5-t)*(1-b)]
                noise = float(rng.uniform(0, .01))
                p = (1-noise)*p + noise*rng.dirichlet(np.ones(n))
                a = p.reshape(components, m)
                energy = float(np.sum(a*np.roll(a, 1, axis=1)))
                eps = cap-energy
                assert 0 < eps <= 1/16
                q = np.zeros(n)
                if m == 1:
                    q[int(np.argmax(p))] = 1
                else:
                    c = int(np.argmax(a.sum(axis=1)))
                    base = c*m
                    if m == 2:
                        q[base:base+2] = .5
                    elif m == 3:
                        q[base:base+3] = 1/3
                    else:
                        for indices in [[base, base+2], [base+1, base+3]]:
                            mass = float(p[indices].sum())
                            assert mass > 0
                            q[indices] = p[indices]/(2*mass)
                qa = q.reshape(components, m)
                assert abs(float(np.sum(qa*np.roll(qa, 1, axis=1)))-cap) < 1e-12
                cost = float(np.sum((np.sqrt(p)-np.sqrt(q))**2))
                assert cost <= squared_constant*eps + 1e-10
                worst = max(worst, cost/(squared_constant*eps))
                count += 1
        rows.append(dict(order=m, trials=count, maximum_cost_bound_ratio=worst))
    return dict(status='PASS', trials=sum(row['trials'] for row in rows), cases=rows)


def noncyclic_refinement_checks() -> dict:
    """Exact rational tests of the coordinate construction on product groups."""
    from fractions import Fraction
    from itertools import product
    import random
    rng = random.Random(SEED + 2)
    rows = []
    for orders in [(2, 4), (3, 6), (4, 4), (2, 2, 2), (2, 3, 4)]:
        points = list(product(*(range(n) for n in orders)))
        d = len(orders)
        checks = 0
        for _ in range(6):
            b = [[Fraction(0) for j in range(d)] for i in range(d)]
            for i in range(d):
                for j in range(i, d):
                    den = math.gcd(orders[i], orders[j])
                    b[i][j] = b[j][i] = Fraction(rng.randrange(den), den)
            a = [-Fraction(n*(n-1), 2*n)*b[i][i]
                 for i,n in enumerate(orders)]
            def q(x: tuple[int, ...]) -> Fraction:
                return sum((x[i]*a[i] + x[i]*(x[i]-1)//2*b[i][i]
                            for i in range(d)), Fraction(0)) + sum(
                    (x[i]*x[j]*b[i][j] for i in range(d) for j in range(i+1,d)),
                    Fraction(0))
            for x in points:
                for i,n in enumerate(orders):
                    y = list(x); y[i] += n
                    assert (q(tuple(y))-q(x)).denominator == 1
                for y in points:
                    z = tuple((x[i]+y[i]) % orders[i] for i in range(d))
                    bilinear = sum((x[i]*y[j]*b[i][j]
                                    for i in range(d) for j in range(d)), Fraction(0))
                    assert (q(z)-q(x)-q(y)-bilinear).denominator == 1
                    checks += 1
        rows.append(dict(cyclic_factor_orders=orders, bilinear_maps=6,
                         pairwise_polarization_checks=checks))
    return dict(status='PASS', arithmetic='exact Fraction',
                pairwise_polarization_checks=sum(r['pairwise_polarization_checks'] for r in rows),
                cases=rows)


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: verification relies on assert statements.")
    result=dict(seed=SEED, python=platform.python_version(), numpy=np.__version__,
                graph=exact_graph_checks(), Fourier=fourier_checks(),
                balanced=balanced_checks(), stability=stability_checks(),
                short_stability=short_stability_checks(),
                noncyclic_refinements=noncyclic_refinement_checks())
    ROOT.joinpath('data').mkdir(exist_ok=True)
    dest=ROOT/'data'/'verification.json'
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
