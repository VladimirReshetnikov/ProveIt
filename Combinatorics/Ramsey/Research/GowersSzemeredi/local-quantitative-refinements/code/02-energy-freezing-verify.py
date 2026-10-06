#!/usr/bin/env python3
"""Independent finite checks for energy-sensitive inverse steps.

Requires Python 3.10+ and NumPy. All random tests use a fixed seed.
These checks supplement, and do not replace, the proofs in the article.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

SEED = 20261006

def ambiguity(f: np.ndarray, g: np.ndarray) -> np.ndarray:
    """A[h,r] = E_x f(x) conjugate(g(x-h)) exp(-2 pi i r x/N)."""
    n = len(f)
    return np.stack([np.fft.fft(f * np.conj(np.roll(g, h))) / n
                     for h in range(n)])

def u3_power(f: np.ndarray) -> float:
    return float(np.mean(np.sum(np.abs(ambiguity(f, f)) ** 4, axis=1)))

def weighted_energy(w: np.ndarray) -> float:
    n = w.shape[0]
    conv = np.fft.ifft2(np.fft.fft2(w) ** 2).real
    return float(np.sum(conv * conv) / n ** 3)

def direct_energy(w: np.ndarray) -> float:
    n = w.shape[0]
    conv = np.zeros_like(w, dtype=float)
    for h in range(n):
        for r in range(n):
            conv += w[h, r] * np.roll(np.roll(w, h, axis=0), r, axis=1)
    return float(np.sum(conv * conv) / n ** 3)

def mass(f: np.ndarray) -> float:
    return float(np.mean(np.abs(f) ** 2))

def check_energy(f: np.ndarray, g: np.ndarray, w: np.ndarray) -> dict:
    n = len(f)
    t = float(np.sum(w * np.abs(ambiguity(f, g)) ** 2) / n)
    mf, mg = mass(f), mass(g)
    uf, ug, energy = u3_power(f), u3_power(g), weighted_energy(w)
    # Verify the convolution/Parseval identities independently.
    x = np.arange(n)
    F = np.stack([f * np.conj(np.roll(f, u)) for u in range(n)])
    A = np.stack([g * np.conj(np.roll(g, u)) for u in range(n)])
    V = np.stack([w @ np.exp(2j*np.pi*u*x/n) for u in range(n)])
    K = np.stack([np.fft.ifft(np.fft.fft(A[u]) * np.fft.fft(V[u])) / n
                  for u in range(n)])
    pairing = np.mean(F * np.conj(K))
    assert abs(pairing - t) <= 2e-9 * max(1.0, t)
    r_value = float(np.mean(np.abs(K) ** 2))
    af = np.fft.fft(A, axis=1) / n
    vf = np.fft.fft(V, axis=1) / n
    assert abs(r_value - np.mean(np.sum(np.abs(af)**2*np.abs(vf)**2,
                                         axis=1))) < 2e-8*max(1,r_value)
    e_spectral = float(np.mean(np.sum(np.abs(vf) ** 4, axis=1)))
    assert abs(e_spectral-energy) <= 2e-8*max(1,energy)
    lhs = t ** 4
    rhs1, rhs2 = mf ** 4 * ug * energy, mg ** 4 * uf * energy
    tolerance = 2e-8 * max(1.0, lhs, rhs1, rhs2)
    assert lhs <= min(rhs1, rhs2) + tolerance
    assert uf <= mf ** 4 + 2e-9*max(1,mf**4)
    assert ug <= mg ** 4 + 2e-9*max(1,mg**4)
    assert t*t <= mf*mf*r_value + 2e-8*max(1,t*t)
    assert r_value*r_value <= ug*energy + 2e-8*max(1,r_value*r_value)
    if n <= 5:
        assert abs(energy-direct_energy(w)) <= 2e-8*max(1,energy)
    return dict(N=n,T=t,m_f=mf,m_g=mg,U3_f_power8=uf,
                U3_g_power8=ug,energy=energy,
                saturation=lhs/min(rhs1,rhs2) if min(rhs1,rhs2)>0 else None)

def main() -> None:
    rng = np.random.default_rng(SEED)
    energy_checks = 0
    for n in (2, 3, 4, 5, 7, 8, 11):
        for _ in range(35):
            f = rng.normal(size=n)+1j*rng.normal(size=n)
            g = rng.normal(size=n)+1j*rng.normal(size=n)
            w = rng.random((n,n))
            w *= rng.random((n,n)) < .4
            check_energy(f,g,w)
            energy_checks += 1
            graph = np.zeros((n,n))
            graph[np.arange(n),rng.integers(n,size=n)] = rng.random(n)
            check_energy(f,g,graph)
            energy_checks += 1
    examples = []
    # Constant-amplitude quadratic phase with its derivative-frequency graph.
    n = 7
    x = np.arange(n)
    f = (0.3+0.4j)*np.exp(2j*np.pi*x*x/n)
    w = np.zeros((n,n)); w[x,(2*x)%n] = 1
    examples.append(dict(name='quadratic_phase_graph',**check_energy(f,f,w)))
    # A subgroup and its annihilator: genuinely multivalued spectral support.
    n=12; f=(np.arange(n)%3==0).astype(float)
    w=np.zeros((n,n)); w[np.ix_([0,3,6,9],[0,4,8])]=1
    examples.append(dict(name='subgroup_spectral_rectangle',**check_energy(f,f,w)))
    # A balanced half-density set: a scalar multiple of a character.
    n=8; f=(np.arange(n)%2==0).astype(float)-.5
    w=np.zeros((n,n)); w[:,0]=1
    examples.append(dict(name='balanced_half_density',**check_energy(f,f,w)))
    for ex in examples:
        assert abs(ex['saturation']-1)<1e-8
    # Sharp local real-phase inequality and its linear envelope.
    phase_checks=0
    for _ in range(2500):
        n=int(rng.integers(2,30)); rho=float(rng.uniform(0,.9999))
        theta=np.arcsin(rho)
        z=np.exp(1j*rng.uniform(-theta,theta,size=n))
        f=rng.normal(size=n)
        L=float(np.sum(np.abs(f))); F=float(np.sum(f)); C=abs(np.dot(f,z))
        assert C*C <= (1-rho*rho)*F*F +rho*rho*L*L +1e-9*max(1,L*L)
        assert C <= rho*L+(1-rho)*abs(F)+1e-9*max(1,L)
        phase_checks+=1
    rho=.3; z=np.exp(1j*np.array([-np.arcsin(rho),np.arcsin(rho)]))
    f=np.array([2.,-1.]); L=np.abs(f).sum(); F=f.sum(); C=abs(f@z)
    assert abs(C*C-((1-rho*rho)*F*F+rho*rho*L*L))<1e-12
    # Sharp positive-mass tail: arbitrary positive weights, zero weighted mean.
    tail_checks=0
    for _ in range(3000):
        n=int(rng.integers(3,40)); sizes=rng.random(n);sizes/=sizes.sum()
        values=rng.uniform(-1,1,size=n);values-=np.dot(sizes,values)
        a=float(-values.min());b=float(values.max())
        p=float(np.dot(sizes,np.maximum(values,0)))
        t=float(rng.uniform(0,a*p/(a-p)))
        Q=(p*(1+t/a)-t)/(b-t)
        actual=float(sizes[values>t].sum())
        assert actual+1e-10>=Q
        tail_checks+=1
    # Nonzero-mean extension: test without balancing the sample.
    nonzero_checks = 0
    for _ in range(1500):
        n = int(rng.integers(3,40))
        sizes = rng.random(n); sizes /= sizes.sum()
        a, b = rng.uniform(.1,2,size=2)
        values = rng.uniform(-a,b,size=n)
        p_plus = float(np.dot(sizes,np.maximum(values,0)))
        p_minus = float(np.dot(sizes,np.maximum(-values,0)))
        t = float(rng.uniform(0,b))
        Q = (p_plus-t*(1-p_minus/a))/(b-t)
        assert float(sizes[values>t].sum())+1e-10 >= Q
        nonzero_checks += 1
    # Closed-form optimum against a dense grid for both threshold regimes.
    budget_checks = 0
    for _ in range(1500):
        delta = float(rng.uniform(.01,.99))
        lam = 2*delta*(1-delta)
        alpha = lam*float(rng.uniform(.01,.99))
        t = delta*alpha/(2*delta-alpha)*float(rng.uniform(0,.99))
        a_t = (1+t/delta)/2
        d, e = a_t*alpha-t, a_t*lam-t
        assert abs(e-delta*(1-delta-t)) < 1e-12
        B0 = float(np.exp(rng.uniform(np.log(4),np.log(1e7))))
        # Stable form of 1-sqrt(1-d/e).
        r = (d/e)/(1+np.sqrt(1-d/e))
        rho = min(r,np.pi/B0)
        def objective(radius):
            q = (d-e*radius)/((1-radius)*(1-delta-t))
            return q/np.maximum(B0,np.pi/radius)
        grid = np.linspace((d/e)*1e-6,(d/e)*(1-1e-6),1501)
        optimum = float(objective(rho))
        assert optimum+1e-12 >= float(np.max(objective(grid)))
        if r <= np.pi/B0:
            assert abs(optimum-delta*r*r/np.pi)<1e-12
        budget_checks += 1
    # Exact rational equality data for the tail bound: a=b=1,p=1/5,t=1/10.
    # Negative, low-positive, high-positive masses: 1/5,2/3,2/15.
    from fractions import Fraction as Fq
    a=b=Fq(1);p=Fq(1,5);t=Fq(1,10)
    q=(p*(1+t/a)-t)/(b-t)
    neg=p/a;low=1-neg-q
    assert q==Fq(2,15) and low==Fq(2,3)
    assert -a*neg+t*low+b*q==0
    delta,alpha,rho=Fq(1,10),Fq(1,50),Fq(1,20)
    sigma=(alpha-2*rho*delta*(1-delta))/(1-rho)
    t_example=Fq(1,400)
    good_mass=((sigma/2)*(1+t_example/delta)-t_example)/(1-delta-t_example)
    best_increment=delta*sigma/(2*delta-sigma)
    assert sigma==Fq(11,950)
    assert best_increment==Fq(11,1790)
    assert good_mass==Fq(261,68210)
    report=dict(seed=SEED,random_energy_checks=energy_checks,
                random_phase_checks=phase_checks,random_tail_checks=tail_checks,
                random_nonzero_mean_checks=nonzero_checks,
                random_phase_budget_checks=budget_checks,
                exact_transfer_example=dict(delta=str(delta),alpha=str(alpha),
                    rho=str(rho),sigma=str(sigma),threshold=str(t_example),
                    good_mass=str(good_mass),best_increment=str(best_increment)),
                sharpness_examples=examples,
                exact_tail_example=dict(a=str(a),b=str(b),p=str(p),t=str(t),
                                        negative_mass=str(neg),
                                        low_positive_mass=str(low),
                                        high_positive_mass=str(q)),
                status='All checks passed. Numerical checks are not formal proofs.')
    dest=Path(__file__).with_name('verification_results.json')
    dest.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
