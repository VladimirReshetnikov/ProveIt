#!/usr/bin/env python3
"""Finite checks for sliding-window phase removal.

Exact checks: window coverage counts, partition identities, modular
polarization, and the interval cube counting formula. Floating checks:
Gowers-CS/Hölder and the extracted partition-energy lower bound.
Requires Python 3.10+ and NumPy. Run: python phase_sliding_verify.py.
"""
from itertools import product
from math import comb, factorial
import json
import numpy as np


def vertices(k):
    return list(product((0, 1), repeat=k))


def cube_energy(f, k):
    """Unnormalized C_{k+1}(f), using Parseval for k=1,2."""
    p = len(f)
    if k == 1:
        return float(np.sum(abs(np.fft.fft(f))**4)/p)
    if k == 2:
        s = np.arange(p)
        diffs = f[None, :]*f[(s[None, :]-s[:, None]) % p].conj()
        return float(np.sum(abs(np.fft.fft(diffs, axis=1))**4)/p)
    raise ValueError('This finite audit uses k=1 or k=2.')


def phase_values(c, eps, p):
    out = np.zeros(p, dtype=np.int64)
    for mask, coefficient in enumerate(c):
        if all(not eps[j] or (mask >> j) & 1 for j in range(len(eps))):
            degree = mask.bit_count()+1
            factor = coefficient*pow(factorial(degree), -1, p) % p
            out = (out+factor*np.array([pow(s, degree, p)
                                       for s in range(p)])) % p
    return out


def tau_value(c, a, p):
    value = 0
    for mask, coefficient in enumerate(c):
        monomial = 1
        for j, aj in enumerate(a):
            if (mask >> j) & 1:
                monomial *= aj
        value += coefficient*monomial
    return value % p


def audit_case(p, k, m, seed):
    rng = np.random.default_rng(seed)
    h = (m-1)//2
    radius = k*h
    target = (k+2)*h
    M = p//target
    assert M >= 4
    assert radius < p/M < p-radius
    U = p//M+1
    s = np.arange(p)
    residues = (M*s[None, :]-np.arange(p*M)[:, None]) % (p*M)
    masks = (residues >= 1) & (residues <= p)
    assert set(map(int, masks.sum(axis=1))) <= {p//M, U}
    for j in range(p):
        assert np.all(masks[j::p].sum(axis=0) == 1)

    verts = vertices(k)
    coefficients = [int(x) for x in rng.integers(0, p, size=2**k)]
    centers = [int(x) for x in rng.integers(0, p, size=k)]
    f = rng.uniform(0.5, 1.0, p)*np.exp(2j*np.pi*rng.uniform(0, 1, p))
    copies = [f[(s-sum(x*y for x, y in zip(eps, centers))) % p]
              for eps in verts]
    phases = [phase_values(coefficients, eps, p) for eps in verts]
    gs = [copy*np.exp(-2j*np.pi*phase/p)
          for copy, phase in zip(copies, phases)]

    E = 0.0
    weighted_E = 0.0
    coverage_vectors = 0
    for a in product(range(-h, h+1), repeat=k):
        coverage = np.ones((p*M, p), dtype=np.bool_)
        product_f = np.ones(p, dtype=np.complex128)
        for eps, copy in zip(verts, copies):
            shift = sum(x*y for x, y in zip(eps, a))
            indices = (s-shift) % p
            coverage &= masks[:, indices]
            term = copy[indices]
            product_f *= term.conj() if sum(eps) % 2 else term
        exact_count = p-M*sum(abs(x) for x in a)
        assert np.all(coverage.sum(axis=0) == exact_count)
        coverage_vectors += p
        tau = tau_value(coefficients, a, p)
        value = abs(np.sum(product_f*np.exp(-2j*np.pi*tau*s/p)))**2
        E += value
        weighted_E += exact_count**2*value

        for y in range(-2, 3):
            total = np.zeros(p, dtype=np.int64)
            for eps, phase in zip(verts, phases):
                shift = sum(x*z for x, z in zip(eps, a))
                total += (-1)**sum(eps)*(phase[(s-shift) % p]
                                        -phase[(s-shift-y) % p])
            assert np.all((total-y*tau) % p == 0)

    # Cache repeated support intervals; the fractional windows have repeats.
    unique, inverse = np.unique(masks, axis=0, return_inverse=True)
    totals = []
    beta_max = 0.0
    for g in gs:
        values = np.array([cube_energy(mask*g, k) for mask in unique])
        energies = values[inverse]
        totals.append(float(energies.sum()))
        for j in range(p):
            beta_max = max(beta_max,
                           float(energies[j::p].sum())/(M*U**(k+2)))
    holder_upper = p*M*np.prod(np.array(totals)**(1/(2**k)))
    beta_lower = E*(p/M-radius)**2/(p*p*U**(k+2))
    weighted_lower = weighted_E/(p*p*M*M*U**(k+2))
    assert weighted_E <= holder_upper*(1+2e-9)
    assert beta_lower <= weighted_lower+1e-10
    assert weighted_lower <= beta_max+1e-9
    return dict(p=p, k=k, m=m, M=M, U=U,
                exact_coverage_vectors=coverage_vectors,
                distinct_windows=len(unique), input_energy=E,
                weighted_energy=weighted_E, holder_upper=holder_upper,
                guaranteed_beta=beta_lower,
                sharper_data_beta=weighted_lower,
                extracted_beta=beta_max, passed=True)


def audit_interval_counts():
    tests = 0
    for d in range(1, 5):
        for L in range(1, 9):
            enumerated = sum(max(L-sum(map(abs, h)), 0)
                             for h in product(range(1-L, L), repeat=d))
            formula = sum(comb(d, j)*comb(L+d-j, d+1)
                          for j in range(d+1)
                          if L+d-j >= d+1)
            assert enumerated == formula
            tests += 1
    return tests


if __name__ == '__main__':
    result = dict(
        interval_count_cases=audit_interval_counts(),
        sliding_cases=[audit_case(29, 1, 5, 1701),
                       audit_case(53, 2, 7, 1702),
                       audit_case(97, 2, 9, 1703)])
    print(json.dumps(result, indent=2))
