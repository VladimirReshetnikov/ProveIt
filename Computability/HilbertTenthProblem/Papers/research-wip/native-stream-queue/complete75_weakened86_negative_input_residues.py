"""Exact finite residue classification of a negative-input86 subsystem.

The complete86 source is unchanged.  The classification includes the input
Pell norm, its discriminant congruence, first-index equation and auxiliary
target modulo c.  It does NOT construct the remaining auxiliary equations,
transport equation, or a complete positive candidate zero.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import gcd, lcm
from pathlib import Path
import random

import complete75_weakened86_gap_eleven as inherited

pell = inherited.pell


def pell_mod(A, index, modulus):
    """Binary exponentiation of the Pell pair, independent of exact recurrence."""
    assert A >= 2 and index >= 0 and modulus >= 1
    delta = A*A-1
    result, base = (1 % modulus, 0), (A % modulus, 1 % modulus)
    def product(left, right):
        x, y = left
        u, v = right
        return ((x*u+delta*y*v) % modulus, (x*v+y*u) % modulus)
    while index:
        if index & 1:
            result = product(result, base)
        base = product(base, base)
        index //= 2
    return result


def crt(left, right):
    """Intersection of two residue classes, or None; moduli are positive."""
    r, m = left
    s, n = right
    assert m >= 1 and n >= 1
    g = gcd(m, n)
    if (s-r) % g:
        return None
    reduced = n//g
    step = 0 if reduced == 1 else ((s-r)//g*pow(m//g, -1, reduced)) % reduced
    modulus = m*reduced
    return ((r+m*step) % modulus, modulus)


def linear_class(coefficient, rhs, modulus):
    """All solutions of coefficient*x=rhs modulo modulus."""
    g = gcd(coefficient, modulus)
    if rhs % g:
        return None
    reduced = modulus//g
    residue = 0 if reduced == 1 else (rhs//g*pow(coefficient//g, -1, reduced)) % reduced
    return residue, reduced


def positive_interval(residue_class, gamma):
    """Positive representatives strictly below gamma, as one progression."""
    if residue_class is None:
        return None
    residue, modulus = residue_class
    first = residue or modulus
    if first >= gamma:
        return None
    return dict(first=first, step=modulus, count=1+(gamma-1-first)//modulus)


def input_index_class(A, p, u, r):
    assert 0 <= r < 2*p
    delta = A*A-1
    # Since A*A=1 modulo delta, this is equivalent to psi_A(v)=u.
    residue = u if r % 2 else A*u
    return crt((r, 2*p), (residue, delta))


def canonical_input_residues(A, p):
    """Residues of chi_A(v)+(A-2)*psi_A(v), indexed modulo 2p."""
    assert A >= 3 and p >= 3 and p % 2
    a = A-2
    c, previous = pell(A, p)[1], pell(A, p-1)[1]
    values = []
    for r in range(2*p):
        if r < p:
            x, y = pell(A, r)
            value = x+a*y
        elif r == p:
            value = c-previous
        else:
            x, y = pell(A, 2*p-r)
            value = x-a*y
        x, y = pell(A, r)
        assert value == (x+a*y) % c
        assert 0 < value <= c-previous < c
        values.append(value)
    return values


def coarse_classes(A, p, M, H, C, K, gamma, u, epsilon, lam, omega):
    """Input/discriminant and target-mod-c test, without the first index."""
    c = pell(A, p)[1]
    result = []
    for r, fr in enumerate(canonical_input_residues(A, p)):
        index = input_index_class(A, p, u, r)
        if index is None:
            continue
        rhs = K-M*C-M*fr+epsilon-lam-omega*p
        rho = positive_interval(linear_class(M*H, rhs, c), gamma)
        if rho:
            result.append(dict(r=r, input_index=list(index), rho=rho))
    return result


def state_period(A, E, limit=10000):
    """Find the exact modular Pell period on a bounded checker host.

    The mathematical search always terminates within E^2 states.  This
    implementation intentionally rejects expensive requests beyond limit.
    """
    assert E >= 2
    x, y, delta = 1, 0, A*A-1
    for t in range(1, min(E*E, limit)+1):
        x, y = (A*x+delta*y) % E, (x+A*y) % E
        if (x, y) == (1, 0):
            return t
    raise ValueError('bounded checker period search exceeded limit')


def classify(A, p, E, M, C, K, k, gamma, u, epsilon, lam, omega, period=None):
    """Exact finite classifier of the four-equation subsystem in the note.

    Records describe rho progressions in [1,gamma) and arbitrary input
    index lifts.  A supplied period need only be a positive return period.
    """
    assert A >= 3 and p >= 3 and p % 2 and E >= 2
    assert M >= 1 and C >= 0 and K >= 1 and k >= 1 and gamma >= 2 and u >= 1
    assert epsilon in (-1, 1) and lam in (-1, 1) and omega in (-1, 1)
    H, c, a = 4*(A-2)+3, pell(A, p)[1], A-2
    T = state_period(A, E) if period is None else period
    assert T >= 1 and pell_mod(A, T, E) == (1, 0)
    values = canonical_input_residues(A, p)
    result = []
    for r, fr in enumerate(values):
        base_index = input_index_class(A, p, u, r)
        if base_index is None:
            continue
        rhs_c = K-M*C-M*fr+epsilon-lam-omega*p
        rho_c = linear_class(M*H, rhs_c, c)
        if positive_interval(rho_c, gamma) is None:
            continue
        for t in range(T):
            index = crt(base_index, (t, T))
            if index is None:
                continue
            x, y = pell_mod(A, t, E)
            ft = (x+a*y) % E
            rhs_E = K-M*C-M*ft+epsilon-k
            rho_E = linear_class(M*H, rhs_E, E)
            rho = None if rho_E is None else positive_interval(crt(rho_c, rho_E), gamma)
            if rho:
                result.append(dict(r=r, t=t, input_index=list(index), rho=rho))
    return dict(period=T, classes=result)


def restore(parameters, record, rho_offset=0, index_offset=1):
    """Produce a positive subsystem extension by increasing its index lift."""
    A, p, E, M, C, K, k, gamma, u, epsilon, lam, omega = parameters
    c, delta, a, H = pell(A, p)[1], A*A-1, A-2, 4*(A-2)+3
    progression = record['rho']
    assert 0 <= rho_offset < progression['count'] and index_offset >= 0
    rho = progression['first']+rho_offset*progression['step']
    base, step = record['input_index']
    v = base+index_offset*step
    while True:
        chi, psi = pell(A, v)
        Z = C+rho*H+chi+a*psi
        R = K-M*Z
        if v > 0 and psi > u and R < 0 and k-R-epsilon > 0:
            break
        v += step
    assert (psi-u) % delta == 0 and (k-R-epsilon) % E == 0
    gap, h = (psi-u)//delta, (k-R-epsilon)//E
    mu = C-Z+a*psi+rho*H
    assert mu == -chi and mu*mu-delta*psi*psi == 1
    assert min(gap, h, Z, rho, gamma-rho) > 0
    assert k-R-h*E == epsilon
    assert (R+epsilon-lam-omega*p) % c == 0
    return dict(v=v, rho=rho, delta_gap=gap, h=h, Z=Z, R=R, mu=mu,
                kappa=psi, sigma=gamma-rho)


def elementary_audit():
    rng = random.Random(860021)
    congruences = periods = classes = 0
    for A in range(3, 13):
      delta = A*A-1
      for p in range(3, 14, 2):
        c = pell(A, p)[1]
        residues = canonical_input_residues(A, p)
        assert pell_mod(A, 2*p, c) == (1, 0)
        for _ in range(24):
            v = rng.randrange(1, 10**24)
            x, y = pell_mod(A, v, c)
            assert (x+(A-2)*y) % c == residues[v % (2*p)]
            yd = pell_mod(A, v, delta)[1]
            assert yd == (v if v % 2 else A*v) % delta
            congruences += 1
      for E in range(2, 21):
        T = state_period(A, E)
        assert T <= E*E and pell_mod(A, T, E) == (1, 0)
        for v in (0, 1, T-1, T+1, 10**18+17):
            assert pell_mod(A, v, E) == pell_mod(A, v % T, E)
        periods += 1
    for m in range(1, 18):
      for n in range(1, 18):
       for _ in range(4):
        r, s = rng.randrange(m), rng.randrange(n)
        answer = crt((r, m), (s, n))
        brute = [v for v in range(lcm(m, n)) if v % m == r and v % n == s]
        assert brute == ([] if answer is None else [answer[0]])
        classes += 1
    return dict(pell_residue_and_discriminant_cases=congruences,
                modular_state_periods=periods, independent_CRT_intersections=classes)


def subsystem_audit():
    """Finite complete-period checks and positive lifts on small algebraic hosts."""
    rng = random.Random(862004)
    hosts = visits = positive = with_classes = 0
    fingerprints = []
    for A in (3, 4, 5, 6):
      for p in (3, 5):
       for E in (2, 3, 4, 5):
        delta, a, H, c = A*A-1, A-2, 4*(A-2)+3, pell(A, p)[1]
        T = state_period(A, E)
        period = lcm(2*p, delta, T)
        for forced in (False, True):
            M, C, gamma = rng.randrange(1, 5), rng.randrange(4), rng.randrange(2, 7)
            epsilon, lam, omega = [rng.choice((-1, 1)) for _ in range(3)]
            if forced:
                v0, rho0 = rng.randrange(1, period+1), rng.randrange(1, gamma)
                chi0, psi0 = pell_mod(A, v0, c*E*delta)
                u = psi0 % delta or delta
                F0 = chi0+a*psi0
                K = (M*C+M*rho0*H+M*F0-epsilon+lam+omega*p) % c or c
                k = (K-M*C-M*rho0*H-M*F0+epsilon) % E or E
            else:
                K, k, u = rng.randrange(1, c+1), rng.randrange(1, E+1), rng.randrange(1, delta+1)
            parameters = (A, p, E, M, C, K, k, gamma, u, epsilon, lam, omega)
            answer = classify(*parameters, period=T)
            actual = set()
            for record in answer['classes']:
                vr, vp = record['input_index']
                assert vp == period
                for j in range(record['rho']['count']):
                    rho = record['rho']['first']+j*record['rho']['step']
                    actual.add((vr, rho))
            expected = set()
            chi, psi = 1, 0
            for v in range(period):
                # Independent sequential Pell-state oracle at common modulus.
                if (psi-u) % delta == 0:
                    for rho in range(1, gamma):
                        R = K-M*(C+rho*H+chi+a*psi)
                        if ((R+epsilon-lam-omega*p) % c == 0 and
                                (k-R-epsilon) % E == 0):
                            expected.add((v, rho))
                chi, psi = ((A*chi+delta*psi) % (c*E*delta),
                            (chi+A*psi) % (c*E*delta))
                visits += 1
            assert actual == expected
            if forced:
                assert actual
            if actual:
                with_classes += 1
                for record in answer['classes'][:2]:
                    for offset in (0, record['rho']['count']-1):
                        restored = restore(parameters, record, offset)
                        fingerprints.append([A, p, E, restored['v'], restored['rho'],
                                             restored['R'].bit_length()])
                        positive += 1
            hosts += 1
    return dict(small_algebraic_hosts=hosts, full_period_index_visits=visits,
        hosts_with_subsystem_solutions=with_classes, positive_subsystem_extensions=positive,
        extension_fingerprint_sha256=hashlib.sha256(json.dumps(fingerprints).encode()).hexdigest(),
        scope='These hosts audit only the stated subsystem. They do not satisfy or claim the full compiler contract.')


def actual_ratio_tuple_exclusion():
    """All actual masks/offsets/positive outer slacks at the gap-nine survivor."""
    d, B, J, q, X, Y, n, p = 4, 16, 1, 16, 1 << 21, 8192, 15, 21
    a, A = Y*(X+1), Y*(X+1)+2
    delta, H, M = A*A-1, 4*a+3, q*q-1
    chi, c = pell(A, p)
    k = 2*pell(2*X*Y*Y+1, n)[1]
    assert k*Y < c < k*(Y+1)
    assert (chi-a*c-X) % H == 0
    gamma = (chi-a*c-X)//H
    assert gamma >= 2
    assert (q-2)//(2*d) == 1  # Positive F,alpha and C>=0 force x=1.
    masks = [(MC, MF) for MC in range(2, B-1, 4) for MF in range(4, B-1, 8)
             if MC.bit_count()+MF.bit_count() == d]
    assert masks == [(6, 12), (10, 12), (14, 4)]
    residues = canonical_input_residues(A, p)
    g, index_gcd = gcd(M*H, c), gcd(2*p, delta)
    assert g == 15 and index_gcd == 21
    counts, records = Counter(), []
    for MC, MF in masks:
     for b in range(1, B):
      u = 2*d+b
      for F in range(1, q-2*d):
       for alpha in range(1, q-2*d-F+1):
        C = q-F-alpha-2*d
        K = q*(q-F)*M+(MC+q*(MF+B-1))*J
        for epsilon in (-1, 1):
         for lam in (-1, 1):
          for omega in (-1, 1):
           for r, fr in enumerate(residues):
            if input_index_class(A, p, u, r) is None:
                continue
            counts['compatible_cases'] += 1
            rhs = K-M*C-M*fr+epsilon-lam-omega*p
            residue_class = linear_class(M*H, rhs, c)
            if residue_class is None:
                counts['gcd_rejections'] += 1
            else:
                assert positive_interval(residue_class, gamma) is None
                counts['interval_rejections'] += 1
                first = residue_class[0] or residue_class[1]
                assert first >= gamma
                records.append([MC, MF, b, F, alpha, epsilon, lam, omega, r,
                                str(first), str(gamma)])
    assert dict(counts) == dict(compatible_cases=20160, gcd_rejections=19320,
                               interval_rejections=840)
    return dict(q=q, B=B, J=J, X=X, Y=Y, n=n, p=p, masks=[list(t) for t in masks],
        input_offsets=15, positive_F_alpha_pairs=28, independent_sign_triples=8,
        gcd_MH_c=g, gcd_2p_Delta=index_gcd, c_bits=c.bit_length(), gamma_bits=gamma.bit_length(),
        counts=dict(counts), exact_interval_certificates=records,
        scope='No full positive86 zero with mu<0 can have this main/first ratio tuple. '
              'The enumeration omits transport and first-index restrictions, so excludes their superset; '
              'it is not a classification of all negative-input main solutions.')


def verify():
    return dict(status='PASS_SCOPED_NEGATIVE_INPUT_RESIDUE_CLASSIFICATION',
        source=inherited.source_contract(), elementary=elementary_audit(),
        subsystem=subsystem_audit(), actual_ratio_tuple=actual_ratio_tuple_exclusion(),
        conclusion='For fixed main/first data, the stated negative-input subsystem has an exact finite '
                   'CRT classification; all actual masks/offsets fail at the specified gap-nine ratio tuple.',
        scope='The full86 candidate remains unresolved. No complete positive zero or uniform '
              'negative-input exclusion is claimed; positive-mu gaps>=13 also remain open.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    arguments = parser.parse_args()
    result = verify()
    target = Path(__file__).with_suffix('.json')
    if arguments.write:
        target.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(target.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['conclusion'])
    print(result['scope'])
