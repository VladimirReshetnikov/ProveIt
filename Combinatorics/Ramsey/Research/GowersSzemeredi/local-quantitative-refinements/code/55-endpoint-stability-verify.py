#!/usr/bin/env python3
"""Reproducible finite checks for the endpoint-stability manuscript.

These are computational diagnostics, not proof-assistant verification.
Exact checks use integers/Fraction; floating checks use declared tolerances.
Run: python code/verify.py --output data/verification_results.json
Dependencies: numpy, mpmath. No network or external data required.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
import json
import math
from pathlib import Path
import platform
import sys
import time

import mpmath as mp
import numpy as np

SEED = 20261006


def constants(d: int) -> dict:
    if d < 2:
        raise ValueError("d must be at least 2")
    q = 2**d
    C = (6**d - 2 * 4**d + 2**d) // 8
    A = q * (q - 1) * (q - 2) // 24
    B = 10 * (math.comb(q, 5) if q >= 5 else 0)
    B += sum(math.comb(q, s) * 2 ** (s - 6) for s in range(6, q + 1))
    K0 = Fraction(q * (q - 1), 8)
    Kmax = K0 + A
    Hmax = B + C
    radius = min(0.5, q / (16 * (float(Kmax) + 1)),
                 math.sqrt(q / (8 * (B + 2 * C + 1))))
    c = Fraction(q, 2)
    R = 12 * Kmax**2 / c**5 + 24 * Kmax * Hmax / c**6 + 8 * Hmax / c**4
    odd = Fraction(3**d - 1, 2 * 4**d)
    even = Fraction(4**d - 1, 3 * 4**d)
    assert (K0 + Fraction(C, 2)) / c**3 == odd
    assert (K0 + A) / c**3 == even
    return dict(d=d, q=q, C=C, A=A, J=A-C, B=B, K0=K0,
                radius=radius, R=R, odd=odd, even=even)


def det3(a: tuple[int, int, int], b: tuple[int, int, int],
         c: tuple[int, int, int]) -> int:
    return (a[0]*(b[1]*c[2]-b[2]*c[1])
            -a[1]*(b[0]*c[2]-b[2]*c[0])
            +a[2]*(b[0]*c[1]-b[1]*c[0]))


def census(d: int) -> dict:
    counts = Counter()
    checked_minors = 0
    for vertices in combinations(range(2**d), 4):
        a, b, c, e = vertices
        pairings = ((a, b, c, e), (a, c, b, e), (a, e, b, c))
        ordinary = any((x ^ y) == (z ^ w) and (x & y) == (z & w)
                       for x, y, z, w in pairings)
        xor_zero = (a ^ b ^ c ^ e) == 0
        typ = "ordinary" if ordinary else "exceptional" if xor_zero else "independent"
        counts[typ] += 1
        if d <= 4:
            rows = [tuple(((v ^ a) >> j) & 1 for j in range(d)) for v in (b, c, e)]
            determinants = []
            for cols in combinations(range(d), 3):
                r = [tuple(row[j] for j in cols) for row in rows]
                determinants.append(det3(*r))
            gcd = math.gcd(*determinants) if determinants else 0
            assert gcd == {"ordinary": 0, "exceptional": 2, "independent": 1}[typ]
            checked_minors += 1
    k = constants(d)
    assert counts["ordinary"] == k["C"]
    assert counts["exceptional"] == k["J"]
    assert counts["ordinary"] + counts["exceptional"] == k["A"]
    return {"dimension": d, "four_subsets": math.comb(2**d, 4),
            "ordinary": counts["ordinary"], "exceptional": counts["exceptional"],
            "independent": counts["independent"],
            "exact_minor_gcd_checks": checked_minors}


@dataclass
class Group:
    moduli: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.moduli or any(m < 2 for m in self.moduli):
            raise ValueError("Use a nontrivial product of cyclic groups")
        self.elements = tuple(product(*(range(m) for m in self.moduli)))
        self.n = len(self.elements)
        lookup = {x: j for j, x in enumerate(self.elements)}
        self.add = np.array([[lookup[tuple((x+y) % m for x, y, m in zip(a, b, self.moduli))]
                              for b in self.elements] for a in self.elements], dtype=np.int64)
        self.characters = np.array([
            [np.exp(2j*np.pi*sum(x*k/m for x,k,m in zip(a,b,self.moduli)))
             for a in self.elements] for b in self.elements], dtype=np.complex128)
        self.two_indices = [j for j,b in enumerate(self.elements)
                            if j and all((2*k) % m == 0 for k,m in zip(b,self.moduli))]
        self.cube_cache: dict[int,np.ndarray] = {}

    def cubes(self, d: int) -> np.ndarray:
        if d not in self.cube_cache:
            args = np.indices((self.n,) * (d+1), dtype=np.int64).reshape(d+1,-1)
            vertices = []
            for mask in range(2**d):
                index = args[0].copy()
                for j in range(d):
                    if (mask >> j) & 1:
                        index = self.add[index, args[j+1]]
                vertices.append(index)
            self.cube_cache[d] = np.array(vertices)
        return self.cube_cache[d]

    def u_power(self, f: np.ndarray, d: int) -> float:
        values = f[self.cubes(d)].astype(np.complex128)
        for mask in range(2**d):
            if mask.bit_count() % 2:
                values[mask] = values[mask].conjugate()
        result = np.prod(values, axis=0).mean()
        assert abs(result.imag) < 2e-11
        return float(result.real)

    def quartic(self, h: np.ndarray, d: int) -> complex:
        values = h[self.cubes(d)].astype(np.complex128)
        for mask in range(2**d):
            if mask.bit_count() % 2:
                values[mask] = values[mask].conjugate()
        coeff = [np.ones(values.shape[1], dtype=np.complex128)]
        coeff += [np.zeros(values.shape[1], dtype=np.complex128) for _ in range(4)]
        for value in values:
            for j in range(4,0,-1):
                coeff[j] += value*coeff[j-1]
        return complex(coeff[4].mean())


def exact_real_checks(group: Group, d: int, rng: np.random.Generator) -> dict:
    n = group.n
    raw = rng.integers(-2,3,size=n)
    b = n*raw - int(raw.sum())  # centered integers
    assert int(b.sum()) == 0
    values = b[group.cubes(d)]
    q = 2**d
    coeff = [np.ones(values.shape[1],dtype=np.int64)]
    coeff += [np.zeros(values.shape[1],dtype=np.int64) for _ in range(4)]
    for value in values:
        for j in range(4,0,-1):
            coeff[j] += value*coeff[j-1]
    Q = Fraction(int(coeff[4].sum()), n**(d+1))
    e4 = Fraction(int(np.prod(b[group.cubes(2)],axis=0).sum()), n**3)
    t4 = Fraction(0)
    for j in group.two_indices:
        signs = np.rint(group.characters[j].real).astype(np.int64)
        numerator = int(np.dot(b,signs))
        t4 += Fraction(numerator,n)**4
    k = constants(d)
    assert Q == k["C"]*e4 + k["J"]*t4
    signs = np.array([(-1)**mask.bit_count() for mask in range(q)],dtype=np.int64)
    S = signs @ values
    mu2 = Fraction(int(np.sum(b**2)),n)
    mu4 = Fraction(int(np.sum(b**4)),n)
    second = Fraction(int(np.sum(S**2)),n**(d+1))
    fourth = Fraction(sum(int(x)**4 for x in S),n**(d+1))
    assert second == q*mu2
    assert fourth == q*mu4 + 3*q*(q-1)*mu2**2 + 24*Q
    return {"group": list(group.moduli), "d": d, "Q": str(Q),
            "fourth_moment": str(fourth), "identities": 3}


def random_local_checks(group: Group, d: int, rng: np.random.Generator,
                        trials: int = 20) -> dict:
    k = constants(d)
    q,C,A,B = (k[key] for key in ("q","C","A","B"))
    odd = group.n % 2 == 1
    M = C/2 if odd else A
    L = C if odd else 0
    K = float(k["K0"]) + M
    H = B + L
    minimum_master_slack = float("inf")
    max_remainder_ratio = 0.0
    radius_cases = 0
    for trial in range(trials):
        scale = [0.003,0.02,0.08,0.22,0.4][trial % 5]
        amplitude = [0.0,scale**2,0.05,0.2][(trial//5) % 4]
        f = (1-amplitude*rng.random(group.n))*np.exp(1j*scale*rng.normal(size=group.n))
        f *= np.exp(-1j*np.angle(f.mean()))
        m = float(f.mean().real)
        h = f-m
        a = float(1-np.mean(abs(f)**2))
        D = float(np.mean(abs(f-1)**2))
        z = D+a
        v = float(np.mean(abs(h)**2))
        assert abs(v-(D-z*z/4)) < 2e-12
        F = group.u_power(f,d)
        eps = 1-F
        assert a <= eps+2e-11
        Q = group.quartic(h,d).real
        ft = group.characters.conjugate() @ h / group.n
        E4 = float(np.sum(abs(ft)**4))
        T4 = float(sum(abs(ft[j])**4 for j in group.two_indices))
        v2 = float(sum(abs(ft[j])**2 for j in group.two_indices))
        assert Q <= C*E4+(A-C)*T4+2e-11
        profile = A*v2**2 + C/2*(v-v2)**2 + C*z*z*(v-v2)
        assert Q <= profile+2e-11
        assert Q <= A*v*v+2e-11
        assert E4 <= v2**2+(v-v2)**2/2+z*z*(v-v2)+2e-11
        remainder = F-m**q-m**(q-4)*Q
        bound = B*(v+a)*v*v
        assert abs(remainder) <= bound+2e-11
        if bound > 1e-13:
            max_remainder_ratio = max(max_remainder_ratio,abs(remainder)/bound)
        if z <= 1:
            master = (1-z/2)**q + M*D*D+B*z*D*D+L*z*z*D
            minimum_master_slack = min(minimum_master_slack,master-F)
            assert F <= master+2e-11
        if z <= k["radius"]:
            radius_cases += 1
            lower = q/2*D-K*D*D-H*D**3+q/4*a
            assert eps >= lower-2e-11
            assert eps >= q/4*z-2e-11
            inv = 2/q*eps+float(k["odd"] if odd else k["even"])*eps**2+float(k["R"])*eps**3
            assert D <= inv+2e-11
    return {"group": list(group.moduli), "d": d, "trials": trials,
            "explicit_radius_cases": radius_cases,
            "minimum_master_slack": minimum_master_slack,
            "maximum_aggregate_remainder_bound_ratio": max_remainder_ratio,
            "absolute_tolerance": 2e-11}


def sharpness() -> list[dict]:
    mp.mp.dps = 85
    results = []
    for d in range(2,6):
        q=2**d
        # For b=sqrt(2) cos(2*pi*x/3), b=(2,-1,-1)/sqrt(2).
        S_count=Counter()
        for args in product(range(3),repeat=d+1):
            s=0
            for mask in range(q):
                x=(args[0]+sum(args[j+1] for j in range(d) if (mask>>j)&1))%3
                s += (-1)**mask.bit_count()*(2 if x==0 else -1)
            S_count[s]+=1
        for parity in ("odd","even"):
            rows=[]
            target=mp.mpf(3**d-1)/(2*4**d) if parity=="odd" else (1-mp.mpf(4)**(-d))/3
            for exponent in (1,2,3,4):
                t=mp.mpf(10)**(-exponent)
                if parity=="even":
                    eps=(1-mp.cos(q*t))/q
                    D=2*(1-mp.cos(t))
                    inv=2*(1-mp.cos(mp.acos(1-q*eps)/q))
                    # For t=0.1 and d=5, q*t exceeds pi; only use local inverse branch.
                    if q*t < mp.pi:
                        assert abs(inv-D)<mp.mpf('1e-70')
                else:
                    F=sum(count*mp.cos(t*s/mp.sqrt(2)) for s,count in S_count.items())/3**(d+1)
                    eps=1-F
                    mean=(mp.exp(1j*mp.sqrt(2)*t)+2*mp.exp(-1j*t/mp.sqrt(2)))/3
                    D=2*(1-abs(mean))
                ratio=(D-2*eps/q)/eps**2
                rows.append({"t":mp.nstr(t,8),"epsilon":mp.nstr(eps,28),
                             "second_coefficient_ratio":mp.nstr(ratio,28),
                             "difference_from_target":mp.nstr(ratio-target,20)})
            assert abs(ratio-target)<mp.mpf('0.00001')
            results.append({"d":d,"parity":parity,"target":mp.nstr(target,28),"rows":rows})
    return results


def exact_u2_diagnostics(groups: list[Group]) -> dict:
    """Check the full defect interval, not only the expansion at zero."""
    rng = np.random.default_rng(SEED + 2)
    random_in_range = 0
    attained_curve_cases = 0
    tolerance = 2e-7  # square-root endpoint conditioning at epsilon=1/2

    def modulus(epsilon: float) -> float:
        epsilon = max(0.0, min(0.5, epsilon))
        return 2*(1-math.sqrt((1+math.sqrt(1-2*epsilon))/2))

    for group in groups:
        for j in range(128):
            scale = (0.03, 0.15, 0.4, 0.8)[j % 4]
            radial = (0.0, 0.01, 0.05, 0.15)[(j//4) % 4]
            f = (1-radial*rng.random(group.n))*np.exp(
                1j*scale*rng.normal(size=group.n))
            coefficients = group.characters.conjugate() @ f / group.n
            s = float(np.mean(abs(f)**2))
            largest = float(max(abs(coefficients)))
            distance = 1+s-2*largest
            epsilon = 1-float(np.sum(abs(coefficients)**4))
            if epsilon <= 0.5:
                random_in_range += 1
                assert distance <= modulus(epsilon)+tolerance
        if group.two_indices:
            character = np.rint(group.characters[group.two_indices[0]].real)
            for t in np.linspace(0.0, math.pi/4, 51):
                f = np.exp(1j*t*character)
                coefficients = group.characters.conjugate() @ f / group.n
                distance = 2-2*float(max(abs(coefficients)))
                epsilon = 1-float(np.sum(abs(coefficients)**4))
                assert abs(distance-modulus(epsilon)) <= tolerance
                attained_curve_cases += 1
    return {"random_functions_tested": 128*len(groups),
            "random_functions_in_defect_range": random_in_range,
            "even_group_attained_curve_cases": attained_curve_cases,
            "absolute_tolerance": tolerance,
            "scope": "Floating diagnostics of Proposition 10.1 on the full interval [0,1/2]."}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('data/verification_results.json'))
    args=parser.parse_args()
    start=time.monotonic()
    rng=np.random.default_rng(SEED)
    census_results=[census(d) for d in range(2,6)]
    groups=[Group(m) for m in [(2,),(3,),(4,),(5,),(6,),(2,2),(3,3),(2,2,2)]]
    exact=[]
    local=[]
    for group in groups:
        for d in range(2,5):
            if d==4 and group.n>5:
                continue
            exact.append(exact_real_checks(group,d,rng))
            local.append(random_local_checks(group,d,rng))
    const_rows=[]
    for d in range(2,7):
        k=constants(d)
        const_rows.append({key:(str(value) if isinstance(value,Fraction) else value)
                           for key,value in k.items()})
    result={
        'status':'all assertions passed',
        'scope':'Finite diagnostics; not a proof or proof-assistant verification.',
        'seed':SEED,
        'environment':{'python':sys.version.split()[0],'numpy':np.__version__,
                       'mpmath':mp.__version__,'platform':platform.platform()},
        'census':census_results,
        'exact_real_cube_identities':exact,
        'random_complex_local_checks':local,
        'sharpness':sharpness(),
        'exact_u2_full_interval_diagnostics':exact_u2_diagnostics(groups),
        'constants':const_rows,
        'totals':{'four_vertex_subsets':sum(x['four_subsets'] for x in census_results),
                  'minor_gcd_checks':sum(x['exact_minor_gcd_checks'] for x in census_results),
                  'exact_moment_identities':sum(x['identities'] for x in exact),
                  'random_functions':sum(x['trials'] for x in local),
                  'explicit_radius_functions':sum(x['explicit_radius_cases'] for x in local)},
        'elapsed_seconds':round(time.monotonic()-start,3)}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':result['status'],'totals':result['totals'],
                      'output':str(args.output),'elapsed_seconds':result['elapsed_seconds']},indent=2))


if __name__=='__main__':
    main()
