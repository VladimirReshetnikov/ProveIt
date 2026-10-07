#!/usr/bin/env python3
"""Finite diagnostics for sharp torsion-sensitive three-term estimates.

The article's proofs are deductive. Exact integer checks below verify fiber
identities and explicit witnesses on the enumerated systems. NumPy checks are
independent floating-point diagnostics, not a formal proof or a substitute for
any argument in the article. Run without -O; assertions are intentional.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import json
from math import gcd, prod
from pathlib import Path
from typing import Sequence

import numpy as np

if not __debug__:
    raise RuntimeError('Run without -O or -OO: verification uses assertions.')

SEED = 20261007
TOL = 2e-8
Element = tuple[int, ...]


@dataclass(frozen=True)
class Group:
    moduli: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.moduli or any(m < 1 for m in self.moduli):
            raise ValueError('Moduli must be a nonempty tuple of positive integers.')

    @property
    def elements(self) -> tuple[Element, ...]:
        return tuple(product(*(range(m) for m in self.moduli)))

    @property
    def zero(self) -> Element:
        return (0,) * len(self.moduli)

    @property
    def size(self) -> int:
        return prod(self.moduli)

    def add(self, x: Element, y: Element) -> Element:
        return tuple((a+b) % m for a, b, m in zip(x, y, self.moduli))

    def neg(self, x: Element) -> Element:
        return tuple((-a) % m for a, m in zip(x, self.moduli))

    def sub(self, x: Element, y: Element) -> Element:
        return self.add(x, self.neg(y))

    def phase(self, xi: Element, x: Element) -> Fraction:
        return sum((Fraction(a*b, m) for a, b, m in
                    zip(xi, x, self.moduli)), Fraction()) % 1

    def character(self, xi: Element, x: Element) -> complex:
        return np.exp(2j*np.pi*float(self.phase(xi, x)))

    def character_matrix(self) -> np.ndarray:
        return np.array([[self.character(xi, x) for xi in self.elements]
                         for x in self.elements])


@dataclass(frozen=True)
class Hom:
    domain: Group
    codomain: Group
    matrix: tuple[tuple[int, ...], ...]

    def __post_init__(self) -> None:
        if len(self.matrix) != len(self.codomain.moduli):
            raise ValueError('Wrong number of homomorphism rows.')
        for row, n in zip(self.matrix, self.codomain.moduli):
            if len(row) != len(self.domain.moduli):
                raise ValueError('Wrong number of homomorphism columns.')
            if any(a*m % n for a, m in zip(row, self.domain.moduli)):
                raise ValueError('Matrix does not define a homomorphism.')

    def __call__(self, x: Element) -> Element:
        return tuple(sum(a*b for a, b in zip(row, x)) % n
                     for row, n in zip(self.matrix, self.codomain.moduli))

    def dual(self, xi: Element) -> Element:
        ans = []
        for j, m in enumerate(self.domain.moduli):
            q = sum((Fraction(xi[i]*self.matrix[i][j]*m, n)
                     for i, n in enumerate(self.codomain.moduli)), Fraction())
            assert q.denominator == 1
            ans.append(int(q) % m)
        return tuple(ans)

    @property
    def image(self) -> set[Element]:
        return {self(x) for x in self.domain.elements}


def random_hom(domain: Group, codomain: Group,
               rng: np.random.Generator) -> Hom:
    matrix = tuple(tuple(int(rng.integers(gcd(m, n))) * (n//gcd(m, n))
                         for m in domain.moduli) for n in codomain.moduli)
    return Hom(domain, codomain, matrix)


def lp(x: np.ndarray, p: float) -> float:
    if p == np.inf:
        return float(np.max(np.abs(x)))
    return float(np.sum(np.abs(x)**p)**(1/p))


def op(x: np.ndarray) -> float:
    return float(np.linalg.svd(x, compute_uv=False)[0]) if x.size else 0.0


class System:
    def __init__(self, A: Hom, B: Hom):
        if A.domain != B.domain or A.codomain != B.codomain:
            raise ValueError('Increment homomorphisms must have common domain/codomain.')
        self.A, self.B, self.G, self.D = A, B, A.codomain, A.domain
        self.E = self.G.elements
        self.index = {x: j for j, x in enumerate(self.E)}
        self.a = {x: A.dual(x) for x in self.E}
        self.b = {x: B.dual(x) for x in self.E}
        self.U = {x for x in self.E if self.a[x] == self.D.zero}
        self.V = {x for x in self.E if self.b[x] == self.D.zero}
        self.L = self.U & self.V
        self.K = {self.G.add(x, y) for x in self.U for y in self.V}
        self.W = {x for x in self.E if self.a[x] == self.b[x]}
        self.u, self.v, self.ell, self.k = map(len, (self.U, self.V, self.L, self.K))
        self.C = (self.u*self.v*self.ell)**0.25
        self.I = set(self.a.values()) & set(self.b.values())
        self.blocks = []
        self.Sigma: set[Element] = set()
        for t in sorted(self.I):
            rows = [x for x in self.E if self.a[x] == t]
            cols = [x for x in self.E if self.b[x] == self.D.neg(t)]
            support = frozenset(self.G.neg(self.G.add(x, y))
                                for x in rows for y in cols)
            self.blocks.append((t, rows, cols, support))
            self.Sigma.update(support)
        self.RU = self.representatives(self.U, self.L)
        self.RV = self.representatives(self.V, self.L)
        # Characters of L represented by distinct restrictions from the dual
        # of Gamma, canonically identified with G for our product coordinates.
        seen = set()
        self.characters = []
        for xi in self.E:
            signature = tuple(self.G.phase(xi, z) for z in sorted(self.L))
            if signature not in seen:
                self.characters.append(xi)
                seen.add(signature)
        assert len(self.characters) == self.ell

    def representatives(self, subgroup: set[Element],
                        smaller: set[Element]) -> list[Element]:
        todo = set(subgroup)
        ans = []
        while todo:
            x = min(todo)
            ans.append(x)
            todo -= {self.G.add(x, y) for y in smaller}
        return ans

    def constant(self, p: float) -> float:
        return (self.ell**(1-1/p) if p <= 2 else
                (self.u*self.v)**0.5*self.k**(-1/p))

    def matrix(self, F: np.ndarray) -> np.ndarray:
        n = self.G.size
        M = np.zeros((n, n), dtype=complex)
        for _, rows, cols, _ in self.blocks:
            for x in rows:
                for y in cols:
                    M[self.index[x], self.index[y]] = F[self.index[
                        self.G.neg(self.G.add(x, y))]]
        return M

    def block_matrix(self, F: np.ndarray, rows: Sequence[Element],
                     cols: Sequence[Element]) -> np.ndarray:
        return np.array([[F[self.index[self.G.neg(self.G.add(x, y))]]
                          for y in cols] for x in rows])

    def coefficient_matrix(self, F: np.ndarray, s: Element,
                           chi: Element) -> np.ndarray:
        return np.array([[sum(F[self.index[self.G.add(s, self.G.add(
            r, self.G.add(t, z)))]] * np.conj(self.G.character(chi, z))
            for z in self.L)/self.ell for t in self.RV] for r in self.RU])

    def physical_average(self, f: np.ndarray, g: np.ndarray,
                         h: np.ndarray) -> complex:
        ans = 0j
        for x in self.E:
            for d in self.D.elements:
                ans += (f[self.index[x]] * g[self.index[self.G.add(x, self.A(d))]]
                        * h[self.index[self.G.add(x, self.B(d))]])
        return ans/(self.G.size*self.D.size)

    def exact_checks(self) -> dict:
        assert self.u*self.v == self.ell*self.k
        assert self.u == self.G.size//len(self.A.image)
        assert self.v == self.G.size//len(self.B.image)
        sum_images = {self.G.add(x, y) for x in self.A.image for y in self.B.image}
        assert self.ell == self.G.size//len(sum_images)
        assert self.k == self.G.size//len(self.A.image & self.B.image)
        counts = Counter()
        for _, rows, cols, support in self.blocks:
            fibers = Counter(self.G.neg(self.G.add(x, y)) for x in rows for y in cols)
            assert len(rows) == self.u and len(cols) == self.v
            assert set(fibers.values()) == {self.ell}
            assert len(support) == self.k
            counts[support] += 1
        assert set(counts.values()) == {len(self.W)//self.ell}
        assert len(self.I)*self.ell == len(counts)*len(self.W)
        assert len(self.Sigma) == len(counts)*self.k
        # Unscaled Fourier subgroup witnesses, exact rational ratios.
        ratio_fourth = Fraction((self.u*self.v)**4,
                                self.k*self.u**2*self.v**2)
        assert ratio_fourth == self.u*self.v*self.ell
        # Indicator witness in physical space: x in A(D) intersect B(D).
        IA, IB = self.A.image, self.B.image
        IH = IA & IB
        total = sum(x in IH and self.G.add(x, self.A(d)) in IA
                    and self.G.add(x, self.B(d)) in IB
                    for x in self.E for d in self.D.elements)
        assert Fraction(total, self.G.size*self.D.size) == Fraction(1, self.k)
        return {'G': self.G.moduli, 'D': self.D.moduli,
                'A': self.A.matrix, 'B': self.B.matrix,
                'u': self.u, 'v': self.v, 'ell': self.ell, 'k': self.k,
                'w': len(self.W), 'C4_fourth': int(ratio_fourth),
                'accessible_cosets': len(counts)}

    def numerical_checks(self, rng: np.random.Generator) -> dict:
        F = rng.normal(size=self.G.size) + 1j*rng.normal(size=self.G.size)
        M = self.matrix(F)
        norm = op(M)
        max_ratio = 0.0
        for p in (1.0, 1.5, 2.0, 3.0, 4.0, 8.0, np.inf):
            bound = self.constant(p)*lp(F, p)
            assert norm <= bound + TOL
            max_ratio = max(max_ratio, norm/bound)
            H = self.L if p <= 2 else self.K
            witness = np.array([float(x in H) for x in self.E])
            assert abs(op(self.matrix(witness))/lp(witness, p)-self.constant(p)) < TOL
        # Check the entire nonzero singular spectrum via the common-kernel DFT.
        reduced = []
        seen = set()
        multiplicity = len(self.W)//self.ell
        for _, _, _, support in self.blocks:
            if support in seen:
                continue
            seen.add(support)
            s = min(support)
            for chi in self.characters:
                small = self.coefficient_matrix(F, s, chi)
                vals = np.linalg.svd(small, compute_uv=False)*self.ell
                for z in vals:
                    if z > 1e-10:
                        reduced.extend([float(z)]*multiplicity)
        actual = [float(x) for x in np.linalg.svd(M, compute_uv=False) if x > 1e-10]
        assert len(actual) == len(reduced)
        error_spectrum = float(np.max(np.abs(np.sort(actual)-np.sort(reduced))))
        assert error_spectrum < TOL
        # Independently verify the physical Fourier identity.
        G = rng.normal(size=self.G.size) + 1j*rng.normal(size=self.G.size)
        H = rng.normal(size=self.G.size) + 1j*rng.normal(size=self.G.size)
        chars = self.G.character_matrix()
        physical = self.physical_average(chars@F, chars@G, chars@H)
        spectral = G @ M @ H
        error_fourier = float(abs(physical-spectral))
        assert error_fourier < TOL*max(1, abs(spectral))
        return {'max_random_norm_ratio': max_ratio,
                'spectrum_error': error_spectrum, 'fourier_error': error_fourier}

    def flat_extremizer(self, s: Element, chi: Element,
                        left: np.ndarray, right: np.ndarray) -> np.ndarray:
        """Lift phases on U/L and V/L; zero coordinates receive phase 1."""
        def phase(z: complex) -> complex:
            return z/abs(z) if abs(z) > 1e-14 else 1+0j
        F = np.zeros(self.G.size, dtype=complex)
        for i, r in enumerate(self.RU):
            for j, t in enumerate(self.RV):
                for z in self.L:
                    x = self.G.add(s, self.G.add(r, self.G.add(t, z)))
                    F[self.index[x]] = (self.k**(-0.25)*phase(left[i]) *
                        np.conj(phase(right[j]))*self.G.character(chi, z))
        return F

    def repair(self, F: np.ndarray) -> tuple[np.ndarray, frozenset[Element]]:
        """Construct the exact extremal marked spectrum from the proof."""
        best = None
        seen = set()
        for _, _, _, support in self.blocks:
            if support in seen:
                continue
            seen.add(support)
            s = min(support)
            for chi in self.characters:
                matrix = self.coefficient_matrix(F, s, chi)
                left, values, right_h = np.linalg.svd(matrix, full_matrices=False)
                score = self.ell*values[0]
                if best is None or score > best[0]:
                    best = (score, support, s, chi, left[:, 0], right_h[0].conj())
        assert best is not None
        _, support, s, chi, left, right = best
        return self.flat_extremizer(s, chi, left, right), support

    def stability_checks(self, rng: np.random.Generator, trials: int = 2) -> list[dict]:
        results = []
        for trial in range(trials):
            support = self.blocks[trial % len(self.blocks)][3]
            s = min(support)
            chi = self.characters[trial % len(self.characters)]
            left = np.exp(2j*np.pi*rng.random(len(self.RU)))
            right = np.exp(2j*np.pi*rng.random(len(self.RV)))
            E = self.flat_extremizer(s, chi, left, right)
            noise = rng.normal(size=self.G.size)+1j*rng.normal(size=self.G.size)
            noise /= lp(noise, 4)
            F = E + (0.003 if trial == 0 else 0.015)*noise
            F /= lp(F, 4)
            M = self.matrix(F)
            uu, sv, vv = np.linalg.svd(M, full_matrices=False)
            g, h = uu[:, 0], vv[0].conj()
            # Perturb a near-maximizing pair; not just the matrix norm.
            ng = rng.normal(size=self.G.size)+1j*rng.normal(size=self.G.size)
            nh = rng.normal(size=self.G.size)+1j*rng.normal(size=self.G.size)
            g = g+0.001*ng/np.linalg.norm(ng)
            h = h+0.001*nh/np.linalg.norm(nh)
            g /= np.linalg.norm(g); h /= np.linalg.norm(h)
            z = np.vdot(g, M@h)
            eps = max(0.0, 1-abs(z)/self.C)
            assert eps <= 1/64 + TOL
            Q, S = self.repair(F)
            MQ = self.matrix(Q)
            assert abs(lp(Q, 4)-1) < TOL
            assert abs(op(MQ)-self.C) < TOL
            distance_f = lp(F-Q, 4)
            assert distance_f <= 4*eps**0.25 + TOL
            c = self.k**(-0.25)
            target_squared = np.array([c*c if x in S else 0 for x in self.E])
            amp_defect = np.linalg.norm(np.abs(F)**2-target_squared)
            assert amp_defect <= 2*np.sqrt(eps)+TOL
            outside = sum(abs(F[self.index[x]])**4 for x in self.E if x not in S)
            assert outside <= 4*eps+TOL
            # Match the original top singular vectors to the flattened model.
            # All test cases here have nonzero quotient amplitudes; the proof
            # handles zeros via the character-sector construction above.
            weights, pieces = [], []
            for _, rows, cols, sup in self.blocks:
                if sup != S:
                    continue
                ri = [self.index[x] for x in rows]
                ci = [self.index[x] for x in cols]
                block = M[np.ix_(ri, ci)]
                u1, val, v1h = np.linalg.svd(block, full_matrices=False)
                u1, v1 = u1[:, 0], v1h[0].conj()
                qblock = MQ[np.ix_(ri, ci)]
                # Because Q is the phase flattening of the same rank-one
                # block, its flat right vector is phase(v1)/sqrt(v).
                v0 = np.exp(1j*np.angle(v1))/np.sqrt(self.v)
                u0 = qblock@v0/self.C
                assert abs(np.linalg.norm(u0)-1) < 1e-7
                assert np.linalg.norm(u1-u0) <= 4*np.sqrt(eps)+1e-7
                weight = np.vdot(v1, h[ci])
                weights.append(weight)
                pieces.append((ri, ci, u0, v0))
            weight_norm = np.linalg.norm(weights)
            gs = np.zeros_like(g); hs = np.zeros_like(h)
            rotation = np.exp(-1j*np.angle(z))
            for weight, (ri, ci, u0, v0) in zip(weights, pieces):
                hs[ci] = weight/weight_norm*v0
                gs[ri] = rotation*weight/weight_norm*u0
            assert abs(abs(np.vdot(gs, MQ@hs))-self.C) < TOL
            dg, dh = np.linalg.norm(g-gs), np.linalg.norm(h-hs)
            assert dg <= 7*np.sqrt(eps)+1e-7
            assert dh <= 7*np.sqrt(eps)+1e-7
            results.append({'epsilon': eps, 'marked_l4_distance': distance_f,
                            'other_l2_distances': [float(dg), float(dh)],
                            'outside_l4_power': float(outside)})
        return results


def build_systems(rng: np.random.Generator, quick: bool) -> list[System]:
    systems = []
    for n in range(1, 9 if quick else 13):
        G = Group((n,))
        for a in range(n):
            for b in range(n):
                systems.append(System(Hom(G, G, ((a,),)), Hom(G, G, ((b,),))))
    types = [((2, 2), (2, 2)), ((2, 3), (2, 3)), ((4, 2), (4, 2)),
             ((3, 3), (3, 3)), ((4, 4), (4, 4)), ((2, 2, 2), (2, 2, 2)),
             ((6,), (2,)), ((2,), (6,)), ((4, 2), (2, 2)), ((6,), (4, 3))]
    for dm, gm in types:
        D, G = Group(dm), Group(gm)
        for _ in range(4 if quick else 10):
            systems.append(System(random_hom(D, G, rng), random_hom(D, G, rng)))
    return systems


def check_counting(rng: np.random.Generator) -> dict:
    cases, error = 0, 0.0
    for mods in ((2,), (3,), (4,), (5,), (6,), (8,), (2, 2), (4, 2), (3, 3)):
        G = Group(mods); E = G.elements; ix = {x: i for i, x in enumerate(E)}
        chars = G.character_matrix()
        two_image = {G.add(x, x) for x in E}
        torsion = {x for x in E if G.add(x, x) == G.zero}
        two_dual = two_image
        for _ in range(12):
            vals = [(rng.random(G.size)<rng.uniform(0.15, 0.85)).astype(float)
                    for j in range(3)]
            f, g, h = vals
            alpha, beta, gamma = (float(v.mean()) for v in vals)
            count = sum(f[ix[x]]*g[ix[G.add(x, d)]]*h[ix[G.add(x, G.add(d, d))]]
                        for x in E for d in E)/G.size**2
            pair = sum(f[ix[x]]*h[ix[G.add(x, y)]] for x in E for y in two_image)
            pair /= G.size*len(two_image)
            gh = chars.conj().T@g/G.size
            rho = max([abs(gh[ix[x]]) for x in two_dual if x != G.zero]+[0.0])
            pa = np.array([sum(f[ix[G.add(x, y)]] for y in two_image)/len(two_image)
                           for x in E])
            pc = np.array([sum(h[ix[G.add(x, y)]] for y in two_image)/len(two_image)
                           for x in E])
            variance_a = max(0.0, alpha-float(np.mean(pa**2)))
            variance_c = max(0.0, gamma-float(np.mean(pc**2)))
            residual_bound = np.sqrt(variance_a*variance_c)*rho
            assert abs(count-beta*pair) <= residual_bound+TOL
            proper = sum(f[ix[x]]*g[ix[G.add(x, d)]]*h[ix[G.add(x, G.add(d, d))]]
                         for x in E for d in E if d not in torsion)/G.size**2
            intersection_density = float(np.mean(f*h))
            lower = beta*pair-residual_bound-len(torsion)/G.size*intersection_density
            assert proper >= lower-TOL
            if len(torsion) == G.size:
                error = max(error, abs(count-beta*pair))
            cases += 1
    return {'indicator_cases': cases, 'exponent_two_identity_error': float(error)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'verification.json')
    args = parser.parse_args()
    rng = np.random.default_rng(SEED)
    systems = build_systems(rng, args.quick)
    exact = [s.exact_checks() for s in systems]
    # All systems receive exact tests; a deterministic subset receives DFT/SVD
    # diagnostics, including every noncyclic and unequal-domain system.
    numerical_systems = [s for i, s in enumerate(systems)
                         if i % 7 == 0 or len(s.G.moduli)>1 or s.G != s.D]
    numerics = [s.numerical_checks(rng) for s in numerical_systems]
    stability = []
    for i, s in enumerate(numerical_systems):
        if i % 3 == 0 or (s.ell > 1 and s.u > s.ell and s.v > s.ell):
            stability.extend(s.stability_checks(rng))
    result = {
        'status': 'all checks passed', 'seed': SEED,
        'scope': 'Finite exact identities plus floating-point diagnostics; not formal verification.',
        'exact_systems': len(exact), 'numerical_systems': len(numerics),
        'stability_cases': len(stability),
        'max_spectrum_error': max(x['spectrum_error'] for x in numerics),
        'max_fourier_error': max(x['fourier_error'] for x in numerics),
        'max_random_norm_ratio': max(x['max_random_norm_ratio'] for x in numerics),
        'counting': check_counting(rng), 'exact_cases': exact,
        'stability_diagnostics': stability,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('exact_cases', 'stability_diagnostics')}, indent=2))
    print('Wrote', args.output)


if __name__ == '__main__':
    main()
