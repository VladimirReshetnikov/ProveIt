#!/usr/bin/env python3
"""Independent bounded review; all author/predecessor programs remain inert."""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

AUTHOR = Path('/tmp/complete83_odd_primary_carry_budget')
AUTHOR_PINS = {
    '.md': '4b884c4d9cc6fd7100c67b98caee4ec9f968653e7a03c3d41558dc0d5cbc5f95',
    '.py': '3b2bc4461caa6f438c3fd6d5cdf0f11d457953555b451e852ba76268c58845e3',
    '.json': 'f7933d99ee19edc51031392c8596e76df7f5d494a6d2e4de35223a4cd056b0de',
}


def check(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def valuation(n, p):
    check(n != 0, 'valuation zero')
    n = abs(n)
    result = 0
    while n % p == 0:
        result += 1
        n //= p
    return result


def carries(n, p):
    """Count actual grade-school carries in n+n, independently of factorials."""
    count = incoming = 0
    while n:
        n, digit = divmod(n, p)
        incoming = int(2*digit+incoming >= p)
        count += incoming
    return count


class Poly:
    """Rational polynomial, monomials represented by sorted variable words."""
    def __init__(self, terms):
        self.terms = {m: Fraction(c) for m, c in terms.items() if c}

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Poly) else Poly({(): Fraction(x)})

    @staticmethod
    def var(x):
        return Poly({(x,): 1})

    def __add__(self, other):
        out = dict(self.terms)
        for m, c in self.coerce(other).terms.items():
            out[m] = out.get(m, 0)+c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self+-self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other)+-self

    def __mul__(self, other):
        out = {}
        for m, c in self.terms.items():
            for n, d in self.coerce(other).terms.items():
                key = tuple(sorted(m+n))
                out[key] = out.get(key, 0)+c*d
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        out = self.coerce(1)
        for _ in range(n):
            out = out*self
        return out

    def zero(self):
        return not self.terms


def source_and_congruence(raw):
    packet = json.loads(raw)['packet']
    rows = {r[0]: r for r in packet['source']}
    m, J, z, K, MC, MF = map(Poly.var, ('m', 'J', 'z', 'K', 'MC', 'MF'))
    env = {'Bm1': m, 'Jrep': J, 'Z': z, 'Kconstant': K, 'F': K*z, 'MC': MC, 'MF': MF}
    visited = set()
    def expand(name):
        if isinstance(name, int):
            return Poly.coerce(name)
        if name in env:
            return env[name]
        _, op, a, b = rows[name]
        x, y = expand(a), expand(b)
        env[name] = x+y if op == '+' else x-y if op == '-' else x*y
        visited.add(name)
        return env[name]
    actual_R = expand('r_lhs')
    q = m*J+1
    formula = q**4-K*z*q**3-(z+1)*q**2+K*z*q+z+(MC+q*MF)*J
    check((actual_R-formula).zero(), 'literal ancestor expansion with computed q and F=Kz')
    check(len(packet['source']) == 83 and len(packet['witnesses']) == 18, 'parent scope')
    A, c = Poly.var('A'), Poly.var('c')
    outputs = []
    for eps in (-1, 1):
        qA = (A**2+eps*A)*Fraction(1, 2)
        # Direct m-times source, using only the exact relation mJ=q-1.
        mR = m*(qA**2-z-qA*K*z)*(qA**2-1)+(MC+qA*MF)*(qA-1)
        P = 2*(MC-c*m)-eps*A*(MC-MF+K*(MC-c*m))
        residue = (2-eps*A*K)*(mR+m*c)-(2*m*z-P)
        check(all(word.count('A') >= 2 for word in residue.terms), 'A^2 divisibility')
        check(all((16*v).denominator == 1 for v in residue.terms.values()), 'denominator 16 suffices')
        low = {k: v for k, v in residue.terms.items() if k.count('A') < 2}
        check(not low, 'zero low remainder')
        transcript = [(list(k), str(v)) for k, v in sorted(residue.terms.items())]
        outputs.append({'epsilon': eps, 'rational_remainder_terms': len(transcript),
                        'full_remainder_sha256': digest(json.dumps(transcript).encode())})
    return {'computed_q_source_rows': sorted(visited), 'expanded_source_terms': len(actual_R.terms),
            'formal_cases': outputs, 'source_constant_z_present': True}


def digit_checks():
    direct = linear = quadratic = counter = 0
    for p in (3, 5, 7, 11, 17):
        for r in range(1, 321):
            check(carries(r, p) == valuation(math.comb(2*r, r), p), 'direct carries/binomial')
            direct += 1
        for depth in range(1, 7):
            for h in range(1, 73):
                if h % p == 0:
                    continue
                r = p**depth*h-1
                check(carries(r, p) == depth+carries(h, p), 'linear quotient carries')
                linear += 1
                qdepth = 2*depth+(1 if p == 3 else 0)
                r2 = p**qdepth*h-2
                check(carries(r2, p) == 2*depth+carries(h, p), 'quadratic quotient carries')
                quadratic += 1
        for a in range(1, 6):
            for L in range(1, 8):
                h = p**L+1
                r = p**a*h-1
                check(r % 2 == 1 and valuation(r+1, p) == a, 'counterfamily parity and depth')
                check(carries(h, p) == 0 and carries(r, p) == a, 'unbounded counterfamily')
                counter += 1
    return {'direct_binomial': direct, 'linear': linear, 'quadratic': quadratic, 'counterfamily': counter,
            'method': 'base-p digit addition; no author factorial implementation'}


def numerical_obstruction():
    records = []
    for d in (25, 125):
        B = 1 << d
        m = B-1
        for n in (5, 9):
            Q = B**n
            for eps in (-1, 1):
                A = Q+1 if eps == -1 else 2*Q-1
                q = A*(A+eps)//2
                J = (q-1)//m
                check(m*J+1 == q and math.gcd(2*m, A) == 1, 'source family denominator')
                for K in (32*B+32, 64*B+64):
                    check(A > 2*m*(3*K+8) and K+2 > 4*m, 'scalar size hypotheses')
                    for MC, MF in ((2, B+3), (B-2, 2*B-5)):
                        A0 = q*q*(q*q-1)+(MC+q*MF)*J
                        G = (1+q*K)*(q*q-1)
                        for c in (1, 3):
                            P = 2*(MC-c*m)-eps*A*(MC-MF+K*(MC-c*m))
                            # Solve the reduced congruence first, independently
                            # of the author's inverse of the source coefficient.
                            z = P*pow(2*m, -1, A*A) % (A*A)
                            check(z > 0 and (A0-G*z+c) % (A*A) == 0, 'source root recovered')
                            j = (2*m*z-P)//(A*A)
                            check(P % 2 == 1 and j % 2 == 1 and j >= 1, 'positive odd quotient')
                            check(2*abs(P) < A*A and 4*m*z > A*A, 'strict polynomial bound')
                            check((K+2)*z > q, 'every positive root violates slack')
                            check(z-A*A < 0, 'all other positive roots increase z')
                            records.append([d, n, eps, K//B, MC == 2, c, j,
                                            digest(str(z).encode())])
    return {'cases': len(records), 'records': records,
            'scope': 'synthetic scalar hypotheses only; no actual compiler output'}


def build():
    for suffix, expected in AUTHOR_PINS.items():
        check(digest(Path(str(AUTHOR)+suffix).read_bytes()) == expected, 'author pin '+suffix)
    author = json.loads(Path(str(AUTHOR)+'.json').read_text())
    deps = {}
    source = None
    for name, metadata in author['dependencies'].items():
        raw = Path(name).read_bytes()
        check(digest(raw) == metadata['sha256'] and len(raw) == metadata['bytes'], 'dependency '+name)
        deps[name] = metadata
        if name.endswith('/complete83_shared_projection_scout.json'):
            source = raw
    check(source is not None, 'actual source located')
    return {'reviewer_sha256': digest(Path(__file__).read_bytes()), 'author_pins': AUTHOR_PINS,
            'inert_dependencies': deps, 'source_algebra': source_and_congruence(source),
            'digit_carry_checks': digit_checks(), 'obstruction': numerical_obstruction(),
            'scope': {'author_or_predecessor_programs_executed': False,
                      'full_compiler_zero_claimed': False, 'source_changed': False}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    raw = (json.dumps(build(), sort_keys=True, indent=2)+'\n').encode()
    if args.output:
        with args.output.open('xb') as handle:
            handle.write(raw)
    else:
        check(raw == args.expect.read_bytes(), 'review receipt mismatch')
    print('PASS: independent carry identities, computed-source congruence, and positive-slack obstruction')


if __name__ == '__main__':
    main()
