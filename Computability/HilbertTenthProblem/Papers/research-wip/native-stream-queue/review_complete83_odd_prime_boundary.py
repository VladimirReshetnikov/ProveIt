#!/usr/bin/env python3
"""Independent fresh reviewer; no author/predecessor code is run or imported."""
import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path

AUTHOR = {'py': '200f3bdfc29a1f156b70852d01d12b70404b4ba60c96eb51bc55900be58ebc22',
          'json': '32ac3d25897c645a70a6d53fc7afeebe8a554f8aa4b6e1cbab4d824161c46100',
          'md': '59fb701504a8cab48a4c29b8167ffe459c049feed00dc6a821003747e8a856da'}
WIP = Path('Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')


def check(ok, why):
    if not ok:
        raise ValueError(why)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def vp(n, p):
    check(n != 0, 'undefined valuation')
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


class Poly:
    def __init__(self, value):
        if isinstance(value, Poly):
            self.terms = dict(value.terms)
        elif isinstance(value, dict):
            self.terms = {m: c for m, c in value.items() if c}
        elif isinstance(value, str):
            self.terms = {(value,): 1}
        else:
            self.terms = {(): value} if value else {}

    def __add__(self, other):
        result = Counter(self.terms)
        for m, c in Poly(other).terms.items():
            result[m] += c
        return Poly(dict(result))

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) - self

    def __mul__(self, other):
        result = Counter()
        for m, c in self.terms.items():
            for n, d in Poly(other).terms.items():
                result[tuple(sorted(m + n))] += c * d
        return Poly(dict(result))

    __rmul__ = __mul__

    def __pow__(self, exponent):
        result = Poly(1)
        for _ in range(exponent):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == Poly(other).terms


def source_audit(source_raw, saved):
    rows = json.loads(source_raw)['packet']['source']
    check(len(rows) == 83, 'source size')
    definitions = {row[0]: row for row in rows}
    check(len(definitions) == len(rows), 'duplicate source register')
    targets = ['q', 'wn2', 'sn2', 'marked_rhs', 'W', 'odd_index', 'r_lhs', 'norm_transport']
    closure = set()
    pending = list(targets)
    while pending:
        name = pending.pop()
        if name in closure or name not in definitions:
            continue
        closure.add(name)
        pending.extend(v for v in definitions[name][2:] if isinstance(v, str))
    env = {}
    bound_rows = []
    def get(value):
        if isinstance(value, int):
            return Poly(value)
        if value not in env:
            check(value not in definitions, 'nontopological selected source')
            env[value] = Poly(value)
        return env[value]
    for name, op, left, right in rows:
        if name not in closure:
            continue
        a, b = get(left), get(right)
        env[name] = a + b if op == '+' else a - b if op == '-' else a * b
        check(op in ['+', '-', '*'], 'unknown operation')
        bound_rows.append(name)
    Bm1, J, w, s, F, Z, slack, two_d, x, b, MC, MF, K, tq = [
        Poly(v) for v in ['Bm1', 'Jrep', 'w', 's', 'F', 'Z', 'alpha',
                         'twice_cell_bits', 'x', 'inner_bits', 'MC', 'MF',
                         'Kconstant', 'transport_quotient']]
    q = Bm1 * J + 1
    C = q - F - Z - slack - two_d * x
    R = (q*q - Z - q*F) * (q*q - 1) + (MC + q*MF)*J
    expected = [q, w*q, s*q**3, C, C-Z, two_d*x+b, R,
                (K+w)*C+q-F-(q-1)*tq]
    for name, polynomial in zip(targets, expected):
        check(env[name] == polynomial, 'actual source binding: ' + name)
    Dmask = Bm1 - MC
    check(R - (Z-Dmask*J-1) == q*(q**3-q-Z*q-q*q*F+F+MF*J+1),
          'whole source residue identity')
    check(sorted(bound_rows) == saved['source_binding']['bound_ancestor_names'], 'saved ancestry mismatch')
    check(len(bound_rows) == 26, 'unexpected selected cone size')
    return {'selected_source_rows': len(bound_rows), 'bound_names': bound_rows,
            'target_term_counts': {name: len(env[name].terms) for name in targets},
            'source_residue_identity': True}


def independent_prime_cases():
    counts = Counter()
    deficiency_cases = 0
    for r in range(2, 243):
        coefficients = [math.comb(2*r, r+j) for j in range(3)]
        for p in [3, 5, 7, 11, 19]:
            central = vp(coefficients[0], p)
            for exponent in [1, 2, 3]:
                for unit in [1, p-1, p+1, 2*p-1]:
                    X = p**exponent * unit
                    value = coefficients[0] + X*(coefficients[1] + X*coefficients[2])
                    numerator = (r+1)*(r+2) + r*(r+2)*X + r*(r-1)*X*X
                    actual = vp(value, p)
                    check((r+1)*(r+2)*value == coefficients[0]*numerator, 'quadratic integer identity')
                    if (r+1) % p == 0:
                        den = vp(r+1, p)
                        shift = exponent - den
                        kind = 'linear'
                        if shift == 0:
                            eta = (r+1)//p**den
                            normalized = eta*(r+2) + r*(r+2)*unit + r*(r-1)*p**exponent*unit**2
                            check(actual == central+vp(normalized, p), 'linear normalized value')
                            check((actual > central) == ((eta-unit) % p == 0), 'linear residue')
                        else:
                            check(actual == central+min(0, shift), 'linear unique minimum')
                    elif (r+2) % p == 0:
                        den = vp(r+2, p)
                        e = vp(r-1, p)
                        shift = 2*exponent+e-den
                        kind = 'quadratic'
                        if shift == 0:
                            eta, zeta = (r+2)//p**den, (r-1)//p**e
                            normalized = (r+1)*eta+r*eta*p**exponent*unit+r*zeta*unit**2
                            check(actual == central+vp(normalized, p), 'quadratic normalized value')
                            check(den == 2*exponent+vp(6, p), 'quadratic tie exponent')
                            check((actual > central) == ((r+2-6*X*X) % p**(den+1) == 0), 'quadratic residue')
                        else:
                            check(actual == central+min(0, shift), 'quadratic unique minimum')
                    else:
                        kind, shift = 'regular', None
                        check(actual == central, 'regular value')
                    counts[kind + ('_tie' if shift == 0 else '')] += 1
                    for radix_exponent in range(1, exponent+1):
                        if central < 3*radix_exponent <= actual:
                            R = 2*r+1
                            check((R+1)*(R+3) % p**radix_exponent == 0, 'full deficient prime power')
                            check(not ((R+1) % p == 0 and (R+3) % p == 0), 'nonexclusive resonance')
                            deficiency_cases += 1
    return {'r_range': [2, 242], 'primes': [3, 5, 7, 11, 19], 'cases': sum(counts.values()),
            'branches': dict(counts), 'full_power_deficiency_cases': deficiency_cases}


def independent_lifts(saved):
    checked = 0
    for example in saved['lifts']['examples']:
        p, r, b = example['p'], example['r'], example['b']
        if example['kind'] == 'linear':
            eta = (r+1)//p**b
            coefficients = [eta*(r+2), r*(r+2), r*(r-1)*p**b]
        else:
            den, e = vp(r+2, p), vp(r-1, p)
            eta, zeta = (r+2)//p**den, (r-1)//p**e
            coefficients = [(r+1)*eta, r*eta*p**b, r*zeta]
        def evaluate(z):
            return coefficients[0]+z*(coefficients[1]+z*coefficients[2])
        roots = [z for z in range(1, p) if evaluate(z) % p == 0]
        check(roots == [v['initial_unit'] for v in example['lifts']], 'saved initial roots')
        for root, claimed in zip(roots, example['lifts']):
            z, modulus = root, p
            for _ in range(1, 7):
                derivative = coefficients[1]+2*z*coefficients[2]
                correction = -(evaluate(z)//modulus)*pow(derivative, -1, p) % p
                z += correction * modulus
                modulus *= p
                check(evaluate(z) % modulus == 0, 'Newton lift')
            check(z == claimed['unit_mod_p7'], 'saved canonical lift')
            X = p**b*z
            actual = vp(sum(math.comb(2*r, r+j)*X**j for j in range(3)), p)
            check(actual == claimed['M2_valuation'], 'saved lift valuation')
            checked += 1
    return {'independent_Newton_lifts': checked, 'precision': 7}


def remaining_checks():
    truncations = odd = transport = 0
    for q in range(4, 44, 2):
        for r in range(3, 28):
            cc = [math.comb(2*r, r+j) for j in range(r+1)]
            for w in [1, 3]:
                modulus, X = 2*q**3, q*w
                full = 0
                for coefficient in reversed(cc):
                    full = (full*X+coefficient) % modulus
                four = sum(cc[j]*pow(X, j, modulus) for j in range(4)) % modulus
                check(full == four, 'independent full truncation')
                truncations += 1
                for p in [3, 5, 7, 11, 13, 17, 19]:
                    if q % p == 0:
                        oddmod = p**(3*vp(q, p))
                        check(full % oddmod == sum(cc[j]*pow(X, j, oddmod) for j in range(3)) % oddmod,
                              'independent odd truncation')
                        odd += 1
        modulus = q-1
        for C in range(q-1):
            image = Counter(((7+w)*C) % modulus for w in range(modulus))
            for F in range(1, q-1):
                gcd = math.gcd(C, modulus)
                check(image[F] == (gcd if F % gcd == 0 else 0), 'transport residue count')
                transport += 1
    return {'full_truncations': truncations, 'odd_truncations': odd, 'transport_cases': transport}


def build(root, directory):
    for ext, pin in AUTHOR.items():
        raw = (directory / ('complete83_odd_prime_boundary.'+ext)).read_bytes()
        check(sha(raw) == pin, 'author pin '+ext)
    saved = json.loads((directory/'complete83_odd_prime_boundary.json').read_text())
    check(saved['helper_sha256'] == AUTHOR['py'], 'receipt author binding')
    dependencies = {}
    source_raw = None
    for name, record in saved['dependencies'].items():
        path = root/WIP/name
        if not path.exists():
            path = directory/name
        raw = path.read_bytes()
        check(sha(raw) == record['sha256'] and len(raw) == record['bytes'], 'dependency pin '+name)
        dependencies[name] = record
        if name.endswith('scout.json'):
            source_raw = raw
    return {'schema': 'independent-review-complete83-odd-prime-v1',
            'reviewer_sha256': sha(Path(__file__).read_bytes()), 'author_pins': AUTHOR,
            'dependencies': dependencies, 'source_audit': source_audit(source_raw, saved),
            'prime_checks': independent_prime_cases(), 'lift_checks': independent_lifts(saved),
            'other_checks': remaining_checks(),
            'scope': {'author_execution': False, 'predecessor_execution': False,
                      'full_native_zero_test': False, 'universal83_claim': False}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--packet-dir', type=Path, default=Path('/tmp'))
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--output', type=Path)
    modes.add_argument('--expect', type=Path)
    args = parser.parse_args()
    receipt = build(args.root, args.packet_dir)
    if args.output:
        with args.output.open('x') as stream:
            stream.write(json.dumps(receipt, sort_keys=True, indent=2)+'\n')
    else:
        old = json.loads(args.expect.read_text())
        check(json.dumps(old, sort_keys=True) == json.dumps(receipt, sort_keys=True), 'review receipt mismatch')
    print('PASS: independent odd-prime proof/source review corroboration')


if __name__ == '__main__':
    main()
