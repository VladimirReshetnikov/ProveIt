#!/usr/bin/env python3
"""Fresh fixed-horizon arithmetic only; no predecessor code or arrays loaded."""
from fractions import Fraction
from itertools import product
from math import gcd, lcm
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
BASE = ROOT / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS = {
    'residue_affine_factored_counter_step.md': '60250f0f6d12f7583b5de747c82d0d91205eab98ca0f4095992d458aaf8a951f',
    'residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882',
    'residue_affine_ancestor_pumping.md': 'd9d2da9a30f9d52a61ceba283e2564dcf162fbac78d685d25e29ef5e67c060e2',
    'fractran_divisibility_residual_projection.md': '42e9c3689e748b04c464d52ba4e55e300333d7b2f1673ab16eda3b4a979c094d',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def interpolate(values):
    """Lagrange interpolation, coefficients in ascending order."""
    out = [Fraction(0)] * len(values)
    for i, value in enumerate(values, 1):
        term = [Fraction(value)]
        denominator = 1
        for j in range(1, len(values) + 1):
            if j == i:
                continue
            nxt = [Fraction(0)] * (len(term) + 1)
            for k, c in enumerate(term):
                nxt[k] -= j * c
                nxt[k + 1] += c
            term = nxt
            denominator *= i - j
        for k, c in enumerate(term):
            out[k] += c / denominator
    return out


def peval(coefficients, value):
    return sum(c * value ** j for j, c in enumerate(coefficients))


class FreshSource:
    def __init__(self, ports):
        self.ports = ports
        self.rows = []

    def gate(self, op, left, right):
        name = 'v' + str(len(self.rows))
        self.rows.append([name, op, left, right])
        return name

    def horner(self, coefficients, value):
        out = coefficients[-1]
        for c in reversed(coefficients[:-1]):
            out = self.gate('+', self.gate('*', out, value), c)
        return out

    def count(self, end=None):
        rows = self.rows if end is None else self.rows[:end]
        m = sum(row[1] == '*' for row in rows)
        return {'M': m, 'A': len(rows) - m, 'total': len(rows)}

    def evaluate(self, assignment):
        # This evaluates only this fresh builder's in-memory rows.
        env = dict(assignment)
        def get(value):
            return value if isinstance(value, int) else env[value]
        for name, op, left, right in self.rows:
            a, b = get(left), get(right)
            env[name] = a * b if op == '*' else a + b if op == '+' else a - b
        return env

    def symbolic(self):
        n = len(self.ports)
        zero = (0,) * n
        env = {p: {tuple(int(j == i) for j in range(n)): 1}
               for i, p in enumerate(self.ports)}
        def get(value):
            return ({zero: value} if value else {}) if isinstance(value, int) else env[value]
        for name, op, left, right in self.rows:
            a, b = get(left), get(right)
            out = {}
            if op == '*':
                for e, c in a.items():
                    for f, d in b.items():
                        key = tuple(x + y for x, y in zip(e, f))
                        out[key] = out.get(key, 0) + c * d
            else:
                out = dict(a)
                for e, c in b.items():
                    out[e] = out.get(e, 0) + (c if op == '+' else -c)
            env[name] = {e: c for e, c in out.items() if c}
        return env


def build(b, aa, dd, duration, common):
    need(duration >= 1 and len(aa) == len(dd) == b, 'bad dimensions')
    need(all(a > 0 and gcd(a, b) == 1 for a in aa), 'unit numerators required')
    need(aa[0] + dd[0] > 0 and all(d > 0 for d in dd[1:]), 'positive map')
    if common:
        need(len(set(aa)) == 1 and aa[0] >= 2, 'common source domain')
    cc = [b * d - a * r for r, (a, d) in enumerate(zip(aa, dd))]
    pa, pc = interpolate(aa), interpolate(cc)
    scale = lcm(*(c.denominator for c in (pc if common else pa + pc)))
    ai, ci = [int(scale * c) for c in pa], [int(scale * c) for c in pc]
    for r in range(b):
        need(peval(ci, r + 1) == scale * cc[r], 'C table')
        if not common:
            need(peval(ai, r + 1) == scale * aa[r], 'P table')
    ports = ['x', 'y'] + [p for j in range(duration) for p in ('s' + str(j), 'vhat' + str(j))]
    src = FreshSource(ports)
    equations = []
    values = []
    for j in range(duration):
        s, v = 's' + str(j), 'vhat' + str(j)
        equations.append([src.gate('+', s, v), b + 1])
        c = src.horner(ci, s)
        a = None if common else src.horner(ai, s)
        values.append((a, c))
    if common:
        a = aa[0]
        accum = src.gate('*', scale * a ** duration, 'x')
        for j, (_, c) in enumerate(values):
            weight = a ** (duration - 1 - j) * b ** j
            term = c if weight == 1 else src.gate('*', weight, c)
            accum = src.gate('+', accum, term)
        rhs = src.gate('*', scale * b ** duration, 'y')
    else:
        accum = 'x'
        for j, (a, c) in enumerate(values):
            first = src.gate('*', a, accum)
            term = c if j == 0 else src.gate('*', (b * scale) ** j, c)
            accum = src.gate('+', first, term)
        rhs = src.gate('*', (b * scale) ** duration, 'y')
    equations.append([accum, rhs])
    prefix = len(src.rows)
    residuals = [src.gate('-', a, c) for a, c in equations]
    squares = [src.gate('*', r, r) for r in residuals]
    out = squares[0]
    for sq in squares[1:]:
        out = src.gate('+', out, sq)
    if common and duration == 1:
        expected_graph = (b + 1, b + 1)
        expected_sos = (b + 3, b + 4)
    elif common:
        expected_graph = (b * duration + 2, (b + 1) * duration)
        expected_sos = ((b + 1) * duration + 3, (b + 3) * duration + 1)
    else:
        expected_graph = (2 * b * duration, 2 * b * duration)
        expected_sos = ((2 * b + 1) * duration + 1, (2 * b + 2) * duration + 1)
    for got, expected in [(src.count(prefix), expected_graph), (src.count(), expected_sos)]:
        need((got['M'], got['A']) == expected, 'literal ledger mismatch')
    polys = src.symbolic()
    combined = {}
    for r in residuals:
        for e, c in polys[r].items():
            for f, d in polys[r].items():
                key = tuple(x + y for x, y in zip(e, f))
                combined[key] = combined.get(key, 0) + c * d
    combined = {k: v for k, v in combined.items() if v}
    need(combined == polys[out], 'full symbolic SOS mismatch')
    degree = max(map(sum, polys[out]))
    bound = 2 * max(b - 1, 1) if common else 2 * (duration * (b - 1) + 1)
    need(degree <= bound, 'degree bound')
    cases = zeros = 0
    for x in range(1, 13):
        true_value = x
        true_word = []
        for _ in range(duration):
            q, r = divmod(true_value, b)
            true_word.append(r)
            true_value = aa[r] * q + dd[r]
        for word in product(range(b), repeat=duration):
            formal = Fraction(x)
            for r in word:
                formal = (aa[r] * formal + cc[r]) / b
            integral = formal.denominator == 1
            need(integral == (list(word) == true_word), 'endpoint reconstruction failed')
            y = int(formal) if integral else true_value
            assignment = {'x': x, 'y': y}
            for j, r in enumerate(word):
                assignment['s' + str(j)] = r + 1
                assignment['vhat' + str(j)] = b - r
            value = src.evaluate(assignment)[out]
            need((value == 0) == integral, 'fresh source zero projection')
            cases += 1
            zeros += value == 0
    # Positive selector corruption: move either member beyond its legal sum.
    for x in range(1, 5):
        y = x
        assignment = {'x': x}
        for j in range(duration):
            q, r = divmod(y, b)
            assignment['s' + str(j)] = r + 1
            assignment['vhat' + str(j)] = b - r
            y = aa[r] * q + dd[r]
        assignment['y'] = y
        for j in range(duration):
            for p in ('s' + str(j), 'vhat' + str(j)):
                altered = dict(assignment)
                altered[p] += b
                need(src.evaluate(altered)[out] > 0, 'positive selector corruption accepted')
    encoded_poly = [[list(e), c] for e, c in sorted(polys[out].items())]
    return {'b': b, 'a_table': aa, 'd_table': dd, 'T': duration, 'common': common,
            'L': scale, 'ports': ports, 'witness_count': 2 * duration,
            'equations': equations, 'graph_rows': prefix, 'rows': src.rows, 'output': out,
            'graph_ledger': src.count(prefix), 'SOS_ledger': src.count(),
            'degree': degree, 'degree_bound': bound, 'output_terms': len(encoded_poly),
            'expanded_output_sha256': digest(json.dumps(encoded_poly, separators=(',', ':')).encode()),
            'all_word_cases': cases, 'positive_zero_cases': zeros,
            'positive_selector_rejections': 8 * duration,
            'max_fixed_integer_bits': max(abs(x).bit_length() for row in src.rows for x in row[2:] if isinstance(x, int))}


def make_receipt():
    deps = []
    for name, pin in PINS.items():
        data = (BASE / name).read_bytes()
        need(digest(data) == pin, 'dependency changed: ' + name)
        deps.append({'path': str((BASE / name).relative_to(ROOT)), 'sha256': pin,
                     'bytes': len(data), 'lines': len(data.splitlines())})
    specs = [
        (2, [1, 3], [0, 2], 1, False),
        (2, [1, 3], [0, 2], 2, False),
        (2, [1, 3], [0, 2], 3, False),
        (3, [1, 2, 4], [0, 1, 2], 2, False),
        (4, [1, 3, 5, 7], [0, 1, 2, 3], 2, False),
        (2, [3, 3], [0, 2], 1, True),
        (2, [3, 3], [0, 2], 2, True),
        (2, [3, 3], [0, 2], 3, True),
        (3, [2, 2, 2], [0, 2, 1], 2, True),
        (4, [3, 3, 3, 3], [0, 1, 2, 1], 2, True),
    ]
    sources = [build(*s) for s in specs]
    # Handwritten nonunit cancellation example, not a source predecessor.
    formal = (4 * Fraction(1, 2) + 2) / 2
    need(formal == 2 and 4 * 2 == 4 * 1 + 4, 'nonunit endpoint example')
    need(all((2 ** (j + 1) - 1) != 2 for j in range(20)), 'diagnostic orbit formula')
    # Separate varying-denominator integral-word lemma check.
    word_cases = 0
    for T in range(1, 4):
        for word in product([(5, 2, 0), (7, 3, 1), (5, 3, -1)], repeat=T):
            need(all(gcd(word[k][0], word[j][1]) == 1 for j in range(T) for k in range(j, T)), 'word premises')
            for x in range(1, 13):
                value = Fraction(x)
                all_integral = True
                for a, b, c in word:
                    value = (a * value + c) / b
                    all_integral &= value.denominator == 1
                need((value.denominator == 1) == all_integral, 'varying denominator word')
                word_cases += 1
    return {'schema': 'fresh-residue-endpoint-evidence/v1', 'status': 'PASS',
            'helper_sha256': digest(Path(__file__).read_bytes()), 'dependencies': deps,
            'sources': sources, 'totals': {'sources': len(sources),
                'rows': sum(len(s['rows']) for s in sources),
                'all_word_cases': sum(s['all_word_cases'] for s in sources),
                'positive_zero_cases': sum(s['positive_zero_cases'] for s in sources),
                'selector_rejections': sum(s['positive_selector_rejections'] for s in sources),
                'varying_denominator_word_cases': word_cases},
            'nonunit_counterexample': {'x': 1, 'y': 2, 'word': [0, 1],
                'formal_intermediate': '1/2', 'actual_orbit_formula': '2^(j+1)-1'},
            'scope': 'Synthetic fixed-horizon graphs only; no predecessor program/array evaluation; no universal or fixed-arity history claim.'}


def main():
    out = Path('/tmp/residue_affine_endpoint_history_tesla_checks.json')
    data = (json.dumps(make_receipt(), indent=2, sort_keys=True) + '\n').encode()
    if sys.argv[1:] == ['--write']:
        out.write_bytes(data)
    elif sys.argv[1:]:
        raise SystemExit('only optional --write accepted')
    else:
        need(out.read_bytes() == data, 'receipt mismatch')
    print('PASS', digest(data))


if __name__ == '__main__':
    main()
