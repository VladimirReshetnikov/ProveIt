#!/usr/bin/env python3
"""Independent exact small-norm identity and literal DAG audit.

Uses only the standard library.  The norm oracle substitutes x+sqrt(d)
and x-sqrt(d) successively in a sparse Laurent-polynomial ring.  It does
not reuse the author's cleared-norm formula or DAG arithmetic library.
"""
from collections import Counter
from hashlib import sha256
from math import comb
from pathlib import Path
import ast
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
NAMES = ('x', 'A', 'B', 'D', 'Cn', 'delta')
ZERO = (0,) * len(NAMES)


def need(condition, message):
    if not condition:
        raise ValueError(message)


class Poly:
    def __init__(self, terms):
        if isinstance(terms, int):
            terms = {ZERO: terms}
        self.terms = {m: c for m, c in terms.items() if c}

    @staticmethod
    def lift(value):
        return value if isinstance(value, Poly) else Poly(value)

    def __add__(self, other):
        out = self.terms.copy()
        for m, c in self.lift(other).terms.items():
            out[m] = out.get(m, 0) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        out = {}
        for ma, ca in self.terms.items():
            for mb, cb in self.lift(other).terms.items():
                m = tuple(a + b for a, b in zip(ma, mb))
                out[m] = out.get(m, 0) + ca * cb
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        need(type(n) is int and n >= 0, 'nonnegative polynomial exponent')
        out, base = Poly(1), self
        while n:
            if n & 1:
                out = out * base
            n >>= 1
            if n:
                base = base * base
        return out


def variable(i, exponent=1):
    m = list(ZERO)
    m[i] = exponent
    return Poly({tuple(m): 1})


def universal_norm(x, radicands):
    """The exact product of all sign conjugates, by even/odd substitution."""
    f = x
    for d in radicands:
        even, odd = Poly(0), Poly(0)
        for monomial, coefficient in f.terms.items():
            k = monomial[0]
            base = Poly({(0,) + monomial[1:]: coefficient})
            for j in range(k + 1):
                term = comb(k, j) * base * x ** (k - j) * d ** (j // 2)
                if j & 1:
                    odd = odd + term
                else:
                    even = even + term
        f = even * even - d * odd * odd
    return f


def norm_identities():
    # Extract only the three reviewed literal formulas, without importing
    # build.py or any of its arithmetic/construction dependencies.
    tree = ast.parse((ROOT / 'build.py').read_text())
    names = {'cleared_norm2', 'cleared_norm3', 'cleared_norm4'}
    nodes = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in names]
    need(len(nodes) == 3, 'three literal cleared-norm formulas present')
    scope = {}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), 'reviewed-norm-formulas', 'exec'), scope)
    x, A, B, D, Cn, delta = [variable(i) for i in range(len(NAMES))]
    rational = Cn * variable(5, -1)
    results = []
    for rank, radicands, args in [
        (2, [A, rational], [x, A, Cn, delta]),
        (3, [A, B, rational], [x, A, B, Cn, delta]),
        (4, [A, B, D, rational], [x, A, B, D, Cn, delta]),
    ]:
        expected = delta ** (2 ** (rank - 1)) * universal_norm(x, radicands)
        actual = scope['cleared_norm' + str(rank)](*args)
        need(expected.terms == actual.terms, 'exact cleared norm identity of rank ' + str(rank))
        need(all(min(m) >= 0 for m in expected.terms), 'denominator clears as a polynomial')
        leading = {ZERO: 0}
        for monomial, coefficient in expected.terms.items():
            # Every nonleading monomial contains a weighted radicand
            # numerator; this licenses the unconditional modulo-4 proof.
            if not any(monomial[i] for i in (1, 2, 3, 4)):
                leading[monomial] = coefficient
        leading = {m: c for m, c in leading.items() if c}
        want = [0] * len(NAMES)
        want[0] = 2 ** rank
        want[5] = 2 ** (rank - 1)
        need(leading == {tuple(want): 1}, 'unique radicand-free monomial')
        serial = [[list(m), c] for m, c in sorted(expected.terms.items())]
        results.append({'rank': rank, 'exact_terms': len(serial),
                        'polynomial_sha256': sha256(json.dumps(serial).encode()).hexdigest(),
                        'exact_identity': True, 'denominators_clear': True,
                        'mod4_leading_monomial_verified': True})
    return results


def circuit_census():
    out = []
    for nv, degree, operations in [(13, 1072, 195), (14, 414, 148),
                                    (15, 218, 130), (16, 124, 118)]:
        path = ROOT / 'equations' / ('integer%d_crt_valuation_degree%d.json' % (nv, degree))
        g = json.loads(path.read_text())
        seen = set()

        def visit(i):
            need(type(i) is int and 0 <= i < len(g['nodes']), 'valid node index')
            if i in seen:
                return
            seen.add(i)
            node = g['nodes'][i]
            if node[0] in ('add', 'sub', 'mul'):
                need(len(node) == 3 and all(0 <= j < i for j in node[1:]), 'topological order')
                for j in node[1:]:
                    visit(j)
            else:
                need(node[0] in ('integer', 'variable', 'coefficient'), 'recognized leaf')

        visit(g['output'])
        need(len(seen) == len(g['nodes']), 'no dead literal nodes')
        counts = Counter(node[0] for node in g['nodes'] if node[0] in ('add', 'sub', 'mul'))
        need(sum(counts.values()) == operations == g['operations'], 'operation census')
        need(len(g['variables']) == nv and len(set(g['variables'])) == nv, 'variable inventory')
        need({node[1] for node in g['nodes'] if node[0] == 'variable'} == set(g['variables']), 'all variables live')
        need(g['exact_degree'] == degree, 'degree metadata matches reviewed proof')
        out.append({'variables': nv, 'reviewed_exact_degree': degree,
                    'operations': operations, 'operation_counts': dict(counts),
                    'all_nodes_live': True, 'all_variables_live': True,
                    'sha256': sha256(path.read_bytes()).hexdigest()})
    return out


def main():
    report = {'status': 'PASS', 'optimization': sys.flags.optimize,
              'small_norm_exact_identities': norm_identities(),
              'literal_circuits': circuit_census(),
              'reviewed_build_sha256': sha256((ROOT / 'build.py').read_bytes()).hexdigest(),
              'scope': 'Exact rank-2, rank-3, rank-4 cleared-norm identities and modulo-4 structural premise; independent circuit topology, liveness and census. Semantic reductions and exact multivariate degrees are reviewed in REVIEW.md. No inherited calibration or consistency claim is computationally proved.'}
    suffix = '_OPTIMIZED' if sys.flags.optimize else ''
    (Path(__file__).parent / ('CHECKS' + suffix + '.json')).write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
