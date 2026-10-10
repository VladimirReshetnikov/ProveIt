"""Check the printed rows and independently expand the ordered tensor.

This imports no delivered verifier. SymPy supplies exact Q[t] factorization;
the tensor is expanded with two ordered slots rather than the delivery's
compressed symmetric-slot coordinates. Endpoint descent is checked separately
by the delivered replay and the written analytic proof.
"""
from collections import defaultdict
from pathlib import Path
import json, re
import sympy as sp

B = Path(__file__).resolve().parents[1]
V = B / 'verification'
source = B.parent / 'reports/uniform-transition-continuation/continuations/tetralogarithm-euler-polynomial-zeros/code'
rows = json.loads((source / 'tetralogarithm_certificate.json').read_text())['rows']
printed = {}
text = (B / 'chapters/03-rational-tetralogarithm-proof.tex').read_text()
for match in re.finditer(r'^([0-9]+(?:\s*&\s*(?:[-+]?[0-9]+|[-+])){13})\s*\\\\', text, re.M):
    cells = [x.strip() for x in match[1].split('&')]
    for start in (0, 7):
        index, coefficient, sign, *exponents = cells[start:start+7]
        printed[int(index)] = [int(coefficient), 1 if sign == '+' else -1, *map(int, exponents)]
assert len(printed) == len(rows) == 42
assert all(printed[i+1] == [int(x) for x in row] for i, row in enumerate(rows))

t = sp.Symbol('t')
def factors(expression):
    result = defaultdict(int)
    top, bottom = sp.fraction(sp.cancel(expression))
    for polynomial, polarity in ((top, 1), (bottom, -1)):
        content, parts = sp.factor_list(polynomial, t)
        numerator, denominator = sp.fraction(abs(content))
        for prime, count in sp.factorint(numerator).items():
            result[('prime', int(prime))] += polarity * count
        for prime, count in sp.factorint(denominator).items():
            result[('prime', int(prime))] -= polarity * count
        for factor, count in parts:
            result[('polynomial', tuple(sp.Poly(factor, t).all_coeffs()))] += polarity * count
    return {key: int(value) for key, value in result.items() if value}

vectors = []
for coefficient, sign, d, a, b, c in rows:
    f = sign * sp.Rational(2)**d * t**a * (1-t)**b * (1+t)**c
    vectors.append((int(coefficient), factors(f), factors(1-f)))

def tensor(corrupt=False):
    residual = defaultdict(int)
    for index, (coefficient, f, g) in enumerate(vectors):
        coefficient += int(corrupt and index == 0)
        for i, vi in f.items():
            for j, vj in f.items():
                for k, vk in f.items():
                    for l, vl in g.items():
                        if k == l:
                            continue
                        u, v = sorted((k, l), key=repr)
                        residual[i, j, u, v] += coefficient * vi * vj * vk * vl * (1 if k == u else -1)
    return {key: value for key, value in residual.items() if value}

assert not tensor()
control = tensor(True)
assert control
record = dict(status='PASS', printed_rows_checked=42,
              ordered_tensor_residual_coordinates=0,
              corrupted_first_coefficient_nonzero_coordinates=len(control),
              retains_rational_prime_two=any(('prime', 2) in f for _, f, _ in vectors),
              scope='Printed canonical rows and independent ordered finite tensor only; analytic descent and branch constants have separate proofs.')
(V / 'tetralogarithm-table-audit.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record, indent=2))
