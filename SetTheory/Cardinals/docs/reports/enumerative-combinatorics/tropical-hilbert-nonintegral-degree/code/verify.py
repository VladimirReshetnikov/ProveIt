#!/usr/bin/env python3
"""Exact certificates for tropical Hilbert functions of two horizontal segments.

Python 3.10+; standard library only. No numerical tolerances or external solvers.
Run: python code/verify.py --max-k 40
Checks every selected monomial against every competing selected monomial at a
rational witness, and independently enumerates the endpoint upper-bound states.
These tests supplement, rather than replace, the all-degree proof in article.tex.
"""
from __future__ import annotations
import argparse
import csv
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def ceil_q(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def hilbert(k: int, d: Q) -> int:
    if k < 0 or d <= 0:
        raise ValueError('Require k >= 0 and d > 0.')
    return k + min(k, ceil_q(Q(k) / d)) + 1


@dataclass(frozen=True)
class Term:
    label: str
    i: int
    j: int
    c: Q
    x: Q
    y: Q

    def value(self, x: Q, y: Q) -> Q:
        return self.c + self.i * x + self.j * y

    def as_dict(self) -> dict:
        return {'label': self.label, 'exponent': [self.i, self.j],
                'coefficient': str(self.c), 'witness': [str(self.x), str(self.y)]}


def certificate(k: int, d: Q) -> tuple[list[Term], dict]:
    if k < 0 or d <= 0:
        raise ValueError('Require k >= 0 and d > 0.')
    if k == 0:
        return [Term('A0', 0, 0, Q(0), Q(1, 2), Q(0))], {'k': 0, 'd': str(d)}
    m = min(k, ceil_q(Q(k) / d)) - 1
    w = min(Q(1), d)
    sigma = w * k - d * m
    assert sigma > 0 and 0 <= m < k
    delta = min(Q(1, 8), sigma / (8 * (m + 1)))
    eps = delta / (4 * k)
    eta = delta / (4 * (m + 1))
    a = 1 - delta
    b = d + 1 + delta
    h = w * k - delta
    terms = [Term(f'A{i}', i, k-i, eps*i*i-a*i, a-2*eps*i, Q(0))
             for i in range(k+1)]
    terms += [Term(f'B{j}', j, 0, h-b*j+eta*j*j, b-2*eta*j, Q(1))
              for j in range(m+1)]
    params = {'k': k, 'd': str(d), 'm': m, 'w': str(w), 'sigma': str(sigma),
              'delta': str(delta), 'epsilon': str(eps), 'eta': str(eta),
              'a': str(a), 'b': str(b), 'h': str(h)}
    return terms, params


def verify_terms(terms: list[Term], k: int, d: Q) -> tuple[int, Q | None]:
    exponents = {(t.i, t.j) for t in terms}
    assert len(exponents) == len(terms), 'Duplicated exponent.'
    assert len(terms) == hilbert(k, d), 'Wrong certificate cardinality.'
    gaps = []
    for t in terms:
        assert t.i >= 0 and t.j >= 0 and t.i + t.j <= k
        assert ((t.y == 0 and 0 <= t.x <= 1) or
                (t.y == 1 and d+1 <= t.x <= d+2)), 'Witness outside V_d.'
        own = t.value(t.x, t.y)
        for other in terms:
            if other is t:
                continue
            gap = other.value(t.x, t.y) - own
            assert gap > 0, (k, d, t.label, other.label, gap)
            gaps.append(gap)
    return len(gaps), min(gaps) if gaps else None


def endpoint_upper(k: int, d: Q) -> int:
    """Enumerate the necessary endpoint-state relaxation from the upper proof.

    If distinct monomials are active at (1,0) and (d+1,1), their x-slopes
    r,P obey d*(P-r) < k-r. The count is <= k+P-r+2. If the endpoint
    monomial is shared, the count is <= k+1. A second independent upper
    bound is 2*k+1. No claim that every enumerated state is realizable.
    """
    if k == 0:
        return 1
    best = k + 1
    for r in range(k+1):
        for P in range(k+1):
            if d * (P-r) < k-r:
                best = max(best, k+P-r+2)
    return min(best, 2*k+1)


def endpoint_upper_box(k: int, d: Q) -> int:
    """Necessary endpoint relaxation for the box 0 <= i,j <= k."""
    if k == 0:
        return 1
    best = k + 1
    for r in range(k+1):
        for P in range(k+1):
            if d * (P-r) < k:
                best = max(best, k+P-r+2)
    return min(best, 2*k+2)


def pretty_example() -> list[Term]:
    k = 4
    terms = [Term(f'A{i}', i, k-i, Q(i*i, 100)-Q(9*i, 10),
                  Q(9,10)-Q(i,50), Q(0)) for i in range(k+1)]
    terms += [Term('B0',0,0,Q(39,10),Q(41,10),Q(1)),
              Term('B1',1,0,Q(-19,100),Q(102,25),Q(1))]
    return terms


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-k', type=int, default=40)
    args = parser.parse_args()
    if args.max_k < 1:
        parser.error('--max-k must be positive')
    ds = [Q(1,4), Q(1,2), Q(2,3), Q(1), Q(5,4), Q(3,2), Q(5,3),
          Q(2), Q(7,3), Q(3), Q(4), Q(5), Q(10), Q(101,7)]
    rows = []
    total_checks = 0
    box_checks = 0
    for d in ds:
        for k in range(args.max_k+1):
            terms, _ = certificate(k,d)
            checks, gap = verify_terms(terms,k,d)
            total_checks += checks
            upper = endpoint_upper(k,d)
            assert upper == len(terms)
            if d >= 1:
                assert endpoint_upper_box(k, d) == len(terms)
                box_checks += 1
            rows.append({'d':str(d), 'k':k, 'hilbert':len(terms),
                         'endpoint_upper_bound':upper, 'strict_inequalities':checks,
                         'minimum_exact_gap':str(gap) if gap is not None else ''})
    example = pretty_example()
    checks,gap = verify_terms(example,4,Q(3))
    total_checks += checks
    resultdir = ROOT / 'data'
    resultdir.mkdir(exist_ok=True)
    with (resultdir/'verification.csv').open('w',newline='') as out:
        writer=csv.DictWriter(out,fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    gap_matrix = []
    for term in example:
        row = [100 * (other.value(term.x, term.y) - term.value(term.x, term.y))
               for other in example]
        assert all(value.denominator == 1 for value in row)
        gap_matrix.append([int(value) for value in row])
    (resultdir/'example_gap_matrix.json').write_text(json.dumps({
        'rows_and_columns': [t.label for t in example], 'scale': 100,
        'gap_matrix': gap_matrix}, indent=2) + '\n')
    (resultdir/'example_k4_d3.json').write_text(json.dumps({
        'k':4,'d':'3','terms':[t.as_dict() for t in example],
        'minimum_exact_gap':str(gap)},indent=2)+'\n')
    terms,params=certificate(12,Q(3))
    (resultdir/'certificate_k12_d3.json').write_text(json.dumps({
        'parameters':params,'terms':[t.as_dict() for t in terms]},indent=2)+'\n')
    # The first difference has exact period p for rational d=p/q > 1.
    for d in ds:
        for k in range(2*args.max_k+1):
            if d >= 1:
                p,q=d.numerator,d.denominator
                assert hilbert(k+p,d)-hilbert(k,d) == p+q
            else:
                assert hilbert(k,d) == 2*k+1
    sequence=[hilbert(k,Q(3)) for k in range(121)]
    # Multiplication by (1-z)(1-z^3) leaves the numerator (1+z)^2.
    for k,v in enumerate(sequence):
        residual=v-(sequence[k-1] if k>=1 else 0)-(sequence[k-3] if k>=3 else 0)+(sequence[k-4] if k>=4 else 0)
        assert residual == ({0:1,1:2,2:1}.get(k,0))
    (resultdir/'hilbert_d3.csv').write_text('k,TH\n'+''.join(f'{k},{v}\n' for k,v in enumerate(sequence)))
    report={
        'status':'PASS', 'arithmetic':'fractions.Fraction, exact rational arithmetic',
        'parameter_values':[str(d) for d in ds], 'max_k':args.max_k,
        'parameter_degree_cases':len(rows), 'strict_witness_inequalities_checked':total_checks,
        'endpoint_upper_bound_checks':len(rows),
        'box_endpoint_upper_bound_checks_d_ge_1':box_checks, 'illustrative_certificate_gap':str(gap),
        'tested_generating_function_coefficients':len(sequence),
        'all_degree_proof':'article.tex; not supplied by the finite tests',
        'proof_assistant_verification':False,
        'method_note':'Direct witness checks plus a separately coded endpoint-state relaxation; not exhaustive enumeration of all tropical polynomials.'}
    (resultdir/'verification_summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O: this verifier uses assertions.')
    main()
