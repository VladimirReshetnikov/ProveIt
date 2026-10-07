"""Exact arithmetic and strict data loading shared by finite diagnostics.

The directly enumerating audit implements its mathematics separately.
"""
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction
from math import comb, isqrt
from pathlib import Path
import csv
import json


def require(condition, check, context=None):
    if not condition:
        raise RuntimeError(f'CHECK_FAILED[{check}]: {context!r}')


def read_json_unique(path):
    def object_pairs(pairs):
        result = {}
        for key,value in pairs:
            require(key not in result,'json_duplicate',key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(),object_pairs_hook=object_pairs)


def read_table(path, header):
    with Path(path).open(newline='') as stream:
        reader = csv.reader(stream, delimiter='\t')
        require(next(reader, None) == header, 'data_format', str(path))
        rows = []
        for line, row in enumerate(reader, 2):
            require(len(row) == len(header), 'data_format', (str(path), line))
            try:
                values = tuple(int(x) for x in row)
            except ValueError:
                raise RuntimeError(f'CHECK_FAILED[data_format]: {(str(path), line)!r}') from None
            require(all(x >= 0 for x in values), 'data_nonnegative', (str(path), line))
            rows.append(values)
    return rows


def load_rows(folder, expected_max):
    folder = Path(folder)
    moments, roots = {}, {}
    for k, value in read_table(folder/'moments_exact.tsv', ['k', 'M2k']):
        require(k not in moments, 'data_duplicate', ('moment', k))
        moments[k] = value
    for k, m, value in read_table(folder/'root_counts_exact.tsv', ['k', 'm', 'count']):
        require(m not in roots.get(k, {}), 'data_duplicate', ('root', k, m))
        roots.setdefault(k, {})[m] = value
    require(set(moments) == set(range(expected_max+1)) and moments.get(0) == 1
            and set(roots) == set(range(1, expected_max+1))
            and all(set(roots[k]) == set(range(1, k+1)) for k in roots),
            'stored_completeness', {'expected_max_k': expected_max})
    roots[0] = {0: 1}
    return moments, roots


def bells(n):
    values = [1]
    for k in range(n):
        values.append(sum(comb(k, j)*values[j] for j in range(k+1)))
    return values


def python_recurrence(n=16):
    """Independent Python implementation; no C++ or TSV used to generate rows."""
    f = [[0]*(n+1) for _ in range(n+1)]
    e = [[0]*(n+1) for _ in range(n+1)]
    f[0][0] = 1
    for q in range(1, n+1):
        e[0][q] = 1
    for k in range(1, n+1):
        for q in range(1, k+1):
            for a in range(k-q+1):
                b = k-q-a
                for mb in range(b+1):
                    f[k][q+mb] += e[a][q]*f[b][mb]*comb(mb+q-1, q-1)
        for q in range(1, n-k+1):
            e[k][q] = sum(f[k][m]*comb(m+q-1,q-1) for m in range(1,k+1))
    return f


def threshold_s(k, family):
    if family == 'quarter':
        return isqrt(isqrt(k))
    # ln(k)^2 is used only to choose an integer S, never to form a count or ratio.
    # Recheck at two decimal precisions to avoid a binary-float ceil decision.
    with localcontext() as context:
        context.prec = 60
        a = int((Decimal(k).ln()**2).to_integral_value(rounding=ROUND_CEILING))
        context.prec = 100
        b = int((Decimal(k).ln()**2).to_integral_value(rounding=ROUND_CEILING))
    require(a == b, 'threshold_stability', k)
    return a


def union_counts(k, threshold, roots, moment, inject=None):
    if 2*threshold <= k:
        return None
    weighted = sum((Fraction(2*k*value,m) for m,value in roots[k].items()
                    if m >= threshold), Fraction(0))
    double = Fraction(0)
    for q in range(max(1,2*threshold-k), k+1):
        r = k-q
        jmin = max(0,threshold-q)
        cut = [sum(roots[a].get(j,0)*comb(j+q-1,q-1)
                   for j in range(jmin,a+1)) for a in range(r+1)]
        double += Fraction(k,q)*sum(cut[a]*cut[r-a] for a in range(r+1))
    union = weighted-double
    checked_double = double+Fraction(1,2) if inject == 'union_integrality' else double
    require(checked_double.denominator == 1 and union.denominator == 1,
            'union_integrality', (k,threshold))
    checked_union = Fraction(moment+1) if inject == 'union_range' else union
    require(0 <= checked_union <= moment, 'union_range', (k,threshold))
    return {'U':union.numerator,'D':double.numerator,'V':weighted}


def exact_ratio(value):
    q = Fraction(value)
    return {'numerator':str(q.numerator), 'denominator':str(q.denominator)}


def display_ratio(value):
    q = Fraction(value)
    if not q:
        return '0'
    with localcontext() as context:
        context.prec = 40
        d = Decimal(q.numerator)/Decimal(q.denominator)
        if abs(d) < Decimal('0.0001') or abs(d) >= Decimal('100000'):
            return format(d, '.6E').replace('E+', 'e+').replace('E-', 'e-')
        return format(d, '.8f')
