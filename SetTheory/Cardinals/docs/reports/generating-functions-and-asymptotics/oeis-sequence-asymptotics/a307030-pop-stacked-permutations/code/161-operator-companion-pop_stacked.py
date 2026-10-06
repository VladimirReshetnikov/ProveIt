#!/usr/bin/env python3
"""Bounded exact Report161 companion; Python 3.10+, standard library only.

The commands emit deterministic JSON to stdout. No network, input-file or
file-writing API is used. Finite checks are not a proof of the analytic
asymptotic theorem or a numerical certificate of its constants/inverse.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import permutations
import json
from math import comb, factorial
import re
import sys

MAX_N = 70
MAX_BRUTE = 9
MAX_POSET = 10
MAX_DIRECT = 12
MAX_VALUE = 10 ** 200
MAX_JSON_BYTES = 2 * 1024 * 1024

# Embedded source data: no external source file is executed or read at runtime.
# The 25 displayed OEIS terms are separately transcribed from the %S/%T/%U
# lines, rather than generated from the recurrence or sliced from PAPER_TABLE.
OEIS_TERMS = (
    1, 1, 3, 11, 49, 263, 1653, 11877, 95991, 862047, 8516221,
    91782159, 1071601285, 13473914281, 181517350571, 2608383775171,
    39824825088809, 643813226048935, 10986188094959045,
    197337931571468445, 3721889002400665951, 73539326922210382215,
    1519081379788242418149, 32743555520207058219615,
    735189675389014372317381,
)
PAPER_TABLE = (
    1, 1, 3, 11, 49, 263, 1653, 11877, 95991, 862047, 8516221,
    91782159, 1071601285, 13473914281, 181517350571, 2608383775171,
    39824825088809, 643813226048935, 10986188094959045,
    197337931571468445, 3721889002400665951, 73539326922210382215,
    1519081379788242418149, 32743555520207058219615,
    735189675389014372317381, 17167470189102029106503457,
    416297325393961581614919699, 10468759109047048511785181499,
    272663345523662949571086535201, 7346518362495550669587951987399,
    204539324291355079758576427320853, 5878416448467628215599958670190869,
    174223945386975482728912851110751431,
    5320106374135453888563313157982976111,
    167232974698164950641578719412434688845,
    5407019929661274797886581276653666104943,
    179677314965899717327756420597568210468933,
    6132116544121046402686046213590718114272089,
    214787281796488809444762543177377466419782267,
    7716175695131570964771559074490172330993576115,
    284131588386675257705011846785657928372695002841,
    10717718945463416620327720805595647805635809236711,
    413908527884993695909526722330319436067536797304549,
    16356508568742954048255540186930772843919017766669517,
    661053598808034620660440013405109251647269697650963759,
)
SOURCES = {
    'oeis': {
        'sequence': 'A307030', 'url': 'https://oeis.org/A307030',
        'offset': 1, 'displayed_terms': 25, 'retrieved_utc_date': '2026-10-03',
        'entry_revision': '#63, 2021-11-18 11:27:57',
        'snapshot_sha256': '0729cb13dcdd2a77adf55b4fa2f1301fdde9df602bfe3f1e8fd12ac5f1d22a39',
        'scope': 'The 25 displayed terms only; the linked b-file is not embedded or claimed checked.',
    },
    'counting_paper': {
        'authors': ['Anders Claesson', 'Bjarki Agust Gudmundsson', 'Jay Pantone'],
        'title': 'Counting pop-stacked permutations in polynomial time',
        'url': 'https://akc.is/papers/033-Counting-pop-stacked-permutations-in-polynomial-time.pdf',
        'arxiv': 'https://arxiv.org/abs/1908.08910',
        'recurrence_location': 'Equations (2), (4), (5), pp. 4-5',
        'table_location': 'Table 1, p. 7, n=1,...,45',
        'retrieved_utc_date': '2026-10-03',
        'pdf_sha256': 'e822a3fc535b5ca7950bbb8efc6222cd4f5dfcdfe940065cc2105c43e7d601fc',
        'text_sha256': '04e0b6c62035cc3386ed37f00f89d621ea02566a448dbbb4062e2e38fcbfbd51',
    },
    'image_characterization': {
        'authors': ['Andrei Asinowski', 'Cyril Banderier', 'Sara Billey',
                    'Benjamin Hackl', 'Svante Linusson'],
        'title': 'Pop-stack sorting and its image: Permutations with overlapping runs',
        'url': 'https://lipn.fr/~cb/Papers/popstack.pdf',
        'location': 'Theorem 1 and proof, pp. 2-3',
    },
}
LIMITATION = ('Exact finite checks only. They do not prove the analytic asymptotic '
              'theorem, certify decimal values of rho or C, provide an effective '
              'asymptotic error/onset, or certify an asymptotic integer inverse.')


class InputError(ValueError):
    """Invalid type, domain or bounded workload."""


class CheckFailure(RuntimeError):
    """An explicit mathematical check failed, including under python -O."""


def integer(value, name, lower=0, upper=MAX_N):
    if type(value) is not int or not lower <= value <= upper:
        raise InputError(f'{name} must be an actual int in [{lower}, {upper}]')
    return value


def check(condition, message):
    if not condition:
        raise CheckFailure(message)


def endpoint_tables(max_n=MAX_N):
    """Published endpoint recurrence with conventional southwest prefix sums.

    f[n][c][d] counts permutations whose final maximal ascending run has
    endpoints c,d. Values outside 1<=c<=d<=n are zero. Return totals and
    endpoint tables; the empty permutation contributes p[0]=1 separately.
    O(N^4) integer operations, O(N^3) integer cells; N<=70.
    """
    integer(max_n, 'max_n')
    tables = [[[0]]]
    prefixes = [[[0]]]
    totals = [1]

    def prefix(n, a, b):
        if n < 1 or a < 1 or b < 1:
            return 0
        return prefixes[n][min(a, n)][min(b, n)]

    for n in range(1, max_n + 1):
        f = [[0] * (n + 1) for _ in range(n + 1)]
        for c in range(1, n + 1):
            for d in range(c, n + 1):
                value = int(c == 1 and d == n)
                if c == d:
                    value += prefix(n - 1, c - 1, n - 1) - prefix(n - 1, c - 1, c - 1)
                else:
                    for ell in range(d - c):
                        m = n - ell - 2
                        value += comb(d - c - 1, ell) * (
                            prefix(m, d - ell - 2, m) - prefix(m, d - ell - 2, c - 1))
                f[c][d] = value
        g = [[0] * (n + 1) for _ in range(n + 1)]
        for a in range(1, n + 1):
            for b in range(1, n + 1):
                g[a][b] = f[a][b] + g[a - 1][b] + g[a][b - 1] - g[a - 1][b - 1]
        tables.append(f)
        prefixes.append(g)
        totals.append(g[n][n])
    return totals, tables


def counts(max_n=MAX_N):
    return endpoint_tables(max_n)[0]


def literal_endpoint_tables(max_n=MAX_DIRECT):
    """Independent implementation of equation (2), without prefix sums."""
    integer(max_n, 'max_n', 0, MAX_DIRECT)
    tables = [[[0]]]
    for n in range(1, max_n + 1):
        f = [[0] * (n + 1) for _ in range(n + 1)]
        for c in range(1, n + 1):
            for d in range(c, n + 1):
                value = int(c == 1 and d == n)
                if c == d:
                    value += sum(tables[n - 1][a][b]
                                 for a in range(1, c) for b in range(c, n))
                else:
                    for ell in range(d - c):
                        m = n - ell - 2
                        if m > 0:
                            value += comb(d - c - 1, ell) * sum(
                                tables[m][a][b] for a in range(1, d - ell - 1)
                                for b in range(c, m + 1))
                f[c][d] = value
        tables.append(f)
    return tables


def _permutation(p, upper=MAX_N):
    if type(p) not in (list, tuple) or len(p) > upper:
        raise InputError(f'permutation must be a list or tuple of length at most {upper}')
    n = len(p)
    for v in p:
        integer(v, 'permutation entry', 1, n)
    if len(set(p)) != n:
        raise InputError('entries must be exactly 1,...,n, without repetition')
    return tuple(p)


def _apply_stack(p):
    stack, out = [], []
    for v in p:
        if stack and v > stack[-1]:
            while stack:
                out.append(stack.pop())
        stack.append(v)
    while stack:
        out.append(stack.pop())
    return tuple(out)


def apply_stack(p):
    """Literal push/flush pop-stack procedure on a bounded permutation."""
    return _apply_stack(_permutation(p))


def _ascending_runs(p):
    runs = []
    for v in p:
        if not runs or v < runs[-1][-1]:
            runs.append([v])
        else:
            runs[-1].append(v)
    return runs


def ascending_runs(p):
    return tuple(tuple(run) for run in _ascending_runs(_permutation(p)))


def _overlap(runs):
    return all(left[0] < right[-1] and right[0] < left[-1]
               for left, right in zip(runs, runs[1:]))


def has_overlapping_runs(p):
    return _overlap(_ascending_runs(_permutation(p)))


def canonical_preimage(p):
    p = _permutation(p)
    runs = _ascending_runs(p)
    if not _overlap(runs):
        raise InputError('canonical preimage requires overlapping maximal ascending runs')
    return tuple(v for run in runs for v in reversed(run))


def append_largest(p):
    p = _permutation(p, MAX_N - 1)
    if not _overlap(_ascending_runs(p)):
        raise InputError('monotonicity map requires overlapping maximal ascending runs')
    return p + (len(p) + 1,)


def _composition_edges(n, cuts, overlap=True, maximality=True):
    if n == 0:
        return (), set()
    starts = (0,) + tuple(i + 1 for i in range(n - 1) if cuts >> i & 1)
    ends = tuple(i - 1 for i in starts[1:]) + (n - 1,)
    edges = {(i, i + 1) for a, b in zip(starts, ends) for i in range(a, b)}
    for j in range(len(starts) - 1):
        if overlap:
            edges.add((starts[j], ends[j + 1]))
        if maximality:
            edges.add((starts[j + 1], ends[j]))
    return starts, edges


def composition_edges(n, cuts):
    """Position constraints for the composition encoded by the n-1 cut bits."""
    integer(n, 'n', 0, MAX_POSET)
    integer(cuts, 'cuts', 0, (1 << max(n - 1, 0)) - 1)
    starts, edges = _composition_edges(n, cuts)
    return starts, tuple(sorted(edges))


def _count_extensions(n, edges):
    predecessors = [0] * n
    for a, b in edges:
        predecessors[b] |= 1 << a
    full = (1 << n) - 1

    @cache
    def extend(used):
        if used == full:
            return 1
        total = 0
        for i in range(n):
            if not used >> i & 1 and predecessors[i] & used == predecessors[i]:
                total += extend(used | 1 << i)
        return total
    return extend(0)


def count_extensions(n, edges):
    """Count linear extensions exactly; cyclic constraints correctly give zero."""
    integer(n, 'n', 0, MAX_POSET)
    if type(edges) not in (tuple, list) or len(edges) > n * n:
        raise InputError('edges must be a bounded list or tuple')
    for edge in edges:
        if type(edge) not in (tuple, list) or len(edge) != 2:
            raise InputError('each edge must have two integer endpoints')
        for v in edge:
            integer(v, 'edge endpoint', 0, n - 1)
    return _count_extensions(n, edges)


def composition_distribution(n):
    """Sum position-poset linear extensions over all compositions, independently
    of the endpoint recurrence; kth entry counts k maximal ascending runs.
    """
    integer(n, 'n', 0, MAX_POSET)
    if n == 0:
        return [1]
    by_runs = [0] * (n + 1)
    for cuts in range(1 << (n - 1)):
        starts, edges = _composition_edges(n, cuts)
        by_runs[len(starts)] += _count_extensions(n, edges)
    return by_runs


def _fraction_document(value):
    return {'numerator': str(value.numerator), 'denominator': str(value.denominator)}


def cross_condition_examples():
    # Ordered position-blocks (1,2)|(3,4) obey the first inequality but are
    # not maximal ascending runs. (3,4)|(1,2) obey the second but not overlap.
    def conditions(left, right):
        return left[0] < right[-1], right[0] < left[-1]
    check(conditions((1, 2), (3, 4)) == (True, False), 'forward-only cross-condition witness')
    check(conditions((3, 4), (1, 2)) == (False, True), 'backward-only cross-condition witness')
    counts_by_conditions = {}
    for name, first, second in [('both', True, True), ('overlap_only', True, False),
                                ('maximality_only', False, True)]:
        counts_by_conditions[name] = sum(
            _count_extensions(4, _composition_edges(4, cuts, first, second)[1])
            for cuts in range(8))
    check(counts_by_conditions['both'] == 11, 'cross-condition total')
    check(counts_by_conditions['maximality_only'] == factorial(4), 'all permutation total')
    check(counts_by_conditions['overlap_only'] > 11, 'missing maximality must overcount')
    for n in range(2, MAX_POSET + 1):
        check(_count_extensions(n, _composition_edges(n, (1 << (n - 1)) - 1)[1]) == 0,
              f'all-singleton composition must vanish at n={n}')
    witness = (1, 4, 3, 2, 5)
    preimage = canonical_preimage(witness)
    check(apply_stack(preimage) == witness, 'decreasing-triple witness')
    check(any(witness[i] > witness[i + 1] > witness[i + 2]
              for i in range(len(witness) - 2)), 'witness must contain decreasing triple')
    check(not has_overlapping_runs((4, 3, 2, 1)), 'four decreasing values forbidden')
    return {
        'both_cross_inequalities_are_essential': True,
        'forward_only_nonmaximal_blocks': [[1, 2], [3, 4]],
        'backward_only_nonoverlapping_blocks': [[3, 4], [1, 2]],
        'composition_sum_n4': counts_by_conditions,
        'all_singleton_compositions_vanish_n2_through': MAX_POSET,
        'decreasing_triple_allowed': list(witness),
        'decreasing_triple_witness_preimage': list(preimage),
        'decreasing_quadruple_4321_rejected': True,
    }


def low_order_inverse_coefficients(u, b):
    """Return d0,d1,d2 for the report's formal inverse, at exact rational
    test parameters. This does not evaluate logarithms, rho, C, or an inverse.
    Each argument must be a Fraction, |numerator|<=1000, denominator<=100;
    u must be strictly positive. These are workload limits, not theorem scope.
    """
    for value, name in ((u, 'u'), (b, 'b')):
        if (type(value) is not Fraction or abs(value.numerator) > 1000
                or value.denominator > 100):
            raise InputError(f'{name} must be a bounded actual Fraction')
    if u <= 0:
        raise InputError('u must be positive')
    d0 = -b / u
    d1 = -(d0 ** 2 / 2 + d0 / 2 + Fraction(1, 12)) / u
    d2 = -((d0 + Fraction(1, 2)) * d1 - d0 ** 3 / 6
           - d0 ** 2 / 4 - d0 / 12) / u
    return d0, d1, d2


def inverse_coefficient_checks():
    # Independently substitute the result into F modulo t^3, using truncated
    # polynomial multiplication rather than reusing the coefficient formulas.
    def multiply(a, b):
        return [sum(a[j] * b[k - j] for j in range(k + 1)) for k in range(3)]

    rows = []
    for u in (Fraction(1, 3), Fraction(1, 2), Fraction(1), Fraction(2), Fraction(7, 2)):
        for b in (Fraction(-2), Fraction(-1, 3), Fraction(0), Fraction(1, 2), Fraction(3)):
            d = list(low_order_inverse_coefficients(u, b))
            square, cube = multiply(d, d), multiply(multiply(d, d), d)
            # F = u*d+b+t*(d^2/2+d/2+1/12)
            #                 +t^2*(-d^3/6-d^2/4-d/12) mod t^3.
            residual = [u * v for v in d]
            residual[0] += b
            for k in range(1, 3):
                residual[k] += square[k - 1] / 2 + d[k - 1] / 2
            residual[1] += Fraction(1, 12)
            residual[2] -= cube[0] / 6 + square[0] / 4 + d[0] / 12
            check(residual == [0, 0, 0], 'formal inverse coefficients do not cancel through t^2')
            rows.append({'u': str(u), 'b': str(b), 'd0': str(d[0]),
                         'd1': str(d[1]), 'd2': str(d[2]),
                         'residual_coefficients_t0_to_t2': list(map(str, residual))})
    return {'scope': 'Formal polynomial substitution at rational test parameters only; no numerical inverse or constants.',
            'parameter_pairs_checked': len(rows), 'rows': rows}


def _effective_bound(value, name, maximum, max_n):
    if value is None:
        return min(maximum, max_n)
    integer(value, name, 0, maximum)
    if value > max_n:
        raise InputError(f'{name} cannot exceed max_n')
    return value


def verify_document(max_n=MAX_N, brute_to=None, poset_to=None, direct_to=None):
    integer(max_n, 'max_n')
    brute_to = _effective_bound(brute_to, 'brute_to', MAX_BRUTE, max_n)
    poset_to = _effective_bound(poset_to, 'poset_to', MAX_POSET, max_n)
    direct_to = _effective_bound(direct_to, 'direct_to', MAX_DIRECT, max_n)
    totals, tables = endpoint_tables(max_n)
    oeis_matched, paper_matched = min(max_n, len(OEIS_TERMS)), min(max_n, len(PAPER_TABLE))
    check(totals[1:oeis_matched + 1] == list(OEIS_TERMS[:oeis_matched]), 'OEIS prefix mismatch')
    check(totals[1:paper_matched + 1] == list(PAPER_TABLE[:paper_matched]), 'paper table mismatch')
    direct = literal_endpoint_tables(direct_to)
    for n in range(direct_to + 1):
        check(direct[n] == tables[n], f'literal endpoint table mismatch at n={n}')
    brute_rows, distributions = [], {}
    for n in range(brute_to + 1):
        alphabet = range(1, n + 1)
        image = {_apply_stack(p) for p in permutations(alphabet)}
        accepted, endpoints, by_runs, injected = set(), Counter(), Counter(), set()
        for p in permutations(alphabet):
            runs = _ascending_runs(p)
            if not _overlap(runs):
                continue
            accepted.add(p)
            by_runs[len(runs)] += 1
            if n:
                endpoints[runs[-1][0], runs[-1][-1]] += 1
            preimage = tuple(v for run in runs for v in reversed(run))
            check(_apply_stack(preimage) == p, f'canonical preimage mismatch at n={n}')
            q = p + (n + 1,)
            check(_overlap(_ascending_runs(q)), f'append-largest fails at n={n}')
            check(q[:-1] == p, 'monotonicity inverse fails')
            injected.add(q)
            check(not any(p[j] > p[j + 1] > p[j + 2] > p[j + 3]
                          for j in range(n - 3)), 'forbidden decreasing quadruple found')
        check(image == accepted, f'exact stack-image/predicate set mismatch at n={n}')
        check(len(image) == totals[n], f'image count mismatch at n={n}')
        check(len(injected) == len(accepted), f'monotonicity collision at n={n}')
        if n:
            check(all(endpoints[c, d] == tables[n][c][d]
                      for c in alphabet for d in alphabet), f'refined endpoint mismatch at n={n}')
        distributions[n] = [by_runs[k] for k in range(n + 1)]
        brute_rows.append({
            'n': n, 'permutations_tested': factorial(n), 'image_count': str(len(image)),
            'exact_image_predicate_set_equality': True,
            'canonical_preimages_checked': len(accepted),
            'append_largest_injections_and_inverses_checked': len(injected),
            'refined_last_run_table_checked': n > 0,
            'last_run_endpoint_counts_rows_c1_to_n_columns_d1_to_n': [
                [str(endpoints[c, d]) for d in alphabet] for c in alphabet],
            'by_number_of_runs_k0_to_n': [str(x) for x in distributions[n]],
            'no_consecutive_decreasing_quadruple': True,
        })
    poset_rows = []
    for n in range(poset_to + 1):
        by_runs = composition_distribution(n)
        check(sum(by_runs) == totals[n], f'position-poset total mismatch at n={n}')
        if n in distributions:
            check(by_runs == distributions[n], f'position-poset run distribution mismatch at n={n}')
        if n:
            check(by_runs[1] == 1, f'single run must contribute one at n={n}')
        poset_rows.append({
            'n': n, 'compositions_checked': 1 << max(n - 1, 0),
            'count': str(sum(by_runs)), 'by_number_of_runs_k0_to_n': [str(x) for x in by_runs],
            'coefficient_of_z_n': _fraction_document(Fraction(sum(by_runs), factorial(n))),
            'single_run_count': str(by_runs[1]) if n else None,
        })
    for n in range(max_n + 1):
        check(1 <= totals[n] <= factorial(n), f'elementary bounds fail at n={n}')
        blocks = n // 4
        check(totals[n] * 24 ** blocks <= factorial(n) * 23 ** blocks,
              f'decreasing-quadruple bound fails at n={n}')
        if n:
            check(totals[n - 1] <= totals[n], f'count monotonicity fails at n={n}')
        if n % 2 == 0:
            check(totals[n] >= factorial(n // 2) ** 2, f'interlacing bound fails at n={n}')
    interlacing_rows = []
    for m in range(min(4, brute_to // 2) + 1):
        constructed = set()
        for low in permutations(range(1, m + 1)):
            for high in permutations(range(m + 1, 2 * m + 1)):
                p = tuple(v for pair in zip(low, high) for v in pair)
                check(_overlap(_ascending_runs(p)), 'interlaced lower/upper halves do not overlap')
                constructed.add(p)
        check(len(constructed) == factorial(m) ** 2, 'interlacing injection collision')
        interlacing_rows.append({'m': m, 'distinct_images_checked': len(constructed)})
    return {
        'schema': 1, 'report': 'Report161', 'sequence': 'A307030', 'status': 'pass',
        'limitations': LIMITATION, 'sources': SOURCES,
        'bounds': {'max_n': max_n, 'brute_to': brute_to, 'poset_to': poset_to, 'direct_to': direct_to},
        'oeis_displayed_terms_matched': oeis_matched, 'paper_table_terms_matched': paper_matched,
        'literal_refined_recurrence_checked_n0_through': direct_to,
        'brute_force': brute_rows, 'position_poset_normalization': poset_rows,
        'count_monotonicity_checked_n0_through': max_n,
        'exact_elementary_factorial_and_decreasing_quadruple_bounds_checked_n0_through': max_n,
        'exact_interlacing_lower_bound_checked_even_n_through': 2 * (max_n // 2),
        'interlacing_construction': interlacing_rows,
        'cross_condition_examples': cross_condition_examples(),
        'low_order_formal_inverse': inverse_coefficient_checks(),
    }


def counts_document(max_n=MAX_N):
    values = counts(max_n)
    return {'schema': 1, 'report': 'Report161', 'sequence': 'A307030', 'offset': 0,
            'empty_permutation_count': '1', 'max_n': max_n,
            'method': 'CGP published endpoint recurrence (2), optimized by (4)-(5)',
            'counts_as_decimal_strings': [str(value) for value in values],
            'sources': SOURCES, 'limitations': LIMITATION}


def threshold_document(value, max_n=MAX_N):
    integer(value, 'value', 1, MAX_VALUE)
    values = counts(max_n)
    first = next((n for n, count in enumerate(values) if count >= value), None)
    return {'schema': 1, 'sequence': 'A307030', 'value': str(value), 'max_n': max_n,
            'domain': 'n>=0, with p_0=1', 'reached': first is not None, 'first_n': first,
            'count_at_first_n': str(values[first]) if first is not None else None,
            'count_immediately_before': str(values[first - 1]) if first else None,
            'conclusion': f'N(value)={first}' if first is not None else f'N(value)>{max_n}',
            'method': 'Exact bounded count scan, not an asymptotic or rounded approximation'}


def cli_integer(token):
    if type(token) is not str or len(token) > 201 or re.fullmatch(r'0|[1-9][0-9]*', token) is None:
        raise argparse.ArgumentTypeError('use a canonical nonnegative ASCII decimal integer (at most 201 digits)')
    return int(token)


def encoded_json(document):
    try:
        result = json.dumps(document, indent=2, sort_keys=True, ensure_ascii=True, allow_nan=False) + '\n'
    except (ValueError, TypeError, OverflowError, RecursionError) as exc:
        raise InputError(f'cannot serialize bounded JSON: {exc}') from exc
    if len(result.encode('utf-8')) > MAX_JSON_BYTES:
        raise InputError('JSON output exceeds the 2 MiB bound')
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('counts', 'verify', 'threshold'):
        command = sub.add_parser(name)
        command.add_argument('--max-n', type=cli_integer, default=MAX_N)
        if name == 'verify':
            command.add_argument('--brute-to', type=cli_integer)
            command.add_argument('--poset-to', type=cli_integer)
            command.add_argument('--direct-to', type=cli_integer)
        if name == 'threshold':
            command.add_argument('--value', type=cli_integer, required=True)
    sub.add_parser('sources')
    args = parser.parse_args(argv)
    try:
        if args.command == 'counts':
            result = counts_document(args.max_n)
        elif args.command == 'verify':
            result = verify_document(args.max_n, args.brute_to, args.poset_to, args.direct_to)
        elif args.command == 'threshold':
            result = threshold_document(args.value, args.max_n)
        else:
            result = {'schema': 1, 'sources': SOURCES,
                      'oeis_displayed_terms_as_decimal_strings': list(map(str, OEIS_TERMS)),
                      'paper_table_terms_as_decimal_strings': list(map(str, PAPER_TABLE))}
        output = encoded_json(result)
    except InputError as exc:
        parser.error(str(exc))
    except CheckFailure as exc:
        print(f'check failed: {exc}', file=sys.stderr)
        return 1
    sys.stdout.write(output)
    return 0


if __name__ == '__main__':
    sys.exit(main())
