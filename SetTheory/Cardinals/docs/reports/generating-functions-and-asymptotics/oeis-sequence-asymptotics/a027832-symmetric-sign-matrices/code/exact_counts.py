#!/usr/bin/env python3
"""Bounded exact labelled-graph recursion and independent finite enumerations."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
import itertools
import json
import math
from pathlib import Path
from common import ROOT, emit, integer, new_file_path, require

MAX_ORDER = 17
MAX_VERTICES = 18
MAX_STATES = 200000
MAX_TRANSITIONS = 8000000


class _Counter:
    """A per-computation bounded cache; all arithmetic is integral."""
    def __init__(self):
        self.cache = {}
        self.transitions = 0

    def count(self, state):
        # Zero-cap vertices have no incident edges; all other caps can be clipped.
        state = tuple(c for c in state if c)
        r = len(state)
        if r <= 1:
            return 1
        state = tuple(min(c, r-1) for c in state)
        if state[0] == r-1:
            return 1 << math.comb(r, 2)
        if state in self.cache:
            return self.cache[state]
        require(len(self.cache) < MAX_STATES, 'exact recursion state budget exceeded')
        cap = state[0]
        groups = [(c, len(list(g))) for c, g in itertools.groupby(state[1:])]
        total = 0
        def visit(j, left, new, multiplicity):
            nonlocal total
            if j == len(groups):
                self.transitions += 1
                require(self.transitions <= MAX_TRANSITIONS, 'exact recursion transition budget exceeded')
                total += multiplicity * self.count(tuple(sorted(new)))
                return
            c, size = groups[j]
            for chosen in range(min(size, left)+1):
                visit(j+1, left-chosen, new+[c-1]*chosen+[c]*(size-chosen),
                      multiplicity*math.comb(size, chosen))
        visit(0, cap, [], 1)
        require(len(self.cache) < MAX_STATES, 'exact recursion state budget exceeded')
        self.cache[state] = total
        return total


def _validate_mixed(M, k, f, maximum=MAX_VERTICES):
    integer(M, 0, maximum, 'graph order')
    integer(k, 0, max(0, M-1), 'degree cap')
    integer(f, 0, M, 'free vertices')


def capped_graph_count(caps):
    """Count labelled graphs with arbitrary caps, at most twelve vertices."""
    require(isinstance(caps, (tuple, list)), 'caps must be a tuple or list')
    integer(len(caps), 0, 12, 'cap-vector length')
    for cap in caps:
        integer(cap, 0, max(0, len(caps)-1), 'vertex degree cap')
    return _Counter().count(tuple(sorted(caps)))


def mixed_graph_count(M, k, f=1):
    """U_f(M,k), for M<=18 and cap<=8, or the trivial full cap M-1."""
    _validate_mixed(M, k, f)
    require(k <= 8 or k == M-1, 'mixed count cap must be at most 8 or full')
    return _Counter().count(tuple([k]*(M-f)+[max(0,M-1)]*f))


def sign_matrix_count(n):
    """Symmetric +/-1 matrices with nonnegative row sums, diagonal included."""
    integer(n, 0, MAX_ORDER, 'matrix order')
    return _Counter().count(tuple([n//2]*n+[n]))


def brute_sign_matrices(n):
    """Literal symmetric-matrix enumeration, independent of the graph bridge."""
    integer(n, 0, 5, 'direct matrix order')
    cells = list(itertools.combinations_with_replacement(range(n), 2))
    total = 0
    for code in range(1 << len(cells)):
        row_sums = [0]*n
        for bit, (i,j) in enumerate(cells):
            sign = -1 if code >> bit & 1 else 1
            row_sums[i] += sign
            if i != j:
                row_sums[j] += sign
        total += all(value >= 0 for value in row_sums)
    return total


def brute_mixed_graphs(M, k, f):
    """Enumerate every edge subset for M<=6, without using the recursion."""
    _validate_mixed(M, k, f, 6)
    edges = list(itertools.combinations(range(M), 2))
    total = 0
    for code in range(1 << len(edges)):
        degrees = [0]*M
        for bit, (i,j) in enumerate(edges):
            if code >> bit & 1:
                degrees[i] += 1
                degrees[j] += 1
        total += all(d <= k for d in degrees[:M-f])
    return total


def read_prefix():
    path = ROOT/'code/oeis_prefix.json'
    require(path.stat().st_size < 8192, 'OEIS prefix file size cutoff')
    source = json.loads(path.read_text(encoding='utf-8'))
    require(source.get('offset') == 1 and source.get('sequence') == 'A027832', 'OEIS prefix identity')
    terms = source.get('terms')
    require(isinstance(terms,list) and len(terms) == 17, 'OEIS prefix length')
    for term in terms:
        require(isinstance(term,int) and not isinstance(term,bool) and 0 < term < 1 << 154,
                'invalid OEIS prefix term')
    return source


def verify(n=MAX_ORDER):
    integer(n, 1, MAX_ORDER, 'maximum matrix order')
    source = read_prefix()
    counter = _Counter()
    exact = [{'n':0,'one_free':1,'all_capped':1}]
    for order in range(1,n+1):
        M, k = order+1, order//2
        U = counter.count(tuple([k]*order+[order]))
        B = counter.count(tuple([k]*M))
        require(U == source['terms'][order-1], 'OEIS A027832 mismatch at n=%d'%order)
        numerator = sum(math.comb(order,d) for d in range(k+1))
        require(B <= U and U*numerator <= B*(1<<order), 'exact one-free FKG bounds')
        exact.append({'n':order,'one_free':U,'all_capped':B})
    sign_checks = []
    for order in range(6):
        direct = brute_sign_matrices(order)
        recursive = counter.count(tuple([order//2]*order+[order]))
        require(direct == recursive, 'literal sign-matrix mismatch')
        sign_checks.append({'n':order,'count':direct})
    graph_checks = 0
    for M in range(7):
        for k in range(max(1,M)):
            for f in range(M+1):
                expected = counter.count(tuple([k]*(M-f)+[max(0,M-1)]*f))
                require(brute_mixed_graphs(M,k,f) == expected, 'direct mixed graph mismatch')
                graph_checks += 1
    free_checks = 0
    free_rows = []
    for M in range(2,13):
        k = (M-1)//2
        B = counter.count(tuple([k]*M))
        numerator = sum(math.comb(M-1,d) for d in range(k+1))
        row = []
        for f in range(M+1):
            U = counter.count(tuple([k]*(M-f)+[M-1]*f))
            require(B <= U <= 1 << math.comb(M,2), 'mixed inclusion bounds')
            require(U*numerator**f <= B*(1 << ((M-1)*f)), 'multi-free FKG bound')
            if f == M:
                require(U == 1 << math.comb(M,2), 'all-free graph identity')
            row.append(U)
            free_checks += 1
        free_rows.append({'M':M,'k':k,'counts_for_f_0_through_M':row})
    variance_checks = 0
    for b in range(1,33):
        for a,D in ((1,10),(1,4),(1,2),(3,4),(9,10)):
            weights = [math.comb(b,d)*a**d*(D-a)**(b-d) for d in range(b+1)]
            mass = first = second = 0
            for k,w in enumerate(weights):
                mass += w; first += k*w; second += k*k*w
                require(4*(second*mass-first*first) <= b*mass*mass,
                        'exact capped-binomial variance bound')
                variance_checks += 1
    return {'status':'PASS','arithmetic':'exact integers','oeis_sequence':'A027832',
            'oeis_offset':1,'oeis_regenerated_terms':n,'oeis_full_17_term_prefix_checked':n==17,
            'empty_order_added_separately':True,'exact_counts':exact,
            'literal_symmetric_sign_matrix_checks':sign_checks,
            'exact_capped_binomial_variance_checks':variance_checks,
            'direct_mixed_graph_checks':graph_checks,'multi_free_exact_bounds_checks':free_checks,
            'mixed_counts':free_rows,'recursion_cache_states':len(counter.cache),
            'recursion_transitions':counter.transitions,
            'scope':'Finite exact identities and prefix agreement; no asymptotic error certification.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, default=MAX_ORDER)
    parser.add_argument('--output')
    args = parser.parse_args()
    integer(args.n, 1, MAX_ORDER, 'maximum matrix order')
    if args.output is not None:
        new_file_path(args.output)
    emit(verify(args.n), args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
