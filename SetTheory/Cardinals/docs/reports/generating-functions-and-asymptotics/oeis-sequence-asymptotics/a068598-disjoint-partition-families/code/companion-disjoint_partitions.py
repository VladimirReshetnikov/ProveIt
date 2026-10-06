#!/usr/bin/env python3
"""Bounded exact diagnostics for Report163 and OEIS A068598.

Standard library only. No network, input-file, or file-writing API.
Finite enumeration is not an asymptotic or novelty certificate.
"""
import argparse
from functools import lru_cache
from itertools import permutations
import json
import re
import sys

MAX_N = 24
MAX_PARTITION_N = 45
MAX_QUEENS = 8
MAX_CLIQUE_N = 18
MAX_ROUNDING_N = 100000
MAX_THRESHOLD = 10**100
MAX_INVERSE_N = 256
MAX_INVERSE_K = 128
SOURCE_TERMS = (1,1,1,1,1,1,2,2,3,4,6,8,13,18,31,47,75,115,199,312,533,888,
1536,2535,4608,7694,13894,24491,44278,78040,147863,260376,489921,906783,
1701068,3139340,6130726,11328526,22059386,42281301,82180670,157539076,
317031631,606850891,1217662195,2413169272)
QUEEN_TERMS = (1,1,0,0,2,10,4,40,92)
SCOPE = 'Finite diagnostics only; no asymptotic remainder or priority certificate'


def _integer(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(name + ' must be an integer in [' + str(low) + ', ' + str(high) + ']')
    return value


def _require(value, message):
    if not value:
        raise RuntimeError(message)


@lru_cache(None)
def _partitions(n):
    _integer(n, 'partition n', 0, MAX_PARTITION_N)
    bins = [[] for _ in range(n+1)]
    bins[0] = [()]
    for part in range(1, n+1):
        for total in range(n, part-1, -1):
            bins[total].extend(b+(part,) for b in bins[total-part])
    return tuple(sorted(bins[n]))


def _recursive_partitions(n):
    _integer(n, 'recursive partition n', 0, MAX_N)
    def rec(left, minimum):
        if left == 0:
            yield ()
        for first in range(minimum, left+1):
            for rest in rec(left-first, first+1):
                yield (first,)+rest
    return tuple(rec(n, 1))


def _mask(block):
    return sum(1 << (x-1) for x in block)


def _encode(blocks, n):
    anchors = tuple(sorted(b[0] for b in blocks))
    free = tuple(sorted((x,b[0]) for b in blocks for x in b[1:-1]))
    groups = {a: [] for a in anchors}
    for x,a in free:
        groups[a].append(x)
    recovered = tuple(sorted(tuple([a]+groups[a]+[n-a-sum(groups[a])]) for a in anchors))
    _require(recovered == tuple(sorted(blocks)), 'Encoding did not recover matching')
    v = sum(map(len, blocks)); m = len(blocks); q = len(free)
    _require(q == v-2*m, 'Free count identity failed')
    _require(v*(v+1) <= 2*m*n, 'Mass bound failed')
    if n >= 2:
        _require(q <= (n-2)//4, 'Integer free-label bound failed')
    return anchors, free


def _enumerate(n, encodings=False):
    _integer(n, 'n', 1, MAX_N)
    edges = tuple(b for b in _partitions(n) if len(b) > 1)
    masks = tuple(map(_mask, edges))
    all_count = maximal = largest_free = 0
    codes = set()
    def visit(start, used, chosen):
        nonlocal all_count, maximal, largest_free
        all_count += 1
        if encodings:
            code = _encode(tuple(edges[j] for j in chosen), n)
            _require(code not in codes, 'Encoding collision')
            codes.add(code)
            largest_free = max(largest_free, len(code[1]))
        if all(used & mask for mask in masks):
            maximal += 1
        for j in range(start, len(edges)):
            if not used & masks[j]:
                visit(j+1, used | masks[j], chosen+(j,))
    visit(0, 0, ())
    _require(maximal >= 1, 'No maximal family found')
    upper = 1 if n == 1 else 3**(n-1)*n**((n-2)//4)
    _require(maximal <= upper, 'Explicit upper bound failed')
    return {'n': n, 'strict_partitions': len(edges)+1,
            'all_matchings_without_singleton': str(all_count),
            'maximal_families': str(maximal), 'maximum_free_vertices': largest_free,
            'free_bound': max(0, (n-2)//4), 'upper_bound': str(upper)}


def _clique_count(n):
    _integer(n, 'clique n', 1, MAX_CLIQUE_N)
    edges = _partitions(n)
    masks = tuple(map(_mask, edges))
    neighbors = [set(j for j,y in enumerate(masks) if not x & y) for x in masks]
    def bk(possible, excluded):
        if not possible and not excluded:
            return 1
        count = 0
        for v in sorted(possible.copy()):
            count += bk(possible & neighbors[v], excluded & neighbors[v])
            possible.remove(v)
            excluded.add(v)
        return count
    return bk(set(range(len(edges))), set())


def _queen_permutations(k):
    _integer(k, 'queens k', 1, MAX_QUEENS)
    return tuple(p for p in permutations(range(1,k+1))
                 if len({i+x for i,x in enumerate(p,1)}) == k
                 and len({i-x for i,x in enumerate(p,1)}) == k)


def _extension(base, n):
    flat = tuple(x for b in base for x in b)
    _require(len(set(flat)) == len(flat), 'Base is not disjoint')
    _require(all(len(b) == len(set(b)) and sum(b) == n and min(b) > 0 for b in base),
             'Base has an invalid strict partition')
    used = _mask(flat)
    extension = list(base)
    for b in _partitions(n):
        mask = _mask(b)
        if not used & mask:
            extension.append(b)
            used |= mask
    _require((n,) in extension, 'Forced singleton missing')
    _require(all(used & _mask(b) for b in _partitions(n)), 'Extension not maximal')
    return tuple(sorted(extension))


def _queen_checks(queen_to):
    _integer(queen_to, 'queen_to', 1, MAX_QUEENS)
    result = []
    for k in range(1, queen_to+1):
        queens = _queen_permutations(k)
        _require(len(queens) == QUEEN_TERMS[k], 'Queens count mismatch')
        residues = []
        for r in range(1,6):
            n = 5*k+r
            extensions = set()
            for p in queens:
                base = tuple((i,k+x,n-k-i-x) for i,x in enumerate(p,1))
                _require(all(tuple(sorted(b)) == b for b in base), 'Triple ranges overlap')
                extension = _extension(base, n)
                recovered = []
                for i in range(1,k+1):
                    anchored = tuple(b for b in extension if i in b)
                    _require(len(anchored) == 1, 'Anchor not unique')
                    middle = tuple(x for x in anchored[0] if k < x <= 2*k)
                    _require(len(middle) == 1, 'Middle value not unique')
                    recovered.append(middle[0]-k)
                _require(tuple(recovered) == p, 'Queens permutation not recovered')
                _require(extension not in extensions, 'Maximal extensions collide')
                extensions.add(extension)
            residues.append({'n': n, 'distinct_maximal_extensions': str(len(extensions))})
        result.append({'k': k, 'queens': str(len(queens)), 'residues': residues})
    return result


def _greedy_checks():
    result = []
    for k in range(1,5):
        for m in range(2*k, 2*k+3):
            choices = tuple(p for p in permutations(range(k+1,k+m+1), k)
                            if len({i+x for i,x in enumerate(p,1)}) == k)
            product = 1
            for i in range(k):
                product *= m-2*i
            _require(len(choices) >= product >= (m-2*k+2)**k, 'Greedy count bound failed')
            for n in (3*k+2*m+1, 3*k+2*m+2):
                bases = set()
                for p in choices:
                    base = tuple((i,x,n-i-x) for i,x in enumerate(p,1))
                    _require(all(b[0] < b[1] < b[2] and sum(b) == n for b in base),
                             'Greedy triple separation failed')
                    flat = tuple(x for b in base for x in b)
                    _require(len(set(flat)) == 3*k, 'Greedy base not disjoint')
                    _require(base not in bases, 'Greedy base collision')
                    bases.add(base)
                result.append({'k': k, 'm': m, 'n': n, 'choices': str(len(choices)),
                               'product_lower': str(product),
                               'power_lower': str((m-2*k+2)**k)})
    return result


def counts(max_n=MAX_N):
    _integer(max_n, 'max_n', 0, MAX_N)
    values = [1] + [int(_enumerate(n)['maximal_families']) for n in range(1,max_n+1)]
    return {'schema': 'report163-counts-v1', 'scope': SCOPE, 'max_n': max_n,
            'values': [str(x) for x in values]}


def verify(max_n=MAX_N, queen_to=MAX_QUEENS, rounding_to=MAX_ROUNDING_N):
    _integer(max_n, 'max_n', 0, MAX_N)
    _integer(queen_to, 'queen_to', 1, MAX_QUEENS)
    _integer(rounding_to, 'rounding_to', 2, MAX_ROUNDING_N)
    rows = []
    clique_rows = []
    for n in range(1,max_n+1):
        _require(_partitions(n) == _recursive_partitions(n), 'Partition generators disagree')
        row = _enumerate(n, encodings=True)
        _require(int(row['maximal_families']) == SOURCE_TERMS[n], 'OEIS mismatch')
        rows.append(row)
        if n <= MAX_CLIQUE_N:
            independent = _clique_count(n)
            _require(independent == int(row['maximal_families']), 'Clique count mismatch')
            clique_rows.append({'n': n, 'maximal_cliques': str(independent)})
    for n in range(2,rounding_to+1):
        _require((n-1)**2//(4*n) == (n-2)//4, 'Floor identity failed')
        k = (n-1)//5
        _require(1 <= n-5*k <= 5 and n-3*k > 2*k, 'Queens floor separation failed')
    return {'schema': 'report163-checks-v1', 'status': 'PASS', 'scope': SCOPE,
            'bounds': {'max_n': max_n, 'queen_to': queen_to, 'rounding_to': rounding_to,
                       'clique_to': min(max_n, MAX_CLIQUE_N)},
            'empty_convention': '1', 'matchings': rows, 'maximal_cliques': clique_rows,
            'queens_extensions': _queen_checks(queen_to), 'greedy_examples': _greedy_checks()}


def threshold(value, max_n=MAX_N):
    _integer(value, 'value', 1, MAX_THRESHOLD)
    _integer(max_n, 'max_n', 0, MAX_N)
    values = counts(max_n)['values']
    first = next((n for n,a in enumerate(values) if int(a) >= value), None)
    return {'schema': 'report163-threshold-v1', 'scope': 'Exact bounded first-passage scan only',
            'value': str(value), 'max_n': max_n, 'reached': first is not None,
            'first_n': first, 'count_at_first': values[first] if first is not None else None,
            'all_counts': values}


def integer_bounds(value):
    _integer(value, 'value', 1, MAX_THRESHOLD)
    if value == 1:
        lower = upper = k = 0
    else:
        lower = next((n for n in range(2, MAX_INVERSE_N+1)
                      if 3**(n-1)*n**((n-2)//4) >= value), None)
        _require(lower is not None, 'Integer lower scan cap insufficient')
        factorial_lower = 1
        for k in range(1, MAX_INVERSE_K+1):
            factorial_lower *= 2*k
            if factorial_lower >= value:
                break
        else:
            raise RuntimeError('Integer factorial scan cap insufficient')
        upper = 7*k+1
    return {'schema': 'report163-integer-bounds-v1',
            'scope': 'Proved finite bracket; endpoints need not be exact first passages',
            'value': str(value), 'lower_n': lower, 'upper_n': upper,
            'factorial_k': k, 'max_lower_scan': MAX_INVERSE_N,
            'max_factorial_scan': MAX_INVERSE_K}


def sources():
    return {'schema': 'report163-sources-v1', 'source': 'OEIS A068598',
            'url': 'https://oeis.org/A068598',
            'official_snapshot_url': 'https://github.com/oeis/oeisdata/blob/main/seq/A068/A068598.seq',
            'snapshot_revision': '50, 2026-02-17 22:51:17', 'retrieved': '2026-10-03',
            'snapshot_sha256': '103c4e77d14ab4bc5192ea53e5e66d515c279f39b5f873f6e3cd0d945b4b1b70',
            'offset': 0, 'values': [str(x) for x in SOURCE_TERMS],
            'checked_enumeration_through': MAX_N,
            'note': 'Displayed numeric excerpt; later terms are source data, not independent enumerations'}


def _token(value):
    if len(value) > 101 or re.fullmatch(r'0|[1-9][0-9]*', value, flags=re.ASCII) is None:
        raise argparse.ArgumentTypeError('Canonical nonnegative ASCII integer required')
    return int(value)


def _json(value):
    result = json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False)+'\n'
    _require(len(result.encode('ascii')) <= 2*1024*1024, 'Output cap exceeded')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    c = sub.add_parser('counts'); c.add_argument('--max-n', type=_token, default=MAX_N)
    v = sub.add_parser('verify'); v.add_argument('--max-n', type=_token, default=MAX_N)
    v.add_argument('--queen-to', type=_token, default=MAX_QUEENS)
    v.add_argument('--rounding-to', type=_token, default=MAX_ROUNDING_N)
    t = sub.add_parser('threshold'); t.add_argument('--value', type=_token, required=True)
    t.add_argument('--max-n', type=_token, default=MAX_N)
    b = sub.add_parser('bounds'); b.add_argument('--value', type=_token, required=True)
    sub.add_parser('sources')
    args = parser.parse_args()
    try:
        if args.command == 'counts': result = counts(args.max_n)
        elif args.command == 'verify': result = verify(args.max_n,args.queen_to,args.rounding_to)
        elif args.command == 'threshold': result = threshold(args.value,args.max_n)
        elif args.command == 'bounds': result = integer_bounds(args.value)
        else: result = sources()
    except ValueError as error:
        parser.error(str(error))
    except RuntimeError as error:
        print('Verification failed: '+str(error), file=sys.stderr)
        return 1
    sys.stdout.write(_json(result))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
