#!/usr/bin/env python3
"""Refined run-index candidate pools, reversible encoding and finite bounds.

Finite exact checks only. All patterns are arbitrary subsequences, and the
entering edge is counted after testing ascent-sequence legality.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
from math import comb, prod
from common import REPORT_NUMBER, emit, integer, new_file_path, require
from exact_counts import ascent_count, checked_word, is_ascent, literal_avoidance, raw_ascent_words

MAX_LENGTH = 64
MAX_VERIFY_LENGTH = 9
MAX_TABLE_LENGTH = 10_000


def pattern_checked(pattern):
    integer(pattern, 100, 110, 'pattern')
    require(pattern in (100, 110), 'pattern must be 100 or 110')
    return pattern


def marks(word, pattern):
    if pattern == 110:
        first = {}
        for i, x in enumerate(word):
            first.setdefault(x, i)
        return tuple(i for i, x in enumerate(word) if i != first[x])
    last = {x: i for i, x in enumerate(word)}
    return tuple(i for i, x in enumerate(word) if i != last[x])


def encode_word(word, pattern):
    """Immutable (n, marked positions, labels, run lengths, candidate ranks)."""
    pattern_checked(pattern)
    word = checked_word(word, MAX_LENGTH)
    require(is_ascent(word), 'encoding input must be an ascent sequence')
    require(literal_avoidance(word)[1 if pattern == 100 else 2], 'forbidden pattern in input')
    n = len(word)
    marked = marks(word, pattern)
    marked_set = set(marked)
    labels = tuple(word[i] for i in marked)
    starts = ([0] + [i for i in range(1, n) if word[i-1] >= word[i]]) if n else []
    ends = starts[1:] + [n] if n else []
    lengths, ranks = [], []
    for j, (start, end) in enumerate(zip(starts, ends), 1):
        ell = end - start
        ceiling = start - j + ell
        seen = set(word[:start])
        unfinished = seen & set(word[start:])
        candidates = sorted((set(range(ceiling + 1)) - seen) |
                            (unfinished if pattern == 100 else set()))
        chosen = tuple(word[i] for i in range(start, end) if i not in marked_set)
        require(set(chosen) <= set(candidates), 'unmarked value outside candidate pool')
        ranks.append(tuple(candidates.index(x) for x in chosen))
        lengths.append(ell)
    return n, marked, labels, tuple(lengths), tuple(ranks)


def validate_encoding(encoding, pattern):
    pattern_checked(pattern)
    require(isinstance(encoding, tuple) and len(encoding) == 5, 'encoding must be a five-tuple')
    n, marked, labels, lengths, ranks = encoding
    integer(n, 0, MAX_LENGTH, 'encoded length')
    for value in (marked, labels, lengths, ranks):
        require(isinstance(value, tuple) and len(value) <= n, 'encoding fields must be bounded tuples')
    require(len(marked) == len(labels), 'marked positions and labels differ in length')
    for position in marked:
        integer(position, 0, n-1, 'marked position')
    for label in labels:
        integer(label, 0, n-1, 'marked label')
    require(all(x < y for x, y in zip(marked, marked[1:])), 'marked positions must strictly increase')
    require(all(x <= y for x, y in zip(labels, labels[1:])), 'marked labels must weakly increase')
    for ell in lengths:
        integer(ell, 1, MAX_LENGTH, 'run length')
    require(sum(lengths) == n, 'run lengths must sum to n')
    require(len(ranks) == len(lengths), 'one rank tuple required per run')
    for ell, subset in zip(lengths, ranks):
        require(isinstance(subset, tuple) and len(subset) <= ell, 'ranks must be bounded tuples')
        for rank in subset:
            integer(rank, 0, 2*MAX_LENGTH, 'candidate rank')
        require(all(x < y for x, y in zip(subset, subset[1:])), 'ranks must strictly increase')
    require(n == 0 or len(marked) < n, 'nonempty word needs an unmarked occurrence')
    require(len(lengths) <= len(marked)+1, 'too many runs')
    return encoding


def decode_details(encoding, pattern):
    n, marked, labels, lengths, ranks = validate_encoding(encoding, pattern)
    specified = dict(zip(marked, labels))
    r = len(marked)
    word, records = [], []
    seen, unfinished, closed = set(), set(), set()
    A = 0
    for j, (ell, rankset) in enumerate(zip(lengths, ranks), 1):
        p, d = len(word), len(seen)
        q = p-d
        require(A == p-j+1, 'prefix-run ascent identity fails')
        ceiling = A+ell-1
        alphabet = set(range(ceiling+1))
        require(seen <= alphabet, 'past label outside refined ceiling')
        unseen = alphabet-seen
        require(len(unseen) == ell+q-j+1, 'exact unseen-pool size fails')
        require(len(unfinished) <= r-q, 'unfinished-label budget fails')
        candidates = sorted(unseen | (unfinished if pattern == 100 else set()))
        cap = ell+r-j+1
        require(len(candidates) <= cap, 'refined candidate bound fails')
        require(all(x < len(candidates) for x in rankset), 'rank outside actual candidate pool')
        subset = tuple(candidates[x] for x in rankset)
        expected = sum(i not in specified for i in range(p, p+ell))
        require(len(subset) == expected, 'rank count disagrees with skeleton')
        records.append({'run': j, 'prefix_length': p, 'run_length': ell,
                        'q': q, 'ascents': A, 'ceiling': ceiling,
                        'unfinished': tuple(sorted(unfinished)),
                        'unseen_size': len(unseen), 'candidate_size': len(candidates),
                        'candidate_cap': cap, 'retained_size': expected})
        values = iter(subset)
        for i in range(p, p+ell):
            x = specified[i] if i in specified else next(values)
            require(x <= ceiling, 'run entry exceeds refined ceiling')
            if not word:
                require(x == 0, 'word must start at zero')
            else:
                require(x <= A+1, 'entry violates ascent legality')
                require((word[-1] >= x) if i == p else (word[-1] < x), 'incorrect run boundary')
            if pattern == 110:
                require((x in seen) == (i in specified), 'first-occurrence status mismatch')
            else:
                require(x not in closed, 'label follows its designated last occurrence')
                if i in specified:
                    unfinished.add(x)
                else:
                    unfinished.discard(x)
                    closed.add(x)
            if word:
                A += word[-1] < x
            word.append(x)
            seen.add(x)
    result = tuple(word)
    require(len(result) == n and marks(result, pattern) == marked, 'occurrence encoding mismatch')
    require(not unfinished, 'unfinished label remains at end')
    require(is_ascent(result), 'illegal decoded ascent sequence')
    require(literal_avoidance(result)[1 if pattern == 100 else 2], 'decoded forbidden pattern')
    return result, records


def decode_word(encoding, pattern):
    return decode_details(encoding, pattern)[0]


def table_term(N, m):
    integer(N, 1, MAX_TABLE_LENGTH, 'table size')
    integer(m, 1, N, 'table dimension')
    return comb(m*(m+1)//2+N-m-1, N-m)


def skeleton_bound(n, r):
    integer(n, 1, MAX_LENGTH, 'skeleton word length')
    integer(r, 0, n-1, 'repetition count')
    return comb(n,r)*comb(n+r-1,r)*sum(comb(n-1,h) for h in range(r+1))


def vandermonde_bound(r, lengths, retained_sizes):
    integer(r, 0, MAX_LENGTH-1, 'repetition count')
    require(isinstance(lengths, (tuple,list)) and len(lengths) <= MAX_LENGTH, 'bounded run list required')
    require(isinstance(retained_sizes, (tuple,list)) and len(retained_sizes) == len(lengths),
            'one retained size per run required')
    for ell in lengths:
        integer(ell, 1, MAX_LENGTH, 'run length')
    n = sum(lengths)
    require(n <= MAX_LENGTH, 'total length exceeds cutoff')
    for ell,k in zip(lengths,retained_sizes):
        integer(k,0,ell,'retained size')
    require(sum(retained_sizes) == n-r, 'retained total must be n-r')
    require(len(lengths) <= r+1, 'too many runs')
    if n == 0:
        require(r == 0, 'empty word requires r=0')
        return 1,1,1
    require(r < n, 'repetition count outside support')
    caps = [ell+r-j+1 for j,ell in enumerate(lengths,1)]
    product = prod(comb(c,k) for c,k in zip(caps,retained_sizes))
    middle = comb(sum(caps),n-r)
    triangle = comb(n+r*(r+1)//2,n-r)
    require(product <= middle <= triangle, 'Vandermonde comparison fails')
    require(triangle == table_term(n+1,r+1), 'shifted triangular identity fails')
    return product,middle,triangle


def finite_upper_bound(n):
    integer(n,0,MAX_LENGTH,'upper-bound length')
    return 1 if n == 0 else sum(skeleton_bound(n,r)*table_term(n+1,r+1) for r in range(n))


def verify(max_n=9):
    integer(max_n,0,MAX_VERIFY_LENGTH,'raw verification cutoff')
    total_raw, total_runs, total_encodings, total_skeletons = 0,0,0,0
    receipts = []
    digests = {p:hashlib.sha256() for p in (100,110)}
    for n in range(max_n+1):
        data = {p:{'encodings':set(),'skeletons':Counter(),'bounds':{},'runs':0} for p in (100,110)}
        for word in raw_ascent_words(n):
            total_raw += 1
            literal = literal_avoidance(word)
            for p,index in ((100,1),(110,2)):
                if not literal[index]:
                    continue
                encoding = encode_word(word,p)
                decoded,run_records = decode_details(encoding,p)
                require(decoded == word, 'rank decoder failed round trip')
                selected = data[p]
                require(encoding not in selected['encodings'], 'encoding collision')
                selected['encodings'].add(encoding)
                if p == 100:
                    for row in run_records:
                        cut = row['prefix_length']
                        require(set(row['unfinished']) == set(word[:cut]) & set(word[cut:]),
                                'decoded unfinished set is incorrect')
                r = len(encoding[1])
                require(r == n-len(set(word)), 'mark count mismatch')
                bound,_,_ = vandermonde_bound(r,encoding[3],tuple(map(len,encoding[4])))
                skeleton = encoding[:4]
                selected['skeletons'][skeleton] += 1
                selected['bounds'][skeleton] = bound
                selected['runs'] += len(run_records)
                digests[p].update((repr(encoding)+'\n').encode('ascii'))
        for p in (100,110):
            selected = data[p]
            for skeleton,count in selected['skeletons'].items():
                require(count <= selected['bounds'][skeleton], 'skeleton fiber exceeds product bound')
            for r in range(n):
                observed = sum(len(s[1]) == r for s in selected['skeletons'])
                require(observed <= skeleton_bound(n,r) <= 16**n, 'skeleton count bound fails')
            count = len(selected['encodings'])
            require(count <= finite_upper_bound(n), 'total upper comparison fails')
            total_encodings += count
            total_runs += selected['runs']
            total_skeletons += len(selected['skeletons'])
            receipts.append({'n':n,'pattern':p,'count':count,'skeletons':len(selected['skeletons']),
                             'run_candidate_checks':selected['runs'],'finite_upper_bound':finite_upper_bound(n)})
    for N in range(1,101):
        for m in range(1,N+1):
            require(table_term(N,m) == comb(N-1+(m-1)*m//2,N-m), 'extended triangular identity fails')
    return {'status':'PASS','report_number':REPORT_NUMBER,'raw_words':total_raw,
            'class_encodings':total_encodings,'run_candidate_checks':total_runs,
            'skeletons_checked':total_skeletons,'table_identities_checked':5050,
            'encoding_sha256':{str(p):h.hexdigest() for p,h in digests.items()},'rows':receipts,
            'scope':'Exact bounded tests only; asymptotic claims are proved in the article.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=9)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(verify(args.max_n),args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:
        raise SystemExit(str(exc))
