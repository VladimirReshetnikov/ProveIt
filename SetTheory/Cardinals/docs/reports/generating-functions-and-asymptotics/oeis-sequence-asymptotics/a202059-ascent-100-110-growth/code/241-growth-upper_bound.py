#!/usr/bin/env python3
"""Finite run-set encodings for the structural 100/110 upper bound.

110 marks non-first occurrences; 100 marks non-last occurrences. A skeleton
contains the marked positions/labels and increasing-run lengths. Retained sets
supply the remaining entries. This file tests finite injections and exact
binomial inequalities, not an asymptotic fit or a numerical proof of a limit.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
from math import comb, prod
from common import REPORT_NUMBER, emit, integer, new_file_path, require
from exact_counts import (ascent_count, checked_word, is_ascent, literal_avoidance,
                          raw_ascent_words)

MAX_LENGTH = 64
MAX_VERIFY_LENGTH = 9


def _pattern(pattern):
    integer(pattern, 100, 110, 'pattern')
    require(pattern in (100, 110), 'pattern must be 100 or 110')
    return pattern


def _marks(word, pattern):
    if pattern == 110:
        seen = set()
        marked = []
        for i, x in enumerate(word):
            if x in seen:
                marked.append(i)
            seen.add(x)
        return tuple(marked)
    last = {x: i for i, x in enumerate(word)}
    return tuple(i for i, x in enumerate(word) if i != last[x])


def encode_word(word, pattern):
    """Return immutable (n, marked positions, labels, run lengths, run sets)."""
    _pattern(pattern)
    word = checked_word(word, MAX_LENGTH)
    require(is_ascent(word), 'encoding input must be an ascent sequence')
    require(literal_avoidance(word)[1 if pattern == 100 else 2], 'encoding input contains forbidden pattern')
    n = len(word)
    marked = _marks(word, pattern)
    marked_set = set(marked)
    marked_labels = tuple(word[i] for i in marked)
    require(all(x <= y for x, y in zip(marked_labels, marked_labels[1:])),
            'marked labels are not weakly increasing')
    starts = [0] + [i for i in range(1, n) if word[i - 1] >= word[i]] if n else []
    ends = starts[1:] + [n] if n else []
    lengths = tuple(end - start for start, end in zip(starts, ends))
    retained = tuple(tuple(word[i] for i in range(start, end) if i not in marked_set)
                     for start, end in zip(starts, ends))
    require(len(marked) == n - len(set(word)), 'incorrect mark count')
    require(len(lengths) <= len(marked) + 1, 'too many increasing runs')
    return n, marked, marked_labels, lengths, retained


def _validate_encoding(encoding, pattern):
    _pattern(pattern)
    require(isinstance(encoding, tuple) and len(encoding) == 5, 'encoding must be a five-tuple')
    n, marked, labels, lengths, retained = encoding
    integer(n, 0, MAX_LENGTH, 'encoded length')
    for value in (marked, labels, lengths, retained):
        require(isinstance(value, tuple), 'encoding fields must be tuples')
        require(len(value) <= n, 'encoding field length exceeds encoded length')
    require(len(marked) == len(labels), 'marked positions and labels have different lengths')
    for position in marked:
        integer(position, 0, n - 1, 'marked position')
    for label in labels:
        integer(label, 0, n - 1, 'marked label')
    require(all(x < y for x, y in zip(marked, marked[1:])), 'marked positions must strictly increase')
    require(all(x <= y for x, y in zip(labels, labels[1:])), 'marked labels must weakly increase')
    for length in lengths:
        integer(length, 1, MAX_LENGTH, 'run length')
    require(sum(lengths) == n, 'run lengths must sum to word length')
    require(len(retained) == len(lengths), 'one retained set is required per run')
    for length, subset in zip(lengths, retained):
        require(isinstance(subset, tuple) and len(subset) <= length, 'retained set must be a bounded tuple')
        for label in subset:
            integer(label, 0, n - 1, 'retained label')
        require(all(x < y for x, y in zip(subset, subset[1:])), 'retained labels must strictly increase')
    require(n == 0 or len(marked) <= n - 1, 'nonempty word requires an unmarked occurrence')
    require(len(lengths) <= len(marked) + 1, 'skeleton has too many runs')
    return n, marked, labels, lengths, retained


def _decode(encoding, pattern):
    n, marked, labels, lengths, retained = _validate_encoding(encoding, pattern)
    marked_values = dict(zip(marked, labels))
    r = len(marked)
    word = []
    seen = set()
    unfinished = set()
    closed = set()
    ascents = 0
    rows = []
    for length, subset in zip(lengths, retained):
        p = len(word)
        d = len(seen)
        q = p - d
        unseen = set(range(ascents + length + 1)) - seen
        require(seen.issubset(set(range(ascents + length + 1))), 'old labels outside run alphabet bound')
        require(len(unseen) <= q + length + 1, 'unseen candidate bound fails')
        require(len(unfinished) <= r - q, 'unfinished-label budget fails')
        candidates = unseen if pattern == 110 else unseen | unfinished
        require(len(candidates) <= r + length + 1, 'candidate union exceeds uniform run bound')
        require(set(subset).issubset(candidates), 'retained labels outside candidate set')
        expected_k = sum(i not in marked_values for i in range(p, p + length))
        require(len(subset) == expected_k, 'retained set size does not match unmarked positions')
        rows.append({'prefix_length': p, 'run_length': length, 'retained_size': expected_k,
                     'q': q, 'unfinished': tuple(sorted(unfinished)),
                     'unseen_size': len(unseen), 'candidate_size': len(candidates)})
        iterator = iter(subset)
        for position in range(p, p + length):
            is_marked = position in marked_values
            x = marked_values[position] if is_marked else next(iterator)
            if position == 0:
                require(x == 0, 'decoded word must start at zero')
            else:
                require(x <= ascents + 1, 'decoded word violates ascent-prefix bound')
                if position == p:
                    require(word[-1] >= x, 'run boundary must be a nonascent')
                else:
                    require(word[-1] < x, 'decoded run must strictly increase')
            if pattern == 110:
                require((x in seen) == is_marked, 'first/non-first status disagrees with skeleton')
            else:
                require(x not in closed, 'a label reappears after its designated last occurrence')
                if is_marked:
                    unfinished.add(x)
                else:
                    unfinished.discard(x)
                    closed.add(x)
            if word:
                ascents += word[-1] < x
            seen.add(x)
            word.append(x)
    decoded = tuple(word)
    require(len(decoded) == n and _marks(decoded, pattern) == marked, 'decoded occurrence statuses disagree')
    require(not unfinished, 'a marked non-last occurrence has no later last occurrence')
    require(is_ascent(decoded), 'decoded word is not an ascent sequence')
    require(literal_avoidance(decoded)[1 if pattern == 100 else 2], 'decoded word contains forbidden pattern')
    return decoded, rows


def decode_word(encoding, pattern):
    """Decode and reject invalid status, ordering, legality or candidate data."""
    return _decode(encoding, pattern)[0]


def vandermonde_bound(r, lengths, retained_sizes):
    """Return (product bound, Vandermonde bound, common finite bound)."""
    integer(r, 0, MAX_LENGTH - 1, 'repeated-occurrence count')
    require(isinstance(lengths, (tuple, list)) and len(lengths) <= MAX_LENGTH,
            'run lengths must be a bounded list or tuple')
    require(isinstance(retained_sizes, (tuple, list)) and len(retained_sizes) == len(lengths),
            'one retained size is required per run')
    for length in lengths:
        integer(length, 1, MAX_LENGTH, 'run length')
    n = sum(lengths)
    require(n <= MAX_LENGTH, 'total run length exceeds finite cutoff')
    for length, k in zip(lengths, retained_sizes):
        integer(k, 0, length, 'retained size')
    require(sum(retained_sizes) == n - r, 'retained sizes must sum to n-r')
    require(len(lengths) <= r + 1, 'too many runs for repeated-occurrence count')
    if n == 0:
        require(r == 0, 'empty word requires r=0')
        return 1, 1, 1
    require(r < n, 'repeated-occurrence count must be smaller than nonempty length')
    product_bound = prod(comb(r + length + 1, k) for length, k in zip(lengths, retained_sizes))
    middle = comb(n + len(lengths) * (r + 1), n - r)
    final = comb(n + (r + 1) ** 2, n - r)
    require(product_bound <= middle <= final, 'finite Vandermonde inequality fails')
    return product_bound, middle, final


def finite_upper_bound(n):
    """The exact finite upper bound 16^n sum_r binom(n+(r+1)^2,n-r)."""
    integer(n, 0, MAX_LENGTH, 'upper-bound length')
    return 1 if n == 0 else 16**n * sum(comb(n + (r + 1)**2, n - r) for r in range(n))


def verify(max_n=9):
    integer(max_n, 0, MAX_VERIFY_LENGTH, 'maximum raw verification length')
    rows = []
    total_words = 0
    total_runs = 0
    total_skeletons = 0
    digests = {100: hashlib.sha256(), 110: hashlib.sha256()}
    for n in range(max_n + 1):
        data = {pattern: {'encodings': set(), 'skeletons': Counter(), 'bounds': {},
                          'r_counts': Counter(), 'runs': 0} for pattern in (100, 110)}
        for word in raw_ascent_words(n):
            literal = literal_avoidance(word)
            for pattern, index in ((100, 1), (110, 2)):
                if not literal[index]:
                    continue
                encoding = encode_word(word, pattern)
                decoded, run_rows = _decode(encoding, pattern)
                require(decoded == word and decode_word(encoding, pattern) == word,
                        'run-set reconstruction fails')
                require(encoding not in data[pattern]['encodings'], 'encoding injection fails')
                data[pattern]['encodings'].add(encoding)
                n_enc, marked, labels, lengths, retained = encoding
                r = n - len(set(word))
                require(n_enc == n and len(marked) == r, 'encoded length or r mismatch')
                require(len(lengths) <= r + 1, 'run count exceeds r+1')
                if pattern == 100:
                    for run in run_rows:
                        p = run['prefix_length']
                        actual_unfinished = set(word[:p]) & set(word[p:])
                        require(actual_unfinished == set(run['unfinished']), 'unfinished set is not determined correctly')
                        require(len(actual_unfinished) <= r - (p - len(set(word[:p]))), 'independent unfinished budget fails')
                retained_sizes = tuple(map(len, retained))
                product_bound, middle, final = vandermonde_bound(r, lengths, retained_sizes)
                skeleton = encoding[:4]
                data[pattern]['skeletons'][skeleton] += 1
                data[pattern]['bounds'][skeleton] = product_bound
                data[pattern]['r_counts'][r] += 1
                data[pattern]['runs'] += len(run_rows)
                digests[pattern].update((repr(encoding) + '\n').encode('ascii'))
        for pattern in (100, 110):
            selected = data[pattern]
            for skeleton, completions in selected['skeletons'].items():
                require(completions <= selected['bounds'][skeleton], 'actual skeleton branching exceeds product bound')
            for r in range(n):
                skeleton_count = sum(len(key[1]) == r for key in selected['skeletons'])
                skeleton_bound = comb(n, r) * comb(n + r - 1, r) * 2**(n - 1)
                require(skeleton_count <= skeleton_bound <= 16**n, 'finite skeleton bound fails')
            count = len(selected['encodings'])
            require(count <= finite_upper_bound(n), 'finite total bound fails')
            total_words += count
            total_runs += selected['runs']
            total_skeletons += len(selected['skeletons'])
            rows.append({'n': n, 'pattern': str(pattern), 'encoded_words': count,
                         'distinct_skeletons': len(selected['skeletons']),
                         'runs_checked': selected['runs'],
                         'counts_by_r': {str(r): value for r, value in sorted(selected['r_counts'].items())},
                         'finite_upper_bound': finite_upper_bound(n)})
    return {'status': 'PASS', 'report_number': REPORT_NUMBER,
            'max_raw_length': max_n, 'cases': rows,
            'total_class_word_encodings': total_words,
            'total_run_candidate_checks': total_runs,
            'total_skeletons_checked': total_skeletons,
            'encoding_sha256': {str(pattern): digest.hexdigest() for pattern, digest in digests.items()},
            'scope': 'Exact finite skeleton/reconstruction, occurrence-status, candidate-set, branching and Vandermonde checks. Asymptotic optimization is proved in the article.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=9)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(verify(args.max_n), args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
