#!/usr/bin/env python3
"""Exact finite doubled-seed construction avoiding 000, 100 and 110 together.

All unrestricted positions of each block are divided into consecutive chunks.
Each chunk increases; order between chunks is unrestricted. Labels after the
seed are fresh. No floating fit or numerical asymptotic claim occurs here.
"""
from __future__ import annotations
import argparse
import hashlib
from itertools import combinations, permutations, product
from math import factorial
from random import Random
from common import REPORT_NUMBER, emit, integer, new_file_path, require
from exact_counts import (MAX_LABEL, MAX_WORD_LENGTH, ascent_count, checked_word,
                          fast_avoidance, is_ascent, literal_avoidance)

MAX_M = 2000
MAX_B = 128
MAX_EXACT_M = 64
MAX_ENUM_M = 7
MAX_FAMILY = 25_000
MAX_ENUM_BLOCK = 8


def stage_sizes(m, b):
    integer(m, 1, MAX_M, 'seed size')
    integer(b, 2, MAX_B, 'chunk size')
    sizes = []
    k = m
    while k:
        sizes.append(k)
        k -= (k + b - 1) // b
    require(2 * m + sum(sizes) + len(sizes) <= MAX_WORD_LENGTH,
            'constructed length exceeds finite cutoff')
    return tuple(sizes)


def block_count(k, b):
    integer(k, 0, 128, 'block size')
    integer(b, 2, MAX_B, 'chunk size')
    q, r = divmod(k, b)
    return factorial(k) // (factorial(b) ** q * factorial(r))


def family_count(m, b):
    integer(m, 1, MAX_EXACT_M, 'exact seed size')
    integer(b, 2, MAX_B, 'chunk size')
    count = 1
    for k in stage_sizes(m, b):
        count *= block_count(k, b)
    return count


def specification(m, b):
    """Return deterministic (fresh alphabet, subsequent record) stage pairs."""
    sizes = stage_sizes(m, b)
    maximum = 2 * m - 1
    alphabet = tuple(range(m, 2 * m))
    stages = []
    for index, k in enumerate(sizes):
        following = sizes[index + 1] if index + 1 < len(sizes) else 0
        record = maximum + following + 1
        require(len(alphabet) == k, 'internal stage alphabet mismatch')
        stages.append((alphabet, record))
        alphabet = tuple(range(maximum + 1, record))
        maximum = record
    return tuple(stages)


def chunk_increasing(word, b):
    word = checked_word(word, 128)
    integer(b, 2, MAX_B, 'chunk size')
    return all(word[i] < word[i + 1] for start in range(0, len(word), b)
               for i in range(start, min(start + b, len(word)) - 1))


def chunk_permutations(alphabet, b):
    """Generate by ordered subset choices, not permutation filtering."""
    alphabet = checked_word(alphabet, MAX_ENUM_BLOCK)
    integer(b, 2, MAX_B, 'chunk size')
    require(len(set(alphabet)) == len(alphabet), 'alphabet labels must be distinct')
    alphabet = tuple(sorted(alphabet))
    def visit(remaining):
        if not remaining:
            yield ()
            return
        size = min(b, len(remaining))
        for chunk in combinations(remaining, size):
            chosen = set(chunk)
            rest = tuple(x for x in remaining if x not in chosen)
            for tail in visit(rest):
                yield chunk + tail
    return visit(alphabet)


def constructed_family(m, b):
    integer(m, 1, MAX_ENUM_M, 'enumerated seed size')
    integer(b, 2, MAX_B, 'chunk size')
    expected = family_count(m, b)
    require(expected <= MAX_FAMILY, 'family enumeration budget exceeded')
    stages = specification(m, b)
    choices = tuple(tuple(chunk_permutations(alphabet, b)) for alphabet, _ in stages)
    seed = tuple(range(m)) * 2
    def visit():
        for blocks in product(*choices):
            word = seed
            for block, (_, record) in zip(blocks, stages):
                word += block + (record,)
            yield word
    return visit()


def fresh_record_padding(word, extra):
    word = checked_word(word)
    integer(extra, 0, MAX_WORD_LENGTH, 'padding length')
    require(len(word) + extra <= MAX_WORD_LENGTH, 'padded word exceeds finite cutoff')
    require(is_ascent(word), 'padding input must be an ascent sequence')
    maximum = max(word, default=-1)
    require(maximum + extra <= MAX_LABEL, 'padded labels exceed finite cutoff')
    return word + tuple(range(maximum + 1, maximum + extra + 1))


def sampled_word(m, b, seed):
    integer(m, 1, MAX_M, 'seed size')
    integer(b, 2, MAX_B, 'chunk size')
    integer(seed, 0, 2**32 - 1, 'random seed')
    sizes = stage_sizes(m, b)
    rng = Random(seed)
    word = list(range(m)) * 2
    for alphabet, record in specification(m, b):
        block = list(alphabet)
        rng.shuffle(block)
        for start in range(0, len(block), b):
            block[start:start + b] = sorted(block[start:start + b])
        word.extend(block)
        word.append(record)
    require(len(word) == 2 * m + sum(sizes) + len(sizes), 'sample length mismatch')
    return tuple(word)


def _independent_legal(word):
    if word and word[0] != 0:
        return False
    return all(0 <= word[i] <= 1 + sum(word[j] < word[j + 1] for j in range(i - 1))
               for i in range(1, len(word)))


def _word_bytes(word):
    return (','.join(map(str, word)) + '\n').encode('ascii')


def verify(max_m=7):
    integer(max_m, 1, MAX_ENUM_M, 'maximum enumerated seed size')
    # An independent permutation filter validates every small block generator.
    block_cases = []
    for k in range(0, 8):
        for b in range(2, 9):
            alphabet = tuple(range(k))
            direct = {p for p in permutations(alphabet) if chunk_increasing(p, b)}
            chosen = list(chunk_permutations(alphabet, b))
            require(len(chosen) == len(set(chosen)), 'duplicate generated chunk permutation')
            require(set(chosen) == direct, 'chunk generators disagree')
            require(len(chosen) == block_count(k, b), 'chunk multinomial count mismatch')
            block_cases.append({'k': k, 'b': b, 'count': len(chosen)})
    cases = []
    word_count = 0
    padded_count = 0
    for b in range(2, 9):
        for m in range(1, max_m + 1):
            sizes = stage_sizes(m, b)
            stages = specification(m, b)
            words = list(constructed_family(m, b))
            expected = family_count(m, b)
            require(len(words) == len(set(words)) == expected, 'family cardinality/injection mismatch')
            length = 2 * m + sum(sizes) + len(sizes)
            checksum = hashlib.sha256()
            for word in words:
                require(len(word) == length, 'wrong constructed length')
                require(_independent_legal(word) and is_ascent(word), 'illegal constructed ascent sequence')
                require(literal_avoidance(word) == (True, True, True), 'literal constructed pattern occurrence')
                require(fast_avoidance(word) == (True, True, True), 'fast constructed pattern occurrence')
                require(word[-1] == max(word) <= ascent_count(word), 'terminal ascent/max invariant fails')
                position = 2 * m
                recovered = []
                for alphabet, record in stages:
                    block = word[position:position + len(alphabet)]
                    require(tuple(sorted(block)) == alphabet and chunk_increasing(block, b),
                            'fixed-position inverse failed')
                    require(word[position + len(alphabet)] == record, 'fixed-position record mismatch')
                    recovered.append(block)
                    position += len(alphabet) + 1
                require(position == length, 'inverse omitted a position')
                checksum.update(_word_bytes(word))
                for extra in (0, 1, 2, 7):
                    padded = fresh_record_padding(word, extra)
                    require(padded[:length] == word, 'padding lost original prefix')
                    require(_independent_legal(padded), 'independent padded ascent check failed')
                    require(literal_avoidance(padded) == (True, True, True), 'padded literal occurrence')
                    require(len(set(padded[length:])) == extra and
                            all(x > max(word) for x in padded[length:]), 'padding not fresh records')
                    padded_count += 1
            # Equal fixed-length prefixes make this an explicit injection check.
            padded_family = {fresh_record_padding(word, 7) for word in words}
            require(len(padded_family) == expected, 'padded family is not injective')
            word_count += len(words)
            cases.append({'m': m, 'b': b, 'stage_sizes': sizes, 'family_count': expected,
                          'length': length, 'ordered_word_sha256': checksum.hexdigest()})
    samples = []
    for m in (1, 2, 50, 100, 1000):
        for b in (2, 7, 20, 50):
            checksum = hashlib.sha256()
            for repetition in range(5):
                word = sampled_word(m, b, 241_000 + 100 * m + b + repetition)
                word = fresh_record_padding(word, 30)
                require(is_ascent(word) and all(fast_avoidance(word)), 'large deterministic sample failed')
                require(word[-1] == max(word) <= ascent_count(word), 'sample invariant failed')
                checksum.update(_word_bytes(word))
            samples.append({'m': m, 'b': b, 'samples': 5, 'padded_length': len(word),
                            'ordered_word_sha256': checksum.hexdigest()})
    for m in range(1, 65):
        for b in range(2, 129):
            sizes = stage_sizes(m, b)
            require(b * m - (b - 1) * len(sizes) <= sum(sizes) <= b * m,
                    'exact telescoping bound fails')
    require(fresh_record_padding((), 3) == (0, 1, 2), 'empty-word padding boundary')
    return {'status': 'PASS', 'report_number': REPORT_NUMBER,
            'block_cases': block_cases, 'construction_cases': cases,
            'constructed_words': word_count, 'padded_words_checked': padded_count,
            'deterministic_large_samples': samples,
            'exact_telescoping_parameter_pairs': 64 * 127,
            'scope': 'Bounded exact cardinality, injection, legality and avoidance checks. Seeded samples are finite tests, not an asymptotic proof.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-m', type=int, default=7)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(verify(args.max_m), args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
