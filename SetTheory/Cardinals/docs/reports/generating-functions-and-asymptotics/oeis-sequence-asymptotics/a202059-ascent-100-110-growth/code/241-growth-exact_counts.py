#!/usr/bin/env python3
"""Bounded exact source recurrences and independent literal word enumeration.

The source recurrences are Conway et al. (2022), Sections 2.3 and 2.4.
The abstract reverses their pattern labels; this implementation follows the
actual equations. Empty words count once. All patterns are subsequences.
"""
from __future__ import annotations
import argparse
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
from common import ROOT, REPORT_NUMBER, emit, integer, new_file_path, require

MAX_STATES = 1_000_000
MAX_TRANSITIONS = 12_000_000
MAX_WORD_LENGTH = 100_000
MAX_LABEL = 100_000
MAX_RAW_LENGTH = 9
MAX_LITERAL_LENGTH = 80
MAX_RECURRENCE_LENGTH = 15
MAX_TRIPLE_LENGTH = 11


def checked_word(word, maximum=MAX_WORD_LENGTH):
    """Return a bounded tuple of nonnegative integer labels; reject bools."""
    integer(maximum, 0, MAX_WORD_LENGTH, 'word length bound')
    require(isinstance(word, (tuple, list)), 'word must be a tuple or list')
    require(len(word) <= maximum, 'word length exceeds finite cutoff')
    return tuple(integer(x, 0, MAX_LABEL, 'word label') for x in word)


def ascent_count(word):
    word = checked_word(word)
    return sum(x < y for x, y in zip(word, word[1:]))


def is_ascent(word):
    word = checked_word(word)
    if not word:
        return True
    if word[0] != 0:
        return False
    ascents = 0
    for index in range(1, len(word)):
        # The entering edge is deliberately counted only after the bound.
        if word[index] > ascents + 1:
            return False
        ascents += word[index - 1] < word[index]
    return True


def literal_avoidance(word):
    """Return (avoids 000, avoids 100, avoids 110), by all index triples."""
    word = checked_word(word, MAX_LITERAL_LENGTH)
    flags = [True, True, True]
    for i, j, k in combinations(range(len(word)), 3):
        x, y, z = word[i], word[j], word[k]
        if x == y == z:
            flags[0] = False
        if x > y == z:
            flags[1] = False
        if x == y > z:
            flags[2] = False
    return tuple(flags)


def fast_avoidance(word):
    """Linear detectors, independently cross-checked against literal triples."""
    word = checked_word(word)
    multiplicity = {}
    blocked = set()
    maximum = -1
    repeated_maximum = -1
    flags = [True, True, True]
    for x in word:
        count = multiplicity.get(x, 0)
        if count >= 2:
            flags[0] = False
        if x in blocked:
            flags[1] = False
        if x < repeated_maximum:
            flags[2] = False
        if x < maximum:
            blocked.add(x)
        if count:
            repeated_maximum = max(repeated_maximum, x)
        maximum = max(maximum, x)
        multiplicity[x] = count + 1
    return tuple(flags)


def raw_ascent_words(n):
    """Generate every ordinary ascent sequence at a small fixed length."""
    integer(n, 0, MAX_RAW_LENGTH, 'raw enumeration length')
    def visit(word, ascents):
        if len(word) == n:
            yield word
            return
        for x in range(ascents + 2):
            yield from visit(word + (x,), ascents + (word[-1] < x))
    return iter(((),)) if n == 0 else visit((0,), 0)


def recurrence_count(n, pattern):
    """Literal published recurrence with finite state and transition budgets."""
    integer(n, 0, MAX_RECURRENCE_LENGTH, 'recurrence length')
    integer(pattern, 100, 110, 'pattern')
    require(pattern in (100, 110), 'pattern must be 100 or 110')
    if n == 0:
        return 1
    states = 0
    transitions = 0
    def consume(a):
        nonlocal states, transitions
        states += 1
        transitions += max(a + 2, 0)
        require(states <= MAX_STATES, 'recurrence state budget exceeded')
        require(transitions <= MAX_TRANSITIONS, 'recurrence transition budget exceeded')
    @lru_cache(maxsize=None)
    def f100(remaining, a, last, maximum):
        consume(a if remaining else -2)
        if remaining == 0:
            return 1
        return sum(f100(remaining - 1, a + (x > last) - 1, x - 1, maximum - 1)
                   if x < maximum else f100(remaining - 1, a + (x > last), x, x)
                   for x in range(a + 2))
    @lru_cache(maxsize=None)
    def f110(remaining, a, last, used):
        consume(a if remaining else -2)
        if remaining == 0:
            return 1
        return sum(f110(remaining - 1, a + (x > last) - x, 0,
                        tuple(y - x for y in used if y >= x))
                   if x in used else f110(remaining - 1, a + (x > last), x,
                                          tuple(sorted(used + (x,))))
                   for x in range(a + 2))
    try:
        return f100(n - 1, 0, 0, 0) if pattern == 100 else f110(n - 1, 0, 0, (0,))
    finally:
        f100.cache_clear()
        f110.cache_clear()


def triple_class_prefix(n):
    """Independent extension recursion: test every earlier pair literally.

    No fast detector or source recurrence is used to prune this search.
    """
    integer(n, 0, MAX_TRIPLE_LENGTH, 'triple-class enumeration length')
    counts = [1] + [0] * n
    transitions = 0
    def visit(word, ascents):
        nonlocal transitions
        counts[len(word)] += 1
        if len(word) == n:
            return
        for z in range(ascents + 2):
            transitions += 1
            require(transitions <= 2_000_000, 'triple-class transition budget exceeded')
            allowed = True
            for i in range(len(word)):
                for j in range(i + 1, len(word)):
                    x, y = word[i], word[j]
                    if x == y == z or x > y == z or x == y > z:
                        allowed = False
                        break
                if not allowed:
                    break
            if allowed:
                visit(word + (z,), ascents + (word[-1] < z))
    if n:
        visit((0,), 0)
    return counts


def verify(raw_n=9, recurrence_n=15, triple_n=11):
    integer(raw_n, 0, MAX_RAW_LENGTH, 'raw enumeration length')
    integer(recurrence_n, 0, MAX_RECURRENCE_LENGTH, 'recurrence length')
    integer(triple_n, 0, MAX_TRIPLE_LENGTH, 'triple-class enumeration length')
    prefixes = json.loads((ROOT / 'code/source_prefixes.json').read_text(encoding='utf-8'))
    a100 = [recurrence_count(n, 100) for n in range(recurrence_n + 1)]
    a110 = [recurrence_count(n, 110) for n in range(recurrence_n + 1)]
    require(a100 == prefixes['A202059']['terms'][:recurrence_n + 1], '100 source prefix mismatch')
    require(a110 == prefixes['A202060']['terms'][:recurrence_n + 1], '110 source prefix mismatch')
    rows = []
    total = 0
    for n in range(raw_n + 1):
        counts = [0, 0, 0]
        count = 0
        for word in raw_ascent_words(n):
            literal = literal_avoidance(word)
            require(literal == fast_avoidance(word), 'literal/fast avoidance disagreement')
            require(is_ascent(word), 'raw enumeration produced an illegal ascent sequence')
            counts[0] += literal[1]
            counts[1] += literal[2]
            counts[2] += all(literal)
            count += 1
        require(counts[0] == prefixes['A202059']['terms'][n], 'raw 100 count mismatch')
        require(counts[1] == prefixes['A202060']['terms'][n], 'raw 110 count mismatch')
        require(counts[2] == prefixes['common_class']['terms'][n], 'raw common-class mismatch')
        total += count
        rows.append({'n': n, 'all_ascent_sequences': count, 'avoid_100': counts[0],
                     'avoid_110': counts[1], 'avoid_000_100_110': counts[2]})
    common = triple_class_prefix(triple_n)
    require(common == prefixes['common_class']['terms'][:triple_n + 1], 'published Class 36 mismatch')
    return {'status': 'PASS', 'report_number': REPORT_NUMBER,
            'source_recurrence_100': a100, 'source_recurrence_110': a110,
            'literal_raw_cross_checks': rows, 'raw_words_cross_checked': total,
            'literal_common_class_prefix': common,
            'scope': 'Finite exact verification; the asymptotic proof is in the article, not inferred from these terms.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--raw-n', type=int, default=9)
    parser.add_argument('--recurrence-n', type=int, default=15)
    parser.add_argument('--triple-n', type=int, default=11)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(verify(args.raw_n, args.recurrence_n, args.triple_n), args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
