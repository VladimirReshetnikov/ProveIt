#!/usr/bin/env python3
"""Reproduce bounded logical-word searches for PA196 (Python standard library).

Usage:
  python3 logical_variant_search.py /path/to/BusyBeaver --out results
  python3 logical_variant_search.py /path/to/BusyBeaver --out results --greedy
  python3 logical_variant_search.py /path/to/BusyBeaver --out results --fusions

The pinned source is jamesyc/BusyBeaver@407cdc356f6b586635e71ac92be394255f4bfea4.
The reported costs are numbers of binary grammar rules, NOT TM state counts.
No table is emitted, and a search score does not certify a physical machine.
"""
import argparse
import collections
import hashlib
import itertools
import json
from pathlib import Path
import re
import time

UPSTREAM = '407cdc356f6b586635e71ac92be394255f4bfea4'
INC = ('leaf', 'inc', 1)
VARS = {'D': 'node55', 'H': 'node58', 'A': 'node70'}
ONE = '1'


def I(a, b): return (0, a, b)
def M(a, b, flip=False): return (1, b, a) if flip else (1, a, b)
def U(a, b): return (2, b, a)
def E(a, b, flip=False): return (3, b, a) if flip else (3, a, b)
def N(a): return I(a, ONE)
def conjunction(a, b): return N(I(a, N(b)))
def exists(a, b): return N(U(a, N(b)))


def emit(formula):
    if isinstance(formula, str):
        return ['node49', INC] if formula == ONE else [VARS[formula]]
    tag, a, b = formula
    return emit(a) + emit(b) + ['node65'] + [INC] * tag


def heads(flags=0, eqflip=False, memflip=False):
    d, h, a = 'DHA'
    eq = lambda x, y: E(x, y, eqflip)
    mem = lambda x, y: M(x, y, memflip)
    result = [
        I(exists(d, U(d, h)), h),
        I(U(d, U(a, h)), U(a, U(d, h))),
        I(mem(h, d), I(eq(h, a), mem(a, d))),
        I(eq(h, d), I(mem(a, h), mem(a, d))),
        exists(d, eq(h, d)),
        I(U(d, a), I(U(d, I(a, h)), U(d, h))),
    ]
    for bit, j in enumerate((2, 3, 5)):
        if (flags >> bit) & 1:
            _, x, (_, y, z) = result[j]
            result[j] = I(y, I(x, z))
    return result


def gate_parts(eqflip=False, memflip=False):
    a, b, c = 'HDA'
    eq = E(a, b, eqflip)
    mem = lambda x, y: M(x, y, memflip)
    delta = I(eq, U(c, eq))
    vacuity = I(mem(a, b), U(c, mem(a, b)))
    point = I(c, mem(c, b))
    separation = U(b, conjunction(I(mem(a, b), point), I(mem(c, b), c)))
    q = U(c, I(separation, N(point)))
    return delta, vacuity, q


def gate(swap=False, eqflip=False, memflip=False):
    delta, vacuity, q = gate_parts(eqflip, memflip)
    return N(I(vacuity, I(delta, q))) if swap else N(I(delta, I(vacuity, q)))


def read_source(source):
    text = (source / 'PA196/Program.lean').read_text()
    nodes = {}
    for line in text.splitlines():
        m = re.match(r'def (\w+) : Tree := \.node (.*)', line)
        if m is None:
            continue
        fields = re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b', m[2])
        children = [name if name else ('leaf', op, int(arg) if arg else None)
                    for op, arg, name in fields]
        assert len(children) == 2
        nodes[m[1]] = tuple(children)

    def body(t):
        if isinstance(t, str) and t.startswith('x'):
            return tuple(body(child) for child in nodes[t])
        return t

    def flatten(t):
        if isinstance(t, tuple) and len(t) == 2:
            return flatten(t[0]) + flatten(t[1])
        return [t]

    tree = body('x67')
    word = flatten(tree)
    assert len(word) == 201
    prefix, suffix = word[:18], word[-3:]
    assert prefix + sum(map(emit, heads()), []) + emit(gate()) + suffix == word
    return tree, word, prefix, suffix


def fixed_association_scorer(tree, alphabet, length):
    postorder = []
    cursor = 0

    def walk(t):
        nonlocal cursor
        if not (isinstance(t, tuple) and len(t) == 2):
            i = cursor
            cursor += 1
            return i
        a, b = map(walk, t)
        i = length + len(postorder)
        postorder.append((a, b))
        return i

    walk(tree)
    assert cursor == length

    def score(word):
        assert len(word) == length
        ids = [alphabet[t] for t in word]
        rules = {}
        for a, b in postorder:
            pair = (ids[a], ids[b])
            if pair not in rules:
                rules[pair] = len(alphabet) + len(rules)
            ids.append(rules[pair])
        return len(rules)

    return score


def greedy_score(word, alphabet):
    """Deterministic RePair upper bound; not a global grammar minimum."""
    seq = [alphabet[t] for t in word]
    rules = 0
    while len(seq) > 1:
        counts = collections.Counter(zip(seq, seq[1:]))
        pair = max(counts, key=counts.__getitem__)
        if counts[pair] < 2:
            return rules + len(seq) - 1
        new = len(alphabet) + rules
        rules += 1
        out, i = [], 0
        while i < len(seq):
            if i + 1 < len(seq) and (seq[i], seq[i + 1]) == pair:
                out.append(new)
                i += 2
            else:
                out.append(seq[i])
                i += 1
        seq = out
    return rules


def word_variants(prefix, suffix, memflip=False):
    for eqflip, swap, flags in itertools.product((False, True), (False, True), range(8)):
        hh = list(map(emit, heads(flags, eqflip, memflip)))
        gg = emit(gate(swap, eqflip, memflip))
        for order in itertools.permutations(range(6)):
            meta = dict(eqflip=eqflip, memflip=memflip, gate_swap=swap,
                        antecedent_flags=flags, head_order=order)
            yield meta, prefix + sum((hh[j] for j in order), []) + gg + suffix


FUSIONS = {'h5': ((4,), False), 'h1_explosion': ((0,), True),
           'both_explosion': ((0, 4), True)}


def fused_variants(prefix, suffix, profile):
    fused, explosion = FUSIONS[profile]
    for mf, ef, flags in itertools.product((False, True), (False, True), range(8)):
        hh = heads(flags, ef, mf)
        kept = [h for j, h in enumerate(hh) if j not in fused]
        if explosion:
            kept.insert(0, I(ONE, 'H'))
        delta, vacuity, q = gate_parts(ef, mf)
        terms = [hh[j] for j in fused] + [delta, vacuity]
        kept, terms, qword = list(map(emit, kept)), list(map(emit, terms)), emit(q)
        for ho in itertools.permutations(range(len(kept))):
            for go in itertools.permutations(range(len(terms))):
                word = (prefix + sum((kept[j] for j in ho), [])
                        + sum((terms[j] for j in go), []) + qword
                        + ['node65'] * len(terms) + ['node49', INC, 'node65'] + suffix)
                yield dict(profile=profile, memflip=mf, eqflip=ef, flags=flags,
                           head_order=ho, gate_order=go), word


def census(items, scorer):
    histogram, best, witness, count = collections.Counter(), None, None, 0
    for meta, word in items:
        value = scorer(word)
        histogram[value] += 1
        count += 1
        if best is None or value < best:
            best, witness = value, meta
    return dict(count=count, minimum=best, minimizing_count=histogram[best],
                witness=witness, histogram=dict(sorted(histogram.items())))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--out', type=Path, default=Path('logical_search_results'))
    parser.add_argument('--greedy', action='store_true')
    parser.add_argument('--fusions', action='store_true')
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    tree, word, prefix, suffix = read_source(args.source)
    alphabet = {t: i for i, t in enumerate(dict.fromkeys(word))}
    fixed = fixed_association_scorer(tree, alphabet, len(word))
    results = {'upstream_commit': UPSTREAM,
               'metric': 'Binary AX-body grammar rules; not TM working states.',
               'original_word_length': len(word),
               'original_fixed_grammar_rules': fixed(word),
               'word_sha256': hashlib.sha256(json.dumps(word).encode()).hexdigest()}
    started = time.monotonic()
    results['fixed_association'] = census(word_variants(prefix, suffix), fixed)
    print('Fixed association:', results['fixed_association']['count'],
          'variants; minimum', results['fixed_association']['minimum'], flush=True)
    if args.greedy:
        for mf in (False, True):
            results['greedy_memflip_' + str(mf)] = census(
                word_variants(prefix, suffix, mf), lambda w: greedy_score(w, alphabet))
    for profile in FUSIONS:
        meta, fused = next(fused_variants(prefix, suffix, profile))
        (args.out / (profile + '.word.json')).write_text(json.dumps(
            {'meta': meta, 'word': fused, 'token_count': len(fused),
             'stack_items': 9 - len(FUSIONS[profile][0]) + int(FUSIONS[profile][1])}, indent=2))
        if args.fusions:
            results['fusion_' + profile] = census(
                fused_variants(prefix, suffix, profile), lambda w: greedy_score(w, alphabet))
            print('Fusion', profile, results['fusion_' + profile]['count'],
                  'variants; greedy minimum', results['fusion_' + profile]['minimum'], flush=True)
    results['elapsed_seconds'] = time.monotonic() - started
    (args.out / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print('Wrote', args.out / 'results.json', flush=True)


if __name__ == '__main__':
    main()
