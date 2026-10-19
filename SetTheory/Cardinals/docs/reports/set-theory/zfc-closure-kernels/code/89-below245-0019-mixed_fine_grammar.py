#!/usr/bin/env python3
"""Joint exact fine-word segmentation and shared grammar optimization.

The 51 bootstrap/non-AX grammar states remain fixed.  Existing atom macros
and fixed grammar words are zero-cost dictionary entries.  New binary
productions are charged once per exact expanded fine word.  This is a
finite-universe search; solver infeasibility is not a machine lower bound.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import cache
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def run(args):
    started = time.monotonic()
    package = args.package
    source = json.loads((package / 'inputs/closed-sequence-grammar-next22.json').read_text())
    symbols = json.loads((package / 'inputs/semantic-symbols.json').read_text())
    seed = json.loads((package / 'grammar.json').read_text())
    grammar = {w: (l, r) for w, l, r in seed['rules']}
    ast = source['ast_dag']
    lines = (package / 'inputs/semantic.txt').read_text().splitlines()
    nr, nt, na = map(int, lines[0].split())
    old = {w: (w[:int(k)], w[int(k):]) for k, w, q in map(str.split, lines[1:nr + 1])}
    names = {int(q): w for k, w, q in map(str.split, lines[1:nr + 1])}
    allowed = {c: int(m) for c, m in map(str.split, lines[1 + nr + nt:])}
    by_ast = {int(i): names[int(q)] for q, i in source['sequence_ast_roots'].items()}

    @cache
    def bounds(i):
        row = ast[i]
        if row[0] == 'L':
            op, *xs = row[1]
            return ((1, 0) if op == 'dec' else (xs[0], 0) if op == 'brk'
                    else (0, xs[0]) if op == 'cont' else (0, 0))
        a, b = bounds(row[1]), bounds(row[2])
        return max(a[0] - 1, b[0], 0), max(a[1], b[1] - 1, 0)

    @cache
    def finest(i):
        row = ast[i]
        if row[0] == 'N' and bounds(row[1]) == bounds(row[2]) == (0, 0):
            return finest(row[1]) + finest(row[2])
        return (i,)

    fine_ids = sorted({i for name in symbols.values() for i in finest(source['atoms'][name]['ast'])})
    encode = {i: chr(65 + k) for k, i in enumerate(fine_ids)}
    atom = {c: ''.join(encode[i] for i in finest(source['atoms'][name]['ast']))
            for c, name in symbols.items()}

    def expand(w):
        return ''.join(atom[c] for c in w)

    def join(a, b):
        return a[0] + 1, max(a[0] + 1, a[1], b[1]), max(a[2], b[2]) + 1

    def properties(g, overrides=None):
        overrides = overrides or {}

        @cache
        def ap(i):
            if i in by_ast:
                w = by_ast[i]
                return wp(overrides.get(w, w))
            row = ast[i]
            return (0, 0, 0) if row[0] == 'L' else join(ap(row[1]), ap(row[2]))

        @cache
        def wp(w):
            if len(w) == 1:
                return ap(source['atoms'][symbols[w]]['ast'])
            return join(*(wp(x) for x in g.get(w, old.get(w))))

        return ap(source['original_ast']), wp

    roots = set(seed['roots']) | {r['word'] for r in seed['routes']}
    ax = names[76]
    assert ax == max(roots, key=len)
    locks = {line.split()[0] for line in
             (package / 'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()[1:]}
    fixed = set()

    def freeze(w):
        if len(w) == 1 or w in fixed:
            return
        fixed.add(w)
        for child in grammar[w]:
            freeze(child)

    for w in (roots - {ax}) | locks:
        freeze(w)
    assert len(fixed) == 51 and ax not in fixed
    baseline_props, wp = properties(grammar)
    dictionary = {}
    for c, f in atom.items():
        assert f not in dictionary
        dictionary[f] = (c, allowed[c], wp(c))
    for w in fixed:
        f = expand(w)
        assert f not in dictionary
        dictionary[f] = (w, 3, wp(w))
    modified = json.loads(args.modified_source.read_text()) if args.modified_source else None
    if modified and args.variant:
        variants = dict(modified.get('variants', {}))
        variants.update(modified.get('anchored_variants', {}))
        modified = variants[args.variant]
    desired_ax = modified.get('modified_AX_word', modified.get('raw_AX_word')) if modified else ax
    word = expand(desired_ax)
    # Every dictionary entry used inside AX is independent of the AX root.
    for f, (spelling, mask, prop) in dictionary.items():
        if f in word:
            assert prop[1] <= args.zero
    initial_private = {expand(w): (expand(l), expand(r)) for w, (l, r) in grammar.items() if w not in fixed}
    assert len(initial_private) == 77
    freq = Counter(word[i:i + n] for n in range(2, args.length + 1)
                   for i in range(len(word) - n + 1))
    vocabulary = set(dictionary) | set(initial_private) | {w for w, c in freq.items() if c >= 2}
    vocabulary.add(word)
    if modified:
        vocabulary.update(word[:i] for i in range(2, len(word)))
        vocabulary.update(word[i:] for i in range(1, len(word) - 1))
    if args.complements:
        for w in list(initial_private):
            vocabulary.update(w[:i] for i in range(2, len(w)))
            vocabulary.update(w[i:] for i in range(1, len(w) - 1))

    def free(w, bit):
        return w in dictionary and bool(dictionary[w][1] & (1 << bit))

    def can_be_grammar(w):
        return len(w) > 1 and not (w in dictionary and dictionary[w][1] == 3)

    choices = {w: [(w, w[:k], w[k:]) for k in range(1, len(w))
                   if w[:k] in vocabulary and w[k:] in vocabulary
                   and (free(w[:k], 0) or can_be_grammar(w[:k]))
                   and (free(w[k:], 1) or can_be_grammar(w[k:]))]
               for w in vocabulary if can_be_grammar(w)}
    while True:
        bad = {w for w, rows in choices.items() if not rows}
        if not bad:
            break
        for w in bad:
            del choices[w]
        for w in choices:
            choices[w] = [row for row in choices[w]
                          if all(free(v, bit) or v in choices for bit, v in enumerate(row[1:]))]
    assert word in choices
    words = sorted(choices, key=lambda w: (len(w), w))
    wi = {w: i for i, w in enumerate(words)}
    rules = [r for w in words for r in choices[w]]
    ri = {r: len(words) + i for i, r in enumerate(rules)}
    rank_offset = len(words) + len(rules)
    nvars = rank_offset + len(words)
    c = np.zeros(nvars)
    c[:len(words)] = 1
    low, high = np.zeros(nvars), np.ones(nvars)
    high[rank_offset:] = args.zero
    low[wi[word]] = 1
    high[rank_offset + wi[word]] = wp(ax)[0]
    integral = np.zeros(nvars)
    integral[:rank_offset] = 1
    rr, cc, vv, lb, ub = [], [], [], [], []

    def add(terms, lower, upper):
        index = len(lb)
        for j, value in terms:
            rr.append(index)
            cc.append(j)
            vv.append(value)
        lb.append(lower)
        ub.append(upper)

    for w in words:
        add([(wi[w], -1)] + [(ri[r], 1) for r in choices[w]], 0, 0)
    big = args.zero + 1
    for r in rules:
        w, a, b = r
        for bit, child in enumerate((a, b)):
            if not free(child, bit):
                add([(ri[r], 1), (wi[child], -1)], -np.inf, 0)
        terms = [(rank_offset + wi[w], 1), (ri[r], -big)]
        lower = 1 - big
        if free(a, 0):
            lower += dictionary[a][2][0]
        else:
            terms.append((rank_offset + wi[a], -1))
        add(terms, lower, np.inf)
    add([(wi[w], 1) for w in words], -np.inf, args.target - len(fixed))
    matrix = coo_matrix((vv, (rr, cc)), shape=(len(lb), nvars)).tocsc()
    setup = dict(fixed_states=len(fixed), zero_cost_dictionary=len(dictionary),
                 fine_alphabet=len(fine_ids), AX_fine_length=len(word),
                 words=len(words), productions=len(rules), variables=nvars,
                 constraints=len(lb), target_total_grammar=args.target,
                 complements=args.complements, max_substring_length=args.length,
                 modified_theory_source=bool(modified), variant=args.variant)
    print(json.dumps(dict(status='START', **setup)), flush=True)
    res = milp(c=c, integrality=integral, bounds=Bounds(low, high),
               constraints=LinearConstraint(matrix, np.array(lb), np.array(ub)),
               options={'time_limit': args.seconds, 'mip_rel_gap': 0})
    report = dict(setup, status=int(res.status), message=res.message,
                  elapsed_seconds=time.monotonic() - started,
                  scope='Explicit finite grammar universe, fixed 51-state core, fixed routes and bootstrap')
    for key in ('fun', 'mip_gap', 'mip_node_count', 'mip_dual_bound'):
        value = getattr(res, key, None)
        if value is not None:
            report[key] = float(value)
    if res.x is not None:
        selected = {w: (a, b) for w, a, b in rules if res.x[ri[w, a, b]] > .5}
        emitted = {w: grammar[w] for w in fixed}

        @cache
        def spell(w):
            a, b = selected[w]
            x = dictionary[a][0] if free(a, 0) else spell(a)
            y = dictionary[b][0] if free(b, 1) else spell(b)
            s = x + y
            assert expand(s) == w
            if s in emitted:
                assert emitted[s] == (x, y)
            emitted[s] = (x, y)
            return s

        new_ax = spell(word)
        new_props, new_wp = properties(emitted, {ax: new_ax})
        assert all(new_wp(spelling) == prop for f, (spelling, mask, prop) in dictionary.items()
                   if f in word)
        assert new_props[1] <= args.zero and new_props[2] <= 64
        out = dict(seed)
        out.update(rules_count=len(emitted), rules=[[w, *emitted[w]] for w in sorted(emitted)],
                   roots=sorted((set(seed['roots']) - {ax}) | {new_ax}),
                   properties=list(new_props), modified_AX_word=new_ax, original_AX_word=ax,
                   short_scan=True, framework_states=117,
                   search_method='joint-fine-segmentation-and-grammar')
        report.update(candidate_rules=len(emitted), new_AX_calls=len(new_ax), properties=new_props,
                      baseline_properties=baseline_props,
                      exact_fine_AX_equality=expand(new_ax) == expand(ax),
                      exact_desired_fine_AX_equality=expand(new_ax) == word)
        if modified:
            out['theory_transform'] = args.variant or 'converse-membership-in-CP-and-GIC'
            out['status'] = 'THEORY_VARIANT_ABSTRACT_GRAMMAR_ONLY'
        out['search_report'] = report
        args.output.write_text(json.dumps(out, indent=2) + '\n')
    args.output.with_suffix('.report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=180)
    parser.add_argument('--length', type=int, default=40)
    parser.add_argument('--target', type=int, default=127)
    parser.add_argument('--zero', type=int, default=6)
    parser.add_argument('--complements', action='store_true')
    parser.add_argument('--modified-source', type=Path)
    parser.add_argument('--variant', default='')
    run(parser.parse_args())
