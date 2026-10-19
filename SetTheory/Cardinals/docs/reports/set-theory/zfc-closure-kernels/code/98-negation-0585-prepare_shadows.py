#!/usr/bin/env python3
"""Price explicit grammar implementations of orientation-restricted atoms.

This is an exploratory source-grammar input generator, not a machine proof.
Each selected old physical word loses its zero-cost terminal status and gets
an ordinary paid binary implementation. The physical runtime is still fully
charged. A complete candidate needs an extended compiler and runtime proof.
"""
import argparse
import itertools
import json
from functools import lru_cache
from pathlib import Path


def parse_input(path):
    lines = path.read_text().splitlines()
    n, nr, na = map(int, lines[0].split())
    rules = {}
    labels = {}
    for line in lines[1:1+n]:
        k, w, q = line.split()
        k = int(k)
        rules[w] = (w[:k], w[k:])
        labels[w] = int(q)
    roots = lines[1+n:1+n+nr]
    atoms = {w: int(m) for w, m in map(str.split, lines[1+n+nr:])}
    assert len(atoms) == na
    return rules, labels, roots, atoms


def parse_resume(path):
    lines = path.read_text().splitlines()
    n = int(lines[0])
    rules = {}
    for row in lines[1:1+n]:
        k, w = row.split()
        k = int(k)
        rules[w] = (w[:k], w[k:])
    nr = int(lines[1+n])
    routes = lines[2+n:]
    assert len(routes) == nr
    return rules, routes


def seed_shadows(original, atoms, shadows):
    available = {w: m for w, m in atoms.items() if w not in shadows}
    rules = dict(original)

    def permitted(w, bit):
        return w not in available or available[w] & (1 << bit)

    for target in sorted(shadows, key=len):
        @lru_cache(None)
        def build(w):
            if w != target and (w in rules or w in available):
                return {}
            best = None
            for k in range(1, len(w)):
                a, b = w[:k], w[k:]
                if not permitted(a, 0) or not permitted(b, 1):
                    continue
                ra, rb = build(a), build(b)
                if ra is None or rb is None:
                    continue
                candidate = {**ra, **rb, w: (a, b)}
                # A shared semantic word has one fixed implementation.
                if any(x in ra and x in rb and ra[x] != rb[x] for x in ra):
                    continue
                key = (len(candidate), max(map(len, candidate), default=0), k)
                if best is None or key < best[0]:
                    best = (key, candidate)
            return None if best is None else best[1]
        added = build(target)
        if added is None:
            return None
        rules.update(added)
    for w, (a, b) in rules.items():
        assert w == a+b
        assert all(x in rules or x in available for x in (a, b))
        assert permitted(a, 0) and permitted(b, 1)
    return rules, available


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--inputs', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--pairs', action='store_true')
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    old, labels, roots, atoms = parse_input(args.inputs/'canonical-grammar.txt')
    rules, routes = parse_resume(args.inputs/'canonical-resume.txt')
    targets = sorted(w for w, m in atoms.items() if len(w)>1 and m!=3)
    choices = [(w,) for w in targets]
    if args.pairs:
        choices += list(itertools.combinations(targets, 2))
    records = []
    for i, shadows in enumerate(choices):
        built = seed_shadows(rules, atoms, shadows)
        if built is None:
            records.append(dict(index=i, shadows=shadows, status='UNPARSEABLE'))
            continue
        new, available = built
        d = args.output/f'shadow-{i:03d}'
        d.mkdir(exist_ok=True)
        grammar = [f'{len(new)} {len(roots)} {len(available)}']
        grammar += [f'{len(a)} {w} {labels.get(w, -1)}' for w,(a,b) in new.items()]
        grammar += roots
        grammar += [f'{w} {m}' for w,m in available.items()]
        (d/'grammar.txt').write_text('\n'.join(grammar)+'\n')
        resume = [str(len(new))] + [f'{len(a)} {w}' for w,(a,b) in new.items()]
        resume += [str(len(routes))] + routes
        (d/'resume.txt').write_text('\n'.join(resume)+'\n')
        records.append(dict(index=i, shadows=shadows, status='SEEDED',
                            grammar_rules=len(new), added_rules=len(new)-len(rules)))
    (args.output/'seeds.json').write_text(json.dumps(records, indent=2)+'\n')
    print(json.dumps(records, indent=2))


if __name__ == '__main__':
    main()
