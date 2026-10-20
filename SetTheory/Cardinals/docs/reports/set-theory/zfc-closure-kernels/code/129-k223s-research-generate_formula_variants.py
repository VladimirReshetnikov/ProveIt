#!/usr/bin/env python3
"""Generate fully specified K-schema arithmetic-emitter alternatives.

This is search input, not a correctness certificate for any machine. The seed
request theory is calibrated by the separate mathematical note. Bundle/conjunct
permutations and double-negation cancellation are classical equivalences.
"""
from pathlib import Path
from itertools import permutations, product
import argparse, json

ROOT = Path(__file__).resolve().parent


def I(x, y): return ('I', x, y)
def Q(x, y): return ('Q', x, y)
def R(x, y): return ('R', x, y)
def E(x, y): return ('E', x, y)
def N(x): return I(x, 1)
def A(x, y): return N(I(x, N(y)))
def X(x, y): return N(Q(x, N(y)))


def simplify(f):
    if not isinstance(f, tuple): return f
    op, x, y = f
    x, y = simplify(x), simplify(y)
    if op == 'I' and y == 1 and isinstance(x, tuple) and x[0] == 'I' and x[2] == 1:
        return simplify(x[1])
    return (op, x, y)


def emit(f):
    if not isinstance(f, tuple): return [{'a': 166, 'b': 121, 'c': 168, 1: 177}[f]]
    op, x, y = f
    if op == 'I' and y == 1:
        return emit(x) + [218]
    return emit(x) + emit(y) + [{'I': 119, 'R': 181, 'Q': 180, 'E': 182}[op]]


def expression(kind, swap_selected, swap_support, swap_root, ordering, helper,
               request_form='universal'):
    a, b, c = 'a', 'b', 'c'
    m, rel = c, R(b, c)
    subset = Q(c, I(R(c, a), R(c, b)))
    selected = A(rel, m) if swap_selected else A(m, rel)
    found = X(b, selected)
    if request_form == 'universal':
        request = Q(b, I(m, found))
    elif request_form == 'exists':
        request = I(X(b, m), found)
    elif request_form == 'contraposed':
        request = I(N(found), N(X(b, m)))
    else:
        raise ValueError('Unknown request form')
    closure = Q(a, I(subset, request))
    support = A(closure, m) if swap_support else A(m, closure)
    H = Q(b, I(rel, X(a, support)))
    rootpremise = {'output': I(m, rel), 'seedrequest': request, 'conditional': rel}[kind]
    rootand = A(H, rootpremise) if swap_root else A(rootpremise, H)
    core = X(c, rootand)
    if kind == 'conditional': core = I(m, core)
    kappa = {'I': I, 'R': R, 'Q': Q, 'E': E}[helper](a, b) if helper != 'c' else c
    rv = I(R(a, b), Q(c, R(a, b)))
    ev = I(E(a, b), Q(kappa, E(a, b)))
    parts = (core, rv, ev)
    return simplify(A(parts[ordering[0]], A(parts[ordering[1]], parts[ordering[2]])))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--emitter-contract', type=Path, required=True,
                        help='K224 portable/theory/emitter_contract.json')
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output_dir.exists() or not any(args.output_dir.iterdir()), 'Use an empty output directory'
    args.output_dir.mkdir(parents=True, exist_ok=True)
    variants = []
    for kind, ss, sp, sr, ordering, helper in product(
        ('output', 'seedrequest', 'conditional'), (False, True), (False, True),
        (False, True), permutations(range(3)), ('R', 'Q', 'E', 'I', 'c')
    ):
        expr = expression(kind, ss, sp, sr, ordering, helper)
        word = emit(expr)
        name = f'{kind}-s{int(ss)}-p{int(sp)}-r{int(sr)}-o{"".join(map(str,ordering))}-h{helper}'
        variants.append(dict(name=name, kind=kind, swap_selected=ss,
                             swap_support=sp, swap_root=sr, bundle_order=ordering,
                             helper=helper, expression=expr, word=word,
                             macro_count=len(word)))
    source = args.emitter_contract
    old = json.loads(source.read_text())
    plain = next(v for v in variants if v['name'] == 'output-s0-p0-r0-o012-hR')
    assert json.loads(json.dumps(plain['expression'])) == old['canonical_expression']
    assert plain['word'] == old['canonical_word']
    (args.output_dir / 'formula_variants.json').write_text(json.dumps(variants, separators=(',', ':')) + '\n')
    extra = []
    for v in variants:
        for form in ('exists', 'contraposed'):
            n = dict(v)
            expr = expression(v['kind'], v['swap_selected'], v['swap_support'],
                              v['swap_root'], v['bundle_order'], v['helper'], form)
            n.update(name=v['name'] + '-w' + form, request_form=form,
                     expression=expr, word=emit(expr), macro_count=len(emit(expr)))
            extra.append(n)
    (args.output_dir / 'formula_request_variants.json').write_text(json.dumps(extra, separators=(',', ':')) + '\n')
    print(json.dumps(dict(variants=len(variants), original_macro_count=plain['macro_count'],
                         output='formula_variants.json', request_variants=len(extra))))


if __name__ == '__main__':
    main()
