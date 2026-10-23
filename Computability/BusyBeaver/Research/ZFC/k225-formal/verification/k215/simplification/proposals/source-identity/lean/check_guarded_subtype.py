#!/usr/bin/env python3
"""Owned finite regressions, not a proof or a Lean execution.

Transcribes the eight constructor semantics and the pinned WF guard as data.
Checks independent old translators against the new context-parametric one,
then compares ambient truth with truth in the finite subtype. The negative
tests deliberately break marker advancement, slot shifting, or native equality.
"""
import argparse
import itertools
import json
import random
from functools import lru_cache
from pathlib import Path

def M(i, j): return ('mem', i, j)
def E(i, j): return ('eq', i, j)
def A(p, q): return ('and', p, q)
def I(p, q): return ('imp', p, q)
def All(p): return ('all', p)
def Ex(p): return ('ex', p)
BOT = ('bot',)
def subset(i, j): return All(I(M(0, i + 1), M(0, j + 1)))
def transitive(i): return All(I(M(0, i + 1), subset(0, i + 1)))
def nonempty(i): return Ex(M(0, i + 1))
def minimal_element(m, s): return A(M(m, s), All(I(M(0, m + 1), I(M(0, s + 1), BOT))))
def minimal(i): return Ex(minimal_element(0, i + 1))
def well_founded(i): return All(I(subset(0, i + 1), I(nonempty(0), minimal(0))))
def tw(i): return A(transitive(i), well_founded(i))
def wf(i): return Ex(A(tw(0), M(i + 1, 0)))
WF_GUARD = wf(0)

def generic(phi, context, next_context, slot, guard, eq_mutant=False):
    op = phi[0]
    if op in ('mem', 'eq'):
        i, j = slot(context, phi[1]), slot(context, phi[2])
        if op == 'eq' and eq_mutant:
            p, q = M(0, i + 1), M(0, j + 1)
            return All(A(I(p, q), I(q, p)))
        return (op, i, j)
    if op == 'bot': return phi
    if op in ('all', 'ex'):
        body = generic(phi[1], next_context(context), next_context, slot, guard, eq_mutant)
        return (op, (('imp' if op == 'all' else 'and'), guard(context), body))
    return (op, *(generic(p, context, next_context, slot, guard, eq_mutant) for p in phi[1:]))

def old_tag(phi, d):
    op = phi[0]
    if op in ('mem', 'eq'):
        return (op, *(i if i < d else i + 1 for i in phi[1:]))
    if op == 'bot': return phi
    if op == 'all': return All(I(M(d + 1, 0), old_tag(phi[1], d + 1)))
    if op == 'ex': return Ex(A(M(d + 1, 0), old_tag(phi[1], d + 1)))
    return (op, *(old_tag(p, d) for p in phi[1:]))

def old_wf(phi):
    op = phi[0]
    if op in ('mem', 'eq', 'bot'): return phi
    if op == 'all': return All(I(WF_GUARD, old_wf(phi[1])))
    if op == 'ex': return Ex(A(WF_GUARD, old_wf(phi[1])))
    return (op, *(old_wf(p) for p in phi[1:]))

def tag(phi, mutant=None):
    return generic(phi, 0, lambda d: d + 1,
        (lambda d, i: i) if mutant == 'unshifted_slots' else lambda d, i: i if i < d else i + 1,
        (lambda d: M(1, 0)) if mutant == 'frozen_marker' else lambda d: M(d + 1, 0),
        eq_mutant=mutant == 'profile_equality')

def raw_wf_pred(n, mem, x):
    def is_tw(t):
        if not all(not (mem[y][t] and mem[z][y]) or mem[z][t]
                   for y in range(n) for z in range(n)):
            return False
        for s in range(n):
            elems = [m for m in range(n) if mem[m][s]]
            if all(not mem[z][s] or mem[z][t] for z in range(n)) and elems:
                if not any(all(not (mem[z][m] and mem[z][s]) for z in range(n)) for m in elems):
                    return False
        return True
    return any(is_tw(t) and mem[x][t] for t in range(n))

def make_sat(mem):
    @lru_cache(maxsize=100000)
    def sat(phi, env, domain):
        op = phi[0]
        if op == 'mem': return mem[env[phi[1]]][env[phi[2]]]
        if op == 'eq': return env[phi[1]] == env[phi[2]]
        if op == 'bot': return False
        if op == 'imp': return not sat(phi[1], env, domain) or sat(phi[2], env, domain)
        if op == 'and': return sat(phi[1], env, domain) and sat(phi[2], env, domain)
        if op == 'or': return sat(phi[1], env, domain) or sat(phi[2], env, domain)
        if op == 'all': return all(sat(phi[1], (x,) + env, domain) for x in domain)
        if op == 'ex': return any(sat(phi[1], (x,) + env, domain) for x in domain)
        raise AssertionError(op)
    return sat

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path)
    args = ap.parse_args()
    rng = random.Random(21518)
    atoms = [BOT] + [make(i, j) for make in (M, E) for i in range(4) for j in range(4)]
    def random_formula(depth):
        if depth == 0 or rng.randrange(4) == 0: return rng.choice(atoms)
        op = rng.choice(['imp', 'and', 'or', 'all', 'ex'])
        return (op, random_formula(depth - 1)) if op in ('all', 'ex') else (
            op, random_formula(depth - 1), random_formula(depth - 1))
    formulas = atoms + [make(a) for make in (All, Ex) for a in atoms]
    formulas += [random_formula(4) for _ in range(60)]
    formulas += [All(Ex(M(0, 2))), Ex(All(E(0, 2))), All(All(I(M(0, 2), M(1, 3))))]
    syntax_checks = 0
    for phi in formulas:
        for d in range(5):
            assert old_tag(phi, d) == generic(phi, d, lambda k: k + 1,
                lambda k, i: i if i < k else i + 1, lambda k: M(k + 1, 0))
            syntax_checks += 1
        assert old_wf(phi) == generic(phi, None, lambda c: c, lambda c, i: i, lambda c: WF_GUARD)
        syntax_checks += 1
    models = [(2, mask) for mask in range(16)] + [(3, mask) for mask in
        sorted(set([0, 511, 1, 3, 7, 73, 146, 292] + [rng.randrange(512) for _ in range(12)]))]
    checks = {'tagged': 0, 'wf': 0, 'guard_definition': 0}
    skipped_empty = {'tagged': 0, 'wf': 0}
    mutations = {}
    for n, mask in models:
        mem = tuple(tuple(bool(mask & (1 << (x * n + y))) for y in range(n)) for x in range(n))
        sat = make_sat(mem)
        ambient = tuple(range(n))
        for marker in range(n):
            domain = tuple(x for x in ambient if mem[marker][x])
            if not domain:
                skipped_empty['tagged'] += 1
                continue
            for env in itertools.product(domain, repeat=4):
                raw = (marker,) + env
                for phi in formulas:
                    expected = sat(phi, env, domain)
                    assert sat(tag(phi), raw, ambient) == expected
                    checks['tagged'] += 1
                    for mutant in ('frozen_marker', 'unshifted_slots', 'profile_equality'):
                        if mutant not in mutations and sat(tag(phi, mutant), raw, ambient) != expected:
                            mutations[mutant] = {'n': n, 'mask': mask, 'marker': marker,
                                'environment': env, 'formula': phi, 'expected': expected,
                                'mutant': sat(tag(phi, mutant), raw, ambient)}
        domain = tuple(x for x in ambient if raw_wf_pred(n, mem, x))
        for x in ambient:
            assert sat(WF_GUARD, (x,) + (0,) * 4, ambient) == (x in domain)
            checks['guard_definition'] += 1
        if not domain:
            skipped_empty['wf'] += 1
            continue
        for env in itertools.product(domain, repeat=4):
            for phi in formulas:
                assert sat(old_wf(phi), env, ambient) == sat(phi, env, domain)
                checks['wf'] += 1
    assert len(mutations) == 3, mutations
    result = {'validation': 'finite source-syntax and semantic regressions only; not a quantified proof',
        'seed': 21518, 'formula_count': len(formulas), 'models': models,
        'syntax_equalities_checked': syntax_checks, 'semantic_checks': checks,
        'empty_subtypes_with_no_valuation_skipped': skipped_empty,
        'negative_capture_and_equality_checks': mutations,
        'Lean_executed': False, 'upstream_code_executed': False}
    text = json.dumps(result, indent=2) + '\n'
    if args.out: args.out.write_text(text)
    else: print(text)

if __name__ == '__main__':
    main()
