#!/usr/bin/env python3
"""Two fixed grammar prices and four local tagged-fold graphs; no broad search.

Uses the exact upstream compiler and local-fold checker copied beside this file.
Neither experiment certifies a new full machine or establishes a global bound.
"""
from pathlib import Path
from collections import defaultdict
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'construction/vendor'))
import compiler as c
import support as s

BOX = {0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}

def tagged_matching(table):
    states = {q for q, _ in table}
    incoming = defaultdict(set)
    for (q, bit), (write, right, nxt) in table.items():
        incoming[nxt].add(bit if right and write == bit else 2)
    left = sorted(q for q in states - BOX if incoming[q] == {0})
    right = sorted(q for q in states - BOX if incoming[q] == {1})
    providers = [defaultdict(list), defaultdict(list)]
    for helper in sorted(states):
        zero, one = table[helper, 0], table[helper, 1]
        if zero[0] != 0 or one[0] != 1 or not zero[1] or not one[1]:
            continue
        if zero[2] not in states or one[2] not in states:
            continue
        for bit in (0, 1):
            providers[bit][table[zero[2], bit], table[one[2], bit]].append((helper, zero[2], one[2]))
    adjacency = {}
    for a in left:
        for b in right:
            if all(table[a, bit] == table[b, bit] or any(
                not ({a, b} & set(provider))
                for provider in providers[bit][table[a, bit], table[b, bit]])
                for bit in (0, 1)):
                adjacency.setdefault(a, []).append(b)
    match = {}
    def augment(a, seen):
        for b in adjacency.get(a, []):
            if b in seen:
                continue
            seen.add(b)
            if b not in match or augment(match[b], seen):
                match[b] = a
                return True
        return False
    for a in left:
        augment(a, set())
    return len(match), sum(map(len, adjacency.values()))

def mp_screen():
    results = []
    for name in ('PA194H5X', 'PA194JH5X'):
        directory = ROOT / 'machines' / name
        raw = s.read_table(directory / 'raw.native.tm')
        folds = json.loads((directory / 'folds.json').read_text())
        assert len(raw) == 406 and len(folds) == 9
        for apply_mp in (False, True):
            table = raw.copy()
            if apply_mp:
                for key, target in (((100,0),213), ((100,1),174), ((174,0),28), ((174,1),164)):
                    write, direction, _ = table[key]
                    table[key] = write, direction, target
            folded, aliases = s.apply_folds(table, folds)
            cases = s.check_local_folds(table, folded, aliases, folds)
            maximum, edges = tagged_matching(table)
            assert maximum == 9 and len(cases['cases']) == 36
            results.append({'machine': name, 'mp_reassociation_applied': apply_mp,
                'raw_controls': 203, 'existing_folds': 9, 'simultaneous_local_cases': 36,
                'all_nonbox_tagged_matching_maximum': maximum, 'eligible_pairs': edges,
                'optimistic_minimum_states_in_this_matching_model': 203 - maximum})
    receipt = {'status': 'FINITE_LOCAL_CHECKS_ONLY', 'results': results,
        'scope': 'One unchanged allocation for each literal raw table, with and without the four-row MP rotation. No complete source/runtime/startup replay of either composite. No new consistency machine or lower bound outside this tagged-pair model is claimed.'}
    (ROOT / 'mp_composition_local_screen.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return receipt

def price_fixed_trees():
    base = s.read_table(ROOT / 'machines/PA194H5X/raw.native.tm')
    c.machine = lambda: (base, [])
    inc = ('leaf', 'inc', 1)
    c.MACROS[inc, inc] = 99
    c.MACROS[(inc, inc), (inc, inc)] = 190
    tree = c.read_grammar(ROOT / 'research/grammar/Bh5X_search.best.grammar.json')
    leaves = []
    def flatten(t):
        if c.isnode(t):
            flatten(t[0]); flatten(t[1])
        else:
            leaves.append(t)
    flatten(tree)
    assert len(leaves) == 189
    B = ['node58','node49',inc,'node65','node58','node55','node65',inc,inc,
         'node49',inc,'node65','node55','node65',inc,inc,'node65']
    R = ['node58','node58','node49',inc,'node65','node55','node65',inc,inc,
         'node49',inc,'node65','node55','node65',inc,inc,'node65']
    assert leaves[18:35] == B
    replacement = leaves.copy()
    replacement[18:35] = R
    iterator = iter(replacement)
    def replace(t):
        return (replace(t[0]), replace(t[1])) if c.isnode(t) else next(iterator)
    changed = replace(tree)
    # Check the changed complete head in free syntax, independent of prices.
    def implication(a, b): return ('I', a, b)
    def successor(a): return ('S', a)
    zero, H, D = ('zero',), ('H',), ('D',)
    one = successor(zero)
    def neg(a): return implication(a, one)
    def universal(d, a): return successor(successor(implication(a, d)))
    def execute(word):
        t, stack = ('originalT',), []
        for token in word:
            if token == 'node58': stack.append(t); t = H
            elif token == 'node55': stack.append(t); t = D
            elif token == 'node49': stack.append(t); t = zero
            elif token == inc: t = successor(t)
            elif token == 'node65': t = implication(stack.pop(), t)
            else: raise AssertionError(token)
        assert stack == [('originalT',)]
        return t
    assert execute(B) == implication(neg(H), universal(D, neg(universal(D, H))))
    assert execute(R) == implication(H, universal(D, neg(universal(D, neg(H)))))
    results = []
    for name, candidate in (('upstream_best_Bh5X_tree', tree), ('same_tree_with_Rh5X_head', changed)):
        rows, index, shape = c.build(candidate)
        possibilities = c.opportunities_fast(rows, shape)
        matching = c.max_matching(possibilities)
        results.append({'name': name, 'raw_fixed': 134, 'raw_readers': len(shape),
            'matching_upper_bound': len(matching), 'optimistic_effective_readers': len(shape)-len(matching),
            'optimistic_state_nomination': 134+len(shape)-len(matching), 'eligible_pairs': len(possibilities)})
    assert [x['optimistic_state_nomination'] for x in results] == [200, 205]
    receipt = {'status': 'COMPLETED_FINITE_PRICE', 'fresh_candidates_priced': 2,
        'baseline_reproduced': True, 'word_length': 189, 'free_term_head_binding': 'PASS',
        'changed_leaf_interval': [18,23], 'results': results,
        'scope': 'Two fixed-tree prices only. Matching gives an optimistic fold count; simultaneous folds, complete runtime, source compiler, and startup were not replayed. No new accepted machine is claimed.'}
    (ROOT / 'fixed_shape_Rh5X_price.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (ROOT / 'same_shape_Rh5X.tree.json').write_text(json.dumps(changed) + '\n')
    return receipt

if __name__ == '__main__':
    assert __debug__
    print(json.dumps({'fixed_prices': price_fixed_trees(), 'mp_local_screen': mp_screen()}, indent=2))
