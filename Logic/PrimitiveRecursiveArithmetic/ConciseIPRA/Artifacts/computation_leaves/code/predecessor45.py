"""Expanded raw trees for the 45-node scalar predecessor: composition of two incoming reductions.

This is an untrusted arithmetic research utility, not a proof checker.
Its finite examples are separate from the accompanying equational proof.
Only zero, successor and a scalar iterator are primitive. Every macro is
expanded, and repeated subtrees count at every occurrence (no DAG sharing).
"""
from functools import lru_cache
from itertools import count
from pathlib import Path
import json

serial = count()
ZERO = ('zero',)

def var(name):
    return ('var', name)

def suc(t):
    return ('suc', t)

def it(counter, seed, body):
    name = 'bound_' + str(next(serial))
    return ('it', counter, seed, name, body(var(name)))

def select(control, first, second):
    return it(control, first, lambda _: second)

def add(a, b):
    return it(b, a, suc)

def zero_test(n):
    return select(n, suc(ZERO), ZERO)

def parity(n):
    return it(n, ZERO, zero_test)

def clock_update(v):
    return it(suc(v), v, lambda w: select(w, suc(v), ZERO))

def clock(n):
    return it(n, ZERO, clock_update)

def ramp(n):
    return it(n, ZERO, lambda u: suc(select(clock(u), u, suc(u))))

def factor(n):
    return it(n, n, lambda v: select(v, ramp(n), ZERO))

def power_two(n):
    return it(n, suc(ZERO), lambda u: add(u, u))

def predecessor(n):
    return it(n, ZERO, lambda u:
              select(it(n, power_two(suc(u)), factor), suc(u), u))

def weighted_alternation(n, a):
    return it(n, ZERO, lambda v: select(v, a, ZERO))

def seeded_alternation(n, a):
    return it(n, n, lambda v: select(v, a, ZERO))

def nodes(t):
    if t[0] in ('zero', 'var'):
        return 1
    if t[0] == 'suc':
        return 1 + nodes(t[1])
    return 1 + nodes(t[1]) + nodes(t[2]) + nodes(t[4])

@lru_cache(None)
def free_vars(t):
    if t[0] == 'zero':
        return frozenset()
    if t[0] == 'var':
        return frozenset((t[1],))
    if t[0] == 'suc':
        return free_vars(t[1])
    return free_vars(t[1]) | free_vars(t[2]) | (free_vars(t[4]) - {t[3]})

def evaluate(t, env):
    return evaluate_cached(t, tuple(sorted((v, env[v]) for v in free_vars(t))))

@lru_cache(None)
def evaluate_cached(t, assignment):
    env = dict(assignment)
    if t[0] == 'zero':
        return 0
    if t[0] == 'var':
        return env[t[1]]
    if t[0] == 'suc':
        return evaluate(t[1], env) + 1
    _, counter, seed, bound, body = t
    limit = evaluate(counter, env)
    value = evaluate(seed, env)
    for _ in range(limit):
        env[bound] = value
        value = evaluate(body, env)
    return value

def substitute(tree, name, term):
    if tree[0] == 'zero':
        return tree
    if tree[0] == 'var':
        return term if tree[1] == name else tree
    if tree[0] == 'suc':
        return suc(substitute(tree[1], name, term))
    if tree[0] == 'eq':
        return ('eq', substitute(tree[1], name, term),
                substitute(tree[2], name, term))
    if tree[0] == 'D':
        return tree if name in tree[1:3] else (
            'D', tree[1], tree[2], substitute(tree[3], name, term))
    return ('it', substitute(tree[1], name, term),
            substitute(tree[2], name, term), tree[3],
            tree[4] if tree[3] == name else substitute(tree[4], name, term))

def gate(control, formula):
    if formula[0] == 'eq':
        return ('eq', select(control, ZERO, formula[1]),
                select(control, ZERO, formula[2]))
    return ('D', formula[1], formula[2], gate(control, formula[3]))

def formula_nodes(formula):
    if formula[0] == 'eq':
        return 1 + nodes(formula[1]) + nodes(formula[2])
    return 1 + formula_nodes(formula[3])

def universal_prefix_example(length):
    term = ZERO
    for j in reversed(range(length)):
        term = add(term, var('x_' + str(j)))
    formula = ('eq', term, suc(ZERO))
    for j in reversed(range(length)):
        witness, counter = 'alias_' + str(next(serial)), 'counter_' + str(next(serial))
        formula = ('D', witness, counter,
                   gate(var(counter), substitute(formula, 'x_' + str(j),
                                                  predecessor(var(counter)))))
    return formula

def main():
    n, a = var('n'), var('a')
    terms = dict(update=clock_update(n), clock=clock(n), ramp=ramp(n),
                 factor=factor(n), power_two=power_two(n),
                 predecessor=predecessor(n))
    sizes = {name: nodes(t) for name, t in terms.items()}
    assert sizes == dict(update=9, clock=12, ramp=20, factor=26,
                         power_two=9, predecessor=45)
    assert all(free_vars(t) == {'n'} for t in terms.values())

    # Directly evaluate the complete expanded trees, including each iterator.
    values = {name: [evaluate(t, {'n': k}) for k in
                    range(8 if name == 'predecessor' else 10 if name == 'power_two' else 30)]
              for name, t in terms.items()}
    assert values['update'][:3] == [1, 2, 0]
    assert values['clock'] == [k % 3 for k in range(30)]
    assert values['ramp'] == [3 * k // 2 for k in range(30)]
    assert values['factor'] == [0 if k % 2 else 3 * k // 2 for k in range(30)]
    assert values['power_two'] == [2 ** k for k in range(10)]
    assert values['predecessor'] == [0, 0, 1, 2, 3, 4, 5, 6]

    w = weighted_alternation(n, a)
    h = seeded_alternation(n, a)
    count_examples = 0
    for k in range(21):
        for payload in range(21):
            expected_w = payload if k % 2 else 0
            # H(k,a) agrees with the even selector at k>0; at k=0
            # it is always zero, hence fusion requires A(0)=0.
            expected_h = payload if k > 0 and k % 2 == 0 else 0
            env = {'n': k, 'a': payload}
            assert evaluate(w, env) == expected_w
            assert evaluate(h, env) == expected_h
            count_examples += 2

    prefix_nodes = []
    for length in (1, 2, 4, 8, 16):
        size = formula_nodes(universal_prefix_example(length))
        assert size == 55 * length + 4
        prefix_nodes.append({'variables': length, 'nodes': size})

    report = {
        'status': 'all expanded-tree counts and finite examples passed',
        'proof_status': 'written equational proof; not a Lean/Rocq verification',
        'metric': 'fully expanded raw 0/S/I constructor nodes, no sharing',
        'nodes': sizes,
        'raw_tree_values': values,
        'alternation_examples': count_examples,
        'expanded_universal_prefix_examples': prefix_nodes,
        'free_variables': sorted(free_vars(terms['predecessor'])),
        'saving_against_incoming46': {'nodes': 1, 'percent': 100 / 46},
        'provenance': '26-node factor from fused_iteration, reversed comparison from refinement',
        'expanded_predecessor_ast': terms['predecessor'],
    }
    destination = Path(__file__).resolve().parents[1] / 'evidence' / 'predecessor45_results.json'
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items()
                      if key != 'expanded_predecessor_ast'}, indent=2))

if __name__ == '__main__':
    main()
