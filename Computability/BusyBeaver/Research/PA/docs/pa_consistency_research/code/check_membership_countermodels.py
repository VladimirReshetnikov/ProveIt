#!/usr/bin/env python3
"""Finite witness checks for the mathematical counterinterpretations.

This checks the exact head-3/head-4 counterexamples, permutation laws,
and finite pointed-separation constructions.  Universal validity of
all source axioms is proved in membership_independence.tex, not inferred
from these samples.  This is not an end-to-end PA proof checker.
"""
import json
from itertools import product


def bit(a, b):
    return bool((a >> b) & 1)


def sigma(t):
    return {2: 3, 3: 2}.get(t, t)


def twist(label, t):
    return sigma(t) if label == 1 else t


def row_mem(a, b, env):
    return bit(twist(a, env[a]), env[b])


def col_mem(a, b, env):
    return bit(env[a], twist(b, env[b]))


def implies(a, b):
    return not a or b


def head3(mem, h, d, a, env):
    return implies(mem(h, d, env), implies(env[h] == env[a], mem(a, d, env)))


def head4(mem, h, d, a, env):
    return implies(env[h] == env[d], implies(mem(a, h, env), mem(a, d, env)))


def selected_witness(mode, a, b, c, env, predicate):
    """Construct witness for arbitrary externally supplied point property.

    The finite support is explicit, so predicate may be arbitrary, and
    its behavior away from the support is irrelevant to the witness.
    """
    assert c != a and c != b
    if a == b:
        support = {env[b]}
    elif mode == 'row':
        value = twist(a, env[a])
        support = {i for i in range(value.bit_length()) if bit(value, i)} | {env[b]}
    else:
        support = {twist(b, i) for i in range(env[a].bit_length()) if bit(env[a], i)} | {env[b]}
    selected = {y for y in support if predicate(y)}
    if mode == 'row':
        encoded = sum(1 << y for y in selected)
        return twist(c, encoded), selected
    return sum(1 << twist(b, y) for y in selected), selected


def check_gate_samples():
    cases = 0
    for mode, mem in [('row', row_mem), ('column', col_mem)]:
        for a, b, c in product(range(4), repeat=3):
            if c == a or c == b:
                continue
            for values in product(range(5), repeat=4):
                env = dict(enumerate(values))
                for predicate in [lambda y: True, lambda y: False,
                                  lambda y: y % 2 == 0, lambda y: y in (1, 4, 7),
                                  lambda y: y == values[b]]:
                    witness, selected = selected_witness(mode, a, b, c, env, predicate)
                    extended = dict(env, **{})
                    extended[c] = witness
                    assert implies(predicate(env[b]), mem(c, b, extended))
                    # The selected sets have no bits beyond 7 in these cases;
                    # 0..9 therefore exhausts all potentially true antecedents.
                    for y in range(10):
                        new = dict(extended)
                        new[b] = y
                        assert implies(mem(a, b, new), implies(predicate(y), mem(c, b, new)))
                        assert implies(mem(c, b, new), predicate(y))
                    cases += 1
    return cases


def main():
    for t in range(10000):
        assert sigma(sigma(t)) == t
        assert not bit(sigma(t), t)
        assert not bit(t, sigma(t))
    row_env = {0: 2, 1: 2, 2: 0}
    col_env = {0: 2, 1: 2, 2: 4}
    assert not head3(row_mem, 1, 2, 0, row_env)
    assert not head4(col_mem, 0, 1, 2, col_env)
    surviving_cases = 0
    for h, d, a in product(range(3), repeat=3):
        for values in product(range(8), repeat=3):
            env = dict(enumerate(values))
            assert head4(row_mem, h, d, a, env)
            assert head3(col_mem, h, d, a, env)
            surviving_cases += 2
    report = {
        'status': 'finite witness and construction checks passed',
        'universal_claim_basis': 'paper proof, not finite sampling',
        'row_twist_refutes_head3': {'h': 1, 'd': 2, 'a': 0, 'env': row_env},
        'column_twist_refutes_head4': {'h': 0, 'd': 1, 'a': 2, 'env': col_env},
        'surviving_head_instances_checked': surviving_cases,
        'pointed_separation_samples_checked': check_gate_samples(),
        'permutation_inputs_checked': 10000,
    }
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
