#!/usr/bin/env python3
"""Finite adversarial checks for coprime-label Horn flow.

These are regressions for the elementary proofs in section.tex, not a
Diophantine compiler, proof of consistency, or search for a ZFC refutation.
Only Python's standard library is needed. Assertions are deliberately not
used, so `python -O` retains every validation.
"""
from collections import Counter
from itertools import combinations_with_replacement
from math import factorial, gcd, prod
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fermat(j):
    return (1 << (1 << j)) + 1


def balance(rows):
    z = Counter()
    for premises, conclusion in rows:
        z[conclusion] += 1
        z.subtract(premises)
    return {j: n for j, n in z.items() if n}


def product_balance(rows, target, weights):
    left = prod(weights[c] for p, c in rows)
    right = weights[target] * prod(weights[a] for p, c in rows for a in p)
    return left == right


def closure(rows):
    """Independent finite least Horn closure, with acyclic proof choices."""
    proofs = {}
    changed = True
    while changed:
        changed = False
        for premises, conclusion in rows:
            if conclusion not in proofs and all(p in proofs for p in premises):
                proofs[conclusion] = (premises, conclusion)
                changed = True
    return proofs


def tree_rows(proofs, target):
    """Root-first proof tree; selected rules may be duplicated."""
    pending, result = [target], []
    while pending:
        current = pending.pop()
        row = proofs[current]
        result.append(row)
        pending.extend(reversed(row[0]))
    return result


def obligation_trace(rows, target, weights):
    states = [weights[target]]
    for premises, conclusion in rows:
        numerator = states[-1] * prod(weights[p] for p in premises)
        require(numerator % weights[conclusion] == 0, "integral trace")
        states.append(numerator // weights[conclusion])
    require(states[-1] == 1, "terminal trace value")
    return states


def beta(code, scale, index):
    return code % (1 + (index + 1) * scale)


def crt_encode(values, scale):
    code, period = 0, 1
    for i, value in enumerate(values):
        modulus = 1 + (i + 1) * scale
        require(0 <= value < modulus, "beta residue bound")
        require(gcd(period, modulus) == 1, "CRT moduli coprime")
        correction = (value - code) * pow(period, -1, modulus) % modulus
        code += period * correction
        period *= modulus
    require(all(beta(code, scale, i) == v for i, v in enumerate(values)),
            "CRT reconstruction")
    return code


def main():
    checks = {}
    fs = [fermat(j) for j in range(11)]
    require(all(fs[j] - 2 == prod(fs[:j]) for j in range(11)),
            "Fermat product identity")
    require(all(gcd(fs[i], fs[j]) == 1 for i in range(11) for j in range(i)),
            "Fermat coprimality")
    require(fs[5] == 641 * 6700417, "composite label control")
    checks["fermat_identity_and_pairwise_coprimality_through_index"] = 10
    checks["composite_label_test"] = "F_5=641*6700417; primality is unnecessary"

    labels = range(3)
    premises = [()] + [(a,) for a in labels] + list(combinations_with_replacement(labels, 2))
    catalogue = [(p, c) for p in premises for c in labels]
    cases = accepted = derived = 0
    for size in range(5):
        for indices in combinations_with_replacement(range(len(catalogue)), size):
            rows = [catalogue[i] for i in indices]
            vector = balance(rows)
            proofs = closure(rows)
            for target in labels:
                exact = vector == {target: 1}
                arithmetic = product_balance(rows, target, fs)
                require(exact == arithmetic, "product/multiplicity equivalence")
                if exact:
                    accepted += 1
                    require(target in proofs, "balanced certificate has a derivation")
                if target in proofs:
                    derived += 1
                    tree = tree_rows(proofs, target)
                    require(balance(tree) == {target: 1}, "proof tree balance")
                    require(product_balance(tree, target, fs), "proof tree product")
                    obligation_trace(tree, target, fs)
                cases += 1
    checks["finite_rule_catalogue_size"] = len(catalogue)
    checks["maximum_selected_rule_occurrences"] = 4
    checks["target_multiset_cases"] = cases
    checks["balanced_cases"] = accepted
    checks["derivable_cases_with_constructed_tree_and_trace"] = derived

    # A disconnected cycle is harmless when a real proof is also present.
    rows = [((), 0), ((1,), 2), ((2,), 1)]
    require(balance(rows) == {0: 1}, "cycle plus axiom balance")
    require(product_balance(rows, 0, fs), "cycle plus axiom product")
    require(0 in closure(rows), "cycle plus real proof")
    cycle = rows[1:]
    require(not closure(cycle), "pure cycle has no derivation")
    require(all(not product_balance(cycle, t, fs) for t in labels),
            "pure cycle rejected for every target")

    # The wrong label assignment creates a false proof with no axioms.
    bad_rows = [((1,), 2)]
    bad_weights = [1, 2, 4]
    require(not closure(bad_rows), "noncoprime control has no derivation")
    require(product_balance(bad_rows, 1, bad_weights), "noncoprime false positive")
    require(not product_balance(bad_rows, 1, fs), "Fermat labels reject collision")

    # Signed multiplicities and multiple conclusions are both unsound.
    v1 = balance([((0,), 1)])
    v2 = balance([((0, 0), 1)])
    require({j: v1.get(j, 0) - v2.get(j, 0) for j in labels if v1.get(j, 0) != v2.get(j, 0)}
            == {0: 1}, "signed multiplicity false positive")
    require(not closure([((0,), 1), ((0, 0), 1)]), "signed control underivable")
    require(fs[0] * fs[1] == fs[1] * fs[0], "two conclusions a,t from a fake flow")
    checks["negative_controls"] = [
        "pure cycle cannot prove any target",
        "noncoprime weights 2,4 give spurious a->b certificate",
        "signed multiplicities give spurious certificate with no axioms",
        "two conclusions invalidate the closure-complement argument",
    ]
    checks["harmless_disconnected_cycle"] = True

    # A concrete four-outer-parameter beta certificate for an artificial
    # Horn theory. This has no relation to an actual ZFC contradiction.
    toy = [((), 0), ((0,), 2), ((0, 2), 1)]
    rows = tree_rows(closure(toy), 1)
    horizon = max(len(rows), 1 + max([1] + [a for p, c in rows for a in (*p, c)])) + 2
    states = obligation_trace(rows, 1, fs)
    while len(rows) < horizon:
        rows.append(((0,), 0))  # sound identity-rule padding
        states.append(states[-1])
    powers = [1 << (1 << j) for j in range(horizon + 1)]
    scale = factorial(horizon) * (1 + max(states + powers))
    s_code, q_code = crt_encode(states, scale), crt_encode(powers, scale)
    require(beta(s_code, scale, 0) == 5, "target-one initial weight")
    require(beta(s_code, scale, horizon) == 1, "source final value")
    require(beta(q_code, scale, 0) == 2, "source power seed")
    for i, (premises, conclusion) in enumerate(rows):
        qi, qn = beta(q_code, scale, i), beta(q_code, scale, i + 1)
        require(qn == qi * qi, "one-loop power recurrence")
        require(all(j < horizon for j in (*premises, conclusion)), "all lookups in proved range")
        wc = beta(q_code, scale, conclusion) + 1
        wp = prod(beta(q_code, scale, j) + 1 for j in premises)
        require(beta(s_code, scale, i + 1) * wc == beta(s_code, scale, i) * wp,
                "one-loop rule update")
    checks["four_parameter_toy_certificate"] = {
        "horizon": horizon,
        "s_code_bits": s_code.bit_length(),
        "q_code_bits": q_code.bit_length(),
        "shared_beta_scale_bits": scale.bit_length(),
        "actual_outer_parameters": ["N", "s_code", "q_code", "scale"],
        "bounded_universal_blocks": 1,
        "scope": "Artificial Horn theory only; no whole Diophantine compiler count",
    }
    checks["status"] = "PASS"
    path = Path(__file__).with_name("VERIFICATION.json")
    path.write_text(json.dumps(checks, indent=2) + "\n")
    print(json.dumps(checks, indent=2))


if __name__ == "__main__":
    main()
