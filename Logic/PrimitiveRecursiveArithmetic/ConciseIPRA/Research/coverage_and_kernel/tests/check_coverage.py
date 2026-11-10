#!/usr/bin/env python3
"""Finite diagnostics for coverage_without_cancellation.tex.

The theorem is proved syntactically in the accompanying text.  These checks
evaluate its source macros on ordinary natural numbers and exercise targeted
incorrect variants.  The final branch-merge example concerns cancellation of
an abstract successor only; it is NOT a countermodel of the full F/EI theory.
"""

import json


def epsilon(a, b):
    return int(a == b)


def F(n, h):
    value = h(0) + 1
    for _ in range(n):
        value = h(value)
    return value


def D(c, a):
    return F(c, lambda _: a)


def not_b(b):
    return epsilon(b, 0)


def and_b(b, c):
    return epsilon(D(b, epsilon(c, 0)), 0)


def or_b(b, c):
    return not_b(and_b(not_b(b), not_b(c)))


def H(a, v):
    return D(or_b(epsilon(v, 0), epsilon(v + 1, a)), v)


def U(j, a):
    return F(j, lambda v: H(a, v))


def pstar(a):
    return U(a, a)


def predecessor(a):
    return 0 if a in (0, 1) else pstar(a)


def unprotected(j, a):
    return F(j, lambda v: D(epsilon(v + 1, a), v))


def unstopped(j, a):
    del a
    return F(j, lambda v: D(epsilon(v, 0), v))


def prefix_update(k, v):
    """The source term h_k built by fixed Boolean-controlled increments.

    k indexes an external finite syntax construction; no variable-k primitive
    recursion or arithmetic order is being postulated in the weak theory.
    """
    value = 0
    for r in range(1, k + 1):
        bad = 0
        for i in range(1, min(r, k - 1) + 1):
            bad = or_b(bad, epsilon(v, i))
        if r == k:
            bad = or_b(bad, epsilon(v, k + 1))
        b_r = not_b(bad)
        value = D(not_b(b_r), value)
    return value


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def branch_successor(value):
    """N plus Z x N; a nonstandard tag loses its low binary bit."""
    if value[0] == "N":
        return ("N", value[1] + 1)
    return ("Z", value[1] + 1, value[2] // 2)


def branch_right_inverse(value):
    if value[0] == "N":
        return ("N", max(0, value[1] - 1))
    return ("Z", value[1] - 1, 2 * value[2])


def main():
    counts = {}

    for b in range(2):
        for c in range(2):
            require(and_b(b, c) == int(bool(b and c)), "Boolean AND")
            require(or_b(b, c) == int(bool(b or c)), "Boolean OR")
    counts["boolean_pairs"] = 4

    # Test the actual staged macros, including their tied initial seed.
    for a in range(19):
        require(H(a, 0) == 0 and U(0, a) == 1, "protected seed")
        for j in range(19):
            value = U(j, a)
            require(value != 0, "nonzero orbit")
            require(value == j + 1 or value + 1 == a, "protected orbit")
            require(U(j + 1, a) == H(a, value), "F successor equation")
            if value + 1 == a:
                require(U(j + 2, a) == value, "two-step persistence")
    counts["orbit_parameter_pairs"] = 361

    for m in range(19):
        require(pstar(m + 2) + 1 == m + 2, "right inverse on S squared")
    counts["right_inverse_inputs"] = 19

    for n in range(21):
        require(n == 0 or n == 1 or pstar(n) + 1 == n, "coverage invariant")
        require(predecessor(n + 1) == n, "corrected predecessor successor")
    require(predecessor(0) == 0, "corrected predecessor zero")
    counts["coverage_and_predecessor_inputs"] = 21

    # The direct no-fixed-point update, and the transient marker for numeral 1.
    for v in range(21):
        require(epsilon(v, 0) != v, "Boolean toggler has no fixed point")
    marker_update = lambda v: not_b(epsilon(v, 2))
    for n in range(21):
        require((F(n, marker_update) == 2) == (n == 0), "unique initial marker")
    require(F(1, marker_update) == 0, "marker at successor zero")
    counts["fixed_point_and_first_marker_inputs"] = 21

    # Finite-prefix metatheorem: build each fixed h_k from the actual source
    # Boolean gates, then compare with its independently specified finite map.
    prefix_cases = 0
    for k in range(1, 7):
        update = lambda v, k=k: prefix_update(k, v)
        markers = [k + 1] + list(range(k - 1, -1, -1))
        for v in range(k + 7):
            expected = v - 1 if 1 <= v <= k - 1 else k - 1 if v == k + 1 else k
            require(update(v) == expected, "finite-map source implementation")
            require(update(v) != markers[0], "initial marker has no incoming edge")
            for j in range(1, k + 1):
                require((update(v) == markers[j]) == (v == markers[j - 1]),
                        "unique incoming marker edge")
            prefix_cases += 1
        for n in range(k + 7):
            for j in range(k):
                require((F(n, update) == markers[j]) == (n == j),
                        "finite-prefix marker recognition")
        require(F(k, update) == 0, "last transient marker")
        require(F(k + 1, update) == k, "absorbing value after the prefix")
    counts["fixed_prefix_indices"] = 6
    counts["finite_map_value_cases"] = prefix_cases

    # Targeted controls: each mutates one substantive part of the construction.
    controls = {
        "deleted_zero_protection": {
            "input": 2,
            "computed_S_pstar_SS0": unprotected(2, 2) + 1,
            "required_SS0": 2,
        },
        "deleted_stop_test": {
            "input": 2,
            "computed_S_pstar_SS0": unstopped(2, 2) + 1,
            "required_SS0": 2,
        },
        "deleted_exception_at_zero": {
            "computed_pstar_zero": pstar(0),
            "required_predecessor_zero": 0,
        },
        "deleted_exception_at_one": {
            "computed_pstar_one": pstar(1),
            "required_predecessor_one": 0,
        },
        "wrong_boolean_fixed_point_update": {
            "update": "epsilon(v,1)",
            "fixed_point_witness": 0,
            "computed_at_witness": epsilon(0, 1),
        },
        "deleted_marker_negation": {
            "computed_F_zero": F(0, lambda v: epsilon(v, 2)),
            "required_initial_marker": 2,
        },
    }
    require(unprotected(2, 2) + 1 != 2, "zero-protection control was not detected")
    require(unstopped(2, 2) + 1 != 2, "stop-test control was not detected")
    require(pstar(0) != 0, "zero-exception control was not detected")
    require(pstar(1) != 0, "one-exception control was not detected")
    require(epsilon(0, 1) == 0, "wrong fixed-point update control was not detected")
    require(F(0, lambda v: epsilon(v, 2)) != 2, "marker-negation control was not detected")
    bad_prefix = lambda v: 3 if v == 4 else prefix_update(3, v)
    require(F(1, bad_prefix) != 2, "corrupt marker edge was not detected")
    controls["corrupted_first_prefix_edge"] = {
        "fixed_index": 3,
        "computed_F_one": F(1, bad_prefix),
        "required_first_marker": 2,
    }

    # A separate structural control shows why one must not cancel S in (R).
    # It is deliberately not represented as a model of all arithmetic axioms.
    m = ("Z", 0, 2)
    sm = branch_successor(m)
    ssm = branch_successor(sm)
    pssm = branch_right_inverse(ssm)
    require(branch_successor(pssm) == ssm, "branch example right inverse")
    require(pssm != sm, "invalid cancellation should fail in branch example")
    structural_control = {
        "scope": "successor/right-inverse equations only, not an F/EI model",
        "m": m,
        "S_m": sm,
        "S_S_m": ssm,
        "p_S_S_m": pssm,
        "S_p_S_S_m": branch_successor(pssm),
        "right_inverse_equation_holds": True,
        "cancelled_equation_fails": True,
    }

    print(json.dumps({
        "status": "PASS",
        "claim": "finite diagnostics only; the nonstandard theorem uses the written proof",
        "counts": counts,
        "targeted_controls": controls,
        "invalid_cancellation_control": structural_control,
        "unresolved": "F + actual equality + equation induction has not here been proved to imply S injective",
    }, indent=2))


if __name__ == "__main__":
    main()
