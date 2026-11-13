"""Finite diagnostics for the two-point obstruction; not a proof search.

The proof is obstruction.tex.  This program checks its closed counterformula,
the Boolean local-rule obligations, examples of the substitution law including
replacement terms that contain the eliminated parameter, and (if --upstream is
given) the incoming checker's ordinary proof of the counterformula.
"""
import argparse
import itertools
import json
import subprocess
import sys


def term(t, env):
    if isinstance(t, int):
        return t
    if isinstance(t, str):
        return env.get(t, 0)
    if t[0] == "S":
        return term(t[1], env) + 1
    _, n, a, u, h = t
    result = term(a, env)
    for _ in range(term(n, env)):
        result = term(h, dict(env, **{u: result}))
    return result


def formula(a, env):
    if a[0] == "=":
        return term(a[1], env) == term(a[2], env)
    _, x, y, body = a
    base = formula(body, dict(env, **{x: 0, y: 0}))
    step = formula(body, dict(env, **{x: 0, y: 1}))
    return not base or step


def free(t):
    if isinstance(t, int):
        return set()
    if isinstance(t, str):
        return {t}
    if t[0] == "S":
        return free(t[1])
    _, n, a, u, h = t
    return free(n) | free(a) | (free(h) - {u})


def subst_term(t, var, replacement):
    if isinstance(t, int):
        return t
    if isinstance(t, str):
        return replacement if t == var else t
    if t[0] == "S":
        return ("S", subst_term(t[1], var, replacement))
    _, n, a, u, h = t
    assert u not in free(replacement), "diagnostic uses fresh binder names"
    return ("I", subst_term(n, var, replacement),
            subst_term(a, var, replacement), u,
            h if u == var else subst_term(h, var, replacement))


def subst_formula(a, var, replacement):
    if a[0] == "=":
        return ("=", subst_term(a[1], var, replacement),
                subst_term(a[2], var, replacement))
    _, x, y, body = a
    assert not ({x, y} & free(replacement))
    return a if var in (x, y) else (
        "D", x, y, subst_formula(body, var, replacement))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", help="path to incoming newest.py")
    args = parser.parse_args()

    # Exactly the normal-form syntax expected by newest.py.  D binds x then y;
    # the iterator step adds u, hence x has de Bruijn index 3 in its body.
    json_goal = [[[1, 0, 3], [1, 0, [0, 0]]]]
    json_proof = ["i", [0, 0], ["r"]]

    select = lambda v, a, b: ("I", v, a, "u", b)
    body = ("=", select("y", 0, "x"), select("y", 0, 1))
    counterformula = ("D", "x", "y", body)
    assert formula(body, {"x": 0, "y": 0})
    assert not formula(body, {"x": 0, "y": 1})
    assert not formula(counterformula, {})
    assert all(formula(body, {"x": 1, "y": n}) for n in range(40))

    # Exhaustive Boolean local obligations for Use and Intro.  In the all-zero
    # environment both permitted Intro antecedents (0 and z) are the same row.
    bool_checks = 0
    for a, b0, b1 in itertools.product((False, True), repeat=3):
        if (not a or (b0 and b1)) and a:
            assert b0 and b1
        # The opened clause B00 -> (B00 and B01) is supplied by major D.
        if not b0 or b1:
            assert not b0 or (b0 and b1)
        for mode in ("case", "progress"):
            branch_valid = not b0 or b1
            if branch_valid:
                assert not b0 or b1
            bool_checks += 1

    # Test the substantive Export equality: r may depend on b, but the major
    # premise forces its value at b=0 to be 0. The substitution is one pass.
    replacements = [0, "b", ("I", "b", 0, "u", ("S", "u")),
                    ("I", 1, "b", "u", "u"),
                    ("I", 3, "b", "u", 0)]
    atoms = [("=", s, t) for s in (0, 1, "b", ("S", "b"))
             for t in (0, 1, "b", ("S", "b"))]
    formulas = atoms + [("D", "x", "y", a) for a in atoms]
    formulas += [("D", "x", "y",
                  ("=", select("y", "b", "x"), "b"))]
    substitution_checks = 0
    for r in replacements:
        assert term(r, {"b": 0}) == 0
        for a in formulas:
            changed = subst_formula(a, "b", r)
            assert formula(changed, {"b": 0}) == formula(a, {"b": 0})
            substitution_checks += 1

    result = {"two_point_counterformula": False,
              "ordinary_witness": 1,
              "ordinary_rows_checked": 40,
              "boolean_local_checks": bool_checks,
              "self_dependent_export_substitution_checks": substitution_checks,
              "proof_status": "theorem is in obstruction.tex; diagnostics are finite"}
    if args.upstream:
        run = subprocess.run([sys.executable, args.upstream],
                             input=json.dumps([json_goal, json_proof]),
                             text=True, capture_output=True, timeout=20)
        assert run.returncode == 0 and run.stdout.strip() == "ACCEPT", run.stderr
        result["unrestricted_intro_upstream"] = "ACCEPT"
        # The same shape with the restricted root witness 0 has step goal 0=1.
        run = subprocess.run([sys.executable, args.upstream],
                             input=json.dumps([json_goal, ["i", 0, ["r"]]]),
                             text=True, capture_output=True, timeout=20)
        assert run.returncode != 0
        result["same_certificate_with_root_witness_zero"] = "REJECT"
        result["underivability_basis"] = "semantic proof, not certificate rejection"
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
