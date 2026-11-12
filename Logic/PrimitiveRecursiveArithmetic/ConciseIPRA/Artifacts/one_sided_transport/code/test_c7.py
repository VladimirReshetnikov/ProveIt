# Regression certificates and independent finite substitution checks for C7.
import ast
import gzip
import io
import json
import random
import subprocess
import sys
import tokenize
from pathlib import Path

from c7_checker import ZERO as Z, check, formula, lift, replace, term

ROOT = Path(__file__).resolve().parent


def S(a):
    return ["S", a]


def I(v, a, h):
    return ["I", v, a, h]


def E(a, b):
    return ["=", a, b]


def reflexivity(a, n):
    w = I(Z, a, Z)
    p = ["i0", a, Z]
    return ["x", w, a, n, p, p]


def symmetry(a, b, p, n):
    w = I(Z, Z, Z)
    return ["x", w, Z, lift(a, n), ["i0", Z, Z], p]


def build_cases():
    cases = []

    def add(name, goal, proof, accept):
        cases.append({"name": name, "accept": accept,
                      "certificate": [goal, proof]})

    s = I(Z, Z, Z)
    major = ["i0", Z, Z]
    add("iterator_zero", E(I(Z, S(Z), Z), S(Z)),
        ["i0", S(Z), Z], True)
    add("iterator_successor", E(I(S(Z), Z, S(0)), S(I(Z, Z, S(0)))),
        ["is", Z, Z, S(0)], True)

    # This expected RHS is written independently, and checks insertion of an
    # iterator-valued term below the inner iterator's state binder.
    h = I(S(Z), 0, S(0))
    r = I(Z, Z, h)
    nested_rhs = I(S(Z), r, S(lift(r, 0)))
    add("successor_computation_under_nested_binder",
        E(I(S(Z), Z, h), nested_rhs), ["is", Z, Z, h], True)

    add("symmetry_with_constant_template", E(Z, s),
        symmetry(s, Z, major, 0), True)

    # Simulate a(s)=b(s) -> a(t)=b(t), using exactly two X nodes.
    # Here s=I(0,0;u.0), t=0, a(v)=I(0,Sv;u.0), b(v)=Sv.
    f = I(Z, S(0), Z)
    g = S(0)
    first = ["x", s, Z, f, major, ["i0", S(s), Z]]
    second = ["x", s, Z, g, major, first]
    conclusion = E(I(Z, S(Z), Z), S(Z))
    add("two_X_simulate_two_sided_transport", conclusion, second, True)
    add("one_sided_target_mismatch", E(S(Z), I(Z, S(Z), Z)), second, False)

    # A literal-zero source is rejected even with true premises.
    zero_major = symmetry(s, Z, major, 0)
    add("literal_zero_source_rejected", E(Z, s),
        ["x", Z, s, 0, zero_major, reflexivity(Z, 0)], False)
    add("formula_used_as_numerical_template_rejected", conclusion,
        ["x", s, Z, E(0, 0), major, first], False)

    # DI progress proves I(y,0;u.Su)=y, using the local hypothesis.
    z = 0
    hz = S(1)
    iz = I(z, Z, hz)
    lhs = I(S(z), Z, hz)
    rhs = S(iz)
    successor_proof = ["is", z, Z, hz]
    flipped = symmetry(lhs, rhs, successor_proof, 1)
    step = ["x", iz, z, S(1), ["hyp", 0], flipped]
    body = E(I(1, Z, S(2)), 1)
    add("DI_progress_uses_induction_hypothesis", ["D", body],
        ["di", Z, step], True)
    add("DI_case_cannot_reuse_progress_hypothesis", ["D", body],
        ["di", S(Z), step], False)
    add("DI_unallocated_witness_rejected", ["D", body],
        ["di", 0, step], False)

    # A nonzero iterator witness with its own binder is inserted below y.
    witness = I(Z, S(Z), 0)
    add("DI_case_iterator_witness_binder_shift", ["D", E(0, 0)],
        ["di", witness, reflexivity(I(Z, S(Z), 1), 1)], True)
    add("DI_compound_matrix_cases", ["D", ["D", E(Z, Z)]],
        ["di", Z, ["di", Z, reflexivity(Z, 2)]], True)

    # Derive Q_y(y=y) by D introduction and witness elimination.
    dbody = E(1, 1)
    dp = ["di", Z, reflexivity(S(0), 1)]
    qp = ["de", dbody, dp, ["hyp", 0]]
    add("DE_exports_closure_at_fresh_witness", ["Q", E(0, 0)], qp, True)
    add("QE_specialization", E(S(Z), S(Z)),
        ["qe", E(0, 0), S(Z), qp, reflexivity(Z, 0)], True)

    add("unallocated_computation_body_rejected", E(I(Z, Z, 1), Z),
        ["i0", Z, 1], False)
    add("boolean_term_rejected", E(False, Z), ["hyp", 0], False)
    add("malformed_goal_rejected", ["Q", Z], ["hyp", 0], False)
    add("boolean_hypothesis_index_rejected", ["D", E(Z, Z)],
        ["di", Z, ["hyp", False]], False)
    add("negative_hypothesis_index_rejected", ["D", E(Z, Z)],
        ["di", Z, ["hyp", -1]], False)
    add("extra_instruction_payload_rejected", E(I(Z, Z, Z), Z),
        ["i0", Z, Z, "unused"], False)
    add("false_closed_equation_rejected", E(Z, S(Z)), ["i0", Z, Z], False)
    add("unknown_rule_rejected", E(Z, Z), ["reflexivity"], False)
    return cases


def evaluate_term(a, environment):
    # Independent denotational evaluator; no use of replace or lift.
    if type(a) is int:
        return environment[a]
    if a[0] == "0":
        return 0
    if a[0] == "S":
        return evaluate_term(a[1], environment) + 1
    count = evaluate_term(a[1], environment)
    state = evaluate_term(a[2], environment)
    for _ in range(count):
        state = evaluate_term(a[3], environment + [state])
    return state


def evaluate_formula(a, environment):
    if a[0] == "=":
        return evaluate_term(a[1], environment) == evaluate_term(a[2], environment)
    if a[0] == "Q":
        return (not evaluate_formula(a[1], environment + [0]) or
                all(evaluate_formula(a[1], environment + [y]) for y in range(3)))
    return any(not evaluate_formula(a[1], environment + [x, 0]) or
               all(evaluate_formula(a[1], environment + [x, y]) for y in range(3))
               for x in range(3))


def substitution_checks():
    rng = random.Random(7112026)

    def random_term(n, depth):
        if depth == 0:
            return rng.choice([Z] + list(range(n)))
        op = rng.randrange(3)
        if op == 0:
            return random_term(n, 0)
        if op == 1:
            return S(random_term(n, depth - 1))
        return I(rng.choice([Z, S(Z), S(S(Z))]),
                 random_term(n, depth - 1), random_term(n + 1, depth - 1))

    def random_formula(n, depth):
        if depth == 0 or rng.randrange(3) == 0:
            return E(random_term(n, 2), random_term(n, 2))
        op = rng.choice(["Q", "D"])
        return [op, random_formula(n + (1 if op == "Q" else 2), depth - 1)]

    checks = 0
    for n in range(4):
        for _ in range(100):
            environment = [rng.randrange(3) for _ in range(n)]
            t = random_term(n, 3)
            value = evaluate_term(t, environment)
            f = random_term(n + 1, 3)
            result = replace(f, n, t)
            if not term(result, n) or evaluate_term(result, environment) != evaluate_term(f, environment + [value]):
                raise AssertionError(("term substitution", n, t, f, result))
            b = random_formula(n + 1, 2)
            result = replace(b, n, t)
            if not formula(result, n) or evaluate_formula(result, environment) != evaluate_formula(b, environment + [value]):
                raise AssertionError(("formula substitution", n, t, b, result))
            f = random_term(n + 2, 3)
            y = rng.randrange(3)
            result = replace(f, n, t, depth=n + 2)
            if not term(result, n + 1) or evaluate_term(result, environment + [y]) != evaluate_term(f, environment + [value, y]):
                raise AssertionError(("D witness substitution", n, t, f, result))
            checks += 3
    return checks


def main():
    cases = build_cases()
    results = []
    for case in cases:
        try:
            check(*case["certificate"])
            accepted = True
        except (ValueError, TypeError, IndexError, RecursionError):
            accepted = False
        if accepted != case["accept"]:
            raise AssertionError((case["name"], accepted, case["accept"]))
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else [])
            command.append(str(ROOT / "c7_checker.py"))
            run = subprocess.run(command, input=json.dumps(case["certificate"]),
                                 text=True, capture_output=True)
            observed = run.returncode == 0 and run.stdout.strip() == "ACCEPT"
            if observed != case["accept"]:
                raise AssertionError((case["name"], optimized, run.stderr))
        results.append({"name": case["name"], "expected": case["accept"], "passed": True})
    checks = substitution_checks()
    source = ROOT / "c7_checker.py"
    normalized = ast.unparse(ast.parse(source.read_text())) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    metrics = {
        "python": sys.version,
        "tokens": sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
        "normalized_bytes": len(normalized.encode()),
        "gzip9_normalized": len(gzip.compress(normalized.encode(), compresslevel=9, mtime=0)),
        "normalization": "ast.unparse(ast.parse(source)) + newline",
        "contract": "Closed-goal grammar and all consumed syntax fields validated"
    }
    (ROOT / "c7_checker_normalized.py").write_text(normalized)
    (ROOT / "metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    (ROOT / "certificates.json").write_text(json.dumps(cases, indent=2) + "\n")
    summary = {"certificate_cases": len(cases),
               "expected_acceptances": sum(c["accept"] for c in cases),
               "direct_checks": len(cases), "subprocess_checks": 2 * len(cases),
               "optimized_mode_checked": True,
               "independent_substitution_checks": checks, "results": results,
               "formal_verification": False}
    (ROOT / "test_results.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"metrics": metrics, "summary": {k: v for k, v in summary.items() if k != "results"}}, indent=2))


if __name__ == "__main__":
    main()
