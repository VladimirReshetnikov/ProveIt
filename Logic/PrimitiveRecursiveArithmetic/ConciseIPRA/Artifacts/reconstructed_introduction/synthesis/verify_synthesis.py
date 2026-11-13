"""Deterministic fixtures and syntax-law checks for synthesis_checker.py."""
import ast
import copy
import gzip
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

import synthesis_checker as c

HERE = Path(__file__).resolve().parent


def s(t):
    return ["s", t]


def eq(a, b):
    return ["=", a, b]


def it(n, a, h):
    return ["i", n, a, h]


def numeral(n):
    result = 0
    for _ in range(n):
        result = s(result)
    return result


def refl(t):
    axiom = ["z", t, ["v", 0]]
    return ["t", axiom, "hole", eq("hole", t), axiom]


def size(a):
    if type(a) is not list or a[0] == "v":
        return 1
    return 1 + sum(size(b) for b in a[1:])


def instantiate(a, x, y):
    return c.substitute(c.substitute(a, "x", x), "y", y)


def marker(body, witness):
    # The count is on B(x,S z), before substituting the marker for x.
    n = 1 + size(c.substitute(body, "y", s("z")))
    return it(0, witness, numeral(n))


def fixtures():
    out = []

    def accept(label, proof, expected=None):
        result = c.infer(proof)
        if expected is not None and result != expected:
            raise RuntimeError((label, result, expected))
        out.append((label, [result, proof], True))

    def reject(label, goal, proof):
        out.append((label, [goal, proof], False))

    identity = ["v", 0]
    accept("zero_computation", ["z", 0, identity])
    accept("successor_computation", ["s", 0, 0, identity])
    accept("derived_reflexivity", refl(s(0)), eq(s(0), s(0)))

    # Equation induction in which the induction hypothesis is actually used.
    seed = eq(it("z", 0, identity), 0)
    template = eq(it(s("z"), 0, identity), "hole")
    branch = ["t", ["h", 0], "hole", template, ["s", "z", 0, identity]]
    induction = ["j", 0, "z", seed, branch]
    expected_d = ["d", eq(it(["v", 0], 0, identity), 0)]
    accept("progress_used_hypothesis", induction, expected_d)
    closure = ["d", induction, "b", ["h", 0]]
    expected_q = ["q", eq(it(["v", 0], 0, identity), 0)]
    accept("closure_from_vacuous_paired_intro", closure, expected_q)
    use = ["q", closure, ["z", 0, identity], numeral(3)]
    accept("closure_specialization", use, eq(it(numeral(3), 0, identity), 0))

    # Case mode when the chosen witness is nonzero.
    case = ["j", s(0), "z", eq(0, 0), refl(s("z"))]
    case_goal = ["d", eq(["v", 0], ["v", 0])]
    accept("case_mode", case, case_goal)
    bad = copy.deepcopy(case)
    bad[1] = 0
    reject("case_seed_cannot_impersonate_progress", case_goal, bad)

    # Unmarked witness occurrences cannot be distinguished from fixed data.
    body = eq("x", s(0))
    target = ["d", c.close(body, ["x", "y"])]
    unmarked = ["j", s(0), "z", eq(s(0), s(0)), ["h", 0]]
    reject("unmarked_witness_collision_changes_goal", target, unmarked)
    w = marker(body, s(0))
    marked = ["j", w, "z", eq(w, s(0)), ["h", 0]]
    accept("marked_witness_recovers_fixed_data", marked, target)

    # Abstraction under a quantifier does not capture its bound variable.
    body = ["q", eq("x", ["v", 0])]
    w = marker(body, 0)
    seed = c.substitute(body, "x", w)
    marked = ["j", w, "z", seed, ["h", 0]]
    target = ["d", c.close(body, ["x", "y"])]
    accept("compound_intro_under_bound_variable", marked, target)

    # A naked eigenvariable is not a substituted successor argument.
    naked = ["j", s(0), "z", eq("z", "z"), ["h", 0]]
    reject("naked_counter_cannot_escape", eq(0, 0), naked)

    # An existential eigenparameter cannot leave its elimination scope.
    d_refl = ["j", s(0), "z", eq(s(0), s(0)), ["h", 0]]
    escape = ["d", d_refl, "b", ["q", ["h", 0], refl("b"), 0]]
    reject("existential_eigenparameter_escape", eq(0, 0), escape)
    reject("free_parameter_in_closed_goal", eq("a", "a"), refl("a"))
    reject("floating_zero_rejected", eq(0, 0), ["z", 0.0, identity])
    reject("boolean_zero_rejected", eq(0, 0), ["z", False, identity])
    reject("dangling_bound_variable", eq(0, 0), ["z", ["v", 0], identity])
    reject("induction_for_compound_formula_not_progress", eq(0, 0),
           ["j", 0, "z", ["q", eq("z", "z")], ["h", 0]])
    reject("missing_hypothesis", eq(0, 0), ["h", 0])
    reject("negative_hypothesis_index", eq(0, 0), ["h", -1])
    reject("unknown_rule", eq(0, 0), ["accept", eq(0, 0)])
    return out


def syntax_checks():
    rng = random.Random(20261113)

    def tm(budget, depth, variables):
        leaves = [0] + list(variables) + [["v", i] for i in range(depth)]
        if budget == 0 or rng.randrange(3) == 0:
            return copy.deepcopy(rng.choice(leaves))
        if rng.randrange(2) == 0:
            return s(tm(budget - 1, depth, variables))
        return it(tm(budget - 1, depth, variables),
                  tm(budget - 1, depth, variables),
                  tm(budget - 1, depth + 1, variables))

    def fm(budget, depth):
        if budget == 0 or rng.randrange(3) == 0:
            return eq(tm(2, depth, ("a", "x", "y")),
                      tm(2, depth, ("a", "x", "y")))
        op = rng.choice(("q", "d"))
        return [op, fm(budget - 1, depth + (1 if op == "q" else 2))]

    checks = 0
    for _ in range(500):
        body = fm(3, 0)
        witness = tm(2, 0, ("a",))
        c.formula(body, {"a", "x", "y"})
        c.term(witness, {"a"})
        w = marker(body, witness)
        step = instantiate(body, w, s("z"))
        abstracted = c.replace_term(c.replace_term(step, w, "x"), s("z"), "y")
        if abstracted != body:
            raise RuntimeError("marker recovery failed")
        checks += 1
        seed = instantiate(body, w, 0)
        result = c.intro_result(w, "z", seed, step, {"a"})
        expected = ["d", c.close(body, ["x", "y"])]
        if result != expected:
            raise RuntimeError("introduction conclusion changed")
        checks += 1
        closed = c.close(body, ["x", "y"])
        reopened = c.open_binders(closed, ["x", "y"])
        if reopened != body:
            raise RuntimeError("binding round trip failed")
        checks += 1

    # Explicitly exercise a free label underneath an unrelated bound index.
    bound = ["q", eq(["v", 0], "a")]
    expected = ["q", eq(["v", 0], "x")]
    if c.replace_term(bound, "a", "x") != expected:
        raise RuntimeError("capture avoidance failed")
    checks += 1
    return checks


def main():
    records = []
    folder = HERE / "synthesis_fixtures"
    folder.mkdir(exist_ok=True)
    for label, cert, expected in fixtures():
        path = folder / (label + ".json")
        path.write_text(json.dumps(cert, separators=(",", ":")) + "\n")
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else [])
            command += [str(HERE / "synthesis_checker.py")]
            process = subprocess.run(command, input=json.dumps(cert), text=True,
                                     capture_output=True, timeout=30)
            accepted = process.returncode == 0 and process.stdout == "ACCEPT\n"
            if accepted != expected:
                raise RuntimeError((label, optimized, process.returncode,
                                    process.stdout, process.stderr))
            records.append({"case": label, "optimized": optimized,
                            "expected_acceptance": expected,
                            "exit_code": process.returncode})
    source = (HERE / "synthesis_checker.py").read_text()
    # Module docstrings are kept, matching the stated whole-module metric.
    normalized = ast.unparse(ast.parse(source)) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(token.type not in ignored for token in
                 tokenize.generate_tokens(io.StringIO(normalized).readline))
    report = {"fixtures": len(records) // 2, "cli_runs": len(records),
              "syntax_law_checks": syntax_checks(),
              "unexpected_results": 0,
              "metrics": {"significant_tokens": tokens,
                          "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
                          "normalized_utf8_bytes": len(normalized.encode()),
                          "gzip9_normalized_bytes": len(gzip.compress(normalized.encode(),
                                                                     compresslevel=9, mtime=0))},
              "runtime": sys.version,
              "proof_status": "Written universal proof; finite checks do not replace it.",
              "runs": records}
    (HERE / "synthesis_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "runs"}, indent=2))


if __name__ == "__main__":
    main()
