"""Focused executable checks and closed-theorem examples for selective_checker."""
import ast
import copy
import hashlib
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

import selective_checker as checker


ROOT = Path(__file__).resolve().parent


def S(term):
    return ["S", term]


def num(number):
    term = 0
    for _ in range(number):
        term = S(term)
    return term


def I(counter, seed, state, body):
    return ["I", counter, seed, state, body]


def eq(left, right):
    return ["=", left, right]


def selector(counter, seed, result):
    state = checker.fresh(checker.all_names([counter, seed, result]))
    return I(counter, seed, state, result)


def wi(body, step, image=0, z="z", x="x", y="y"):
    return {"rule": "wi", "x": x, "y": y, "body": body,
            "t": image, "z": z, "step": step}


def reflexivity(term):
    """A genuine IS instance; there is no primitive reflexivity rule."""
    return {"rule": "succ", "n": 0, "a": term, "u": "_r", "h": "_r"}


def alpha_term(left, right):
    return checker.term_key(left) == checker.term_key(right)


def must_reject(operation):
    try:
        operation()
    except checker.CheckError:
        return
    raise AssertionError("An invalid operation was accepted")


def natural_value(term, environment):
    if checker.zero(term):
        return 0
    if isinstance(term, str):
        return environment[term]
    if term[0] == "S":
        return natural_value(term[1], environment) + 1
    _, counter, seed, state, body = term
    count = natural_value(counter, environment)
    value = natural_value(seed, environment)
    for _ in range(count):
        value = natural_value(body, environment | {state: value})
    return value


def term_size(term):
    if checker.zero(term) or isinstance(term, str):
        return 1
    if term[0] == "S":
        return 1 + term_size(term[1])
    return 1 + term_size(term[1]) + term_size(term[2]) + term_size(term[4])


def examples():
    hypothesis = {"rule": "hyp"}
    iteration3 = I(num(3), 0, "u", S("u"))
    successor_proof = {"rule": "succ", "n": num(2), "a": 0, "u": "u", "h": S("u")}

    # The naming packet for zero, followed by QE at one, supplies b=0.
    naming_body = eq(selector("y", 0, "x"), 0)
    naming_proof = wi(naming_body, reflexivity(0))
    opened_body = checker.substitute_formula(naming_body, {"x": "b"})
    name_zero = {"rule": "qe", "y": "y", "body": opened_body, "t": num(1),
                 "major": hypothesis, "base": reflexivity(0)}
    # VSub with an unused b reverses the nontrivial general successor axiom.
    reverse_successor = {"rule": "vsub", "x": "b", "t": 0,
                         "u": iteration3, "v": num(3),
                         "major": name_zero, "minor": successor_proof}
    all_rules = {
        "goal": eq(num(3), iteration3),
        "proof": {"rule": "de", "x": "x", "y": "y", "body": naming_body,
                  "b": "b", "major": naming_proof, "minor": reverse_successor},
    }

    # Here progress really supplies z=S(z); VSub uses that assumption.
    progress_body = eq("y", S("y"))
    progress_step = {"rule": "vsub", "x": "z", "t": S("z"),
                     "u": S("z"), "v": S("z"),
                     "major": hypothesis, "minor": reflexivity(S("z"))}
    progress = {"goal": ["D", "x", "y", progress_body],
                "proof": wi(progress_body, progress_step)}

    cases_body = ["D", "p", "q", eq("y", "y")]
    cases_step = wi(eq(S("z"), S("z")), reflexivity(S("z")), z="w", x="p", y="q")
    cases = {"goal": ["D", "x", "y", cases_body],
             "proof": wi(cases_body, cases_step)}

    alias_mode_attack = copy.deepcopy(progress)
    alias_mode_attack["proof"]["t"] = I(0, 0, "u", "u")
    future_witness = copy.deepcopy(progress)
    future_witness["proof"]["t"] = "z"
    reused_eigenvariable = copy.deepcopy(cases)
    reused_eigenvariable["proof"]["step"]["z"] = "z"
    composite_vsub = copy.deepcopy(all_rules)
    composite_vsub["proof"]["minor"]["x"] = S("b")

    return {
        "closed_all_six_rules": (all_rules, True),
        "closed_general_successor": ({"goal": eq(iteration3, num(3)), "proof": successor_proof}, True),
        "closed_progress_with_used_assumption": (progress, True),
        "closed_compound_cases": (cases, True),
        "closed_one_iteration": ({"goal": eq(I(num(1), 0, "u", S("u")), num(1)), "proof": reflexivity(num(1))}, True),
        "closed_two_iterations": ({"goal": eq(I(num(2), 0, "u", S("u")), num(2)), "proof": reflexivity(num(2))}, True),
        "reject_raw_zero_alias_selecting_progress": (alias_mode_attack, False),
        "reject_future_witness_capture": (future_witness, False),
        "reject_reused_eigenvariable": (reused_eigenvariable, False),
        "reject_composite_vsub_source": (composite_vsub, False),
        "reject_leaked_free_variable": ({"goal": eq("b", 0), "proof": reflexivity(0)}, False),
        "reject_false_equation": ({"goal": eq(0, num(1)), "proof": hypothesis}, False),
        "reject_wrong_successor_endpoint": ({"goal": eq(iteration3, num(2)), "proof": successor_proof}, False),
        "reject_boolean_zero": ({"goal": eq(False, 0), "proof": reflexivity(0)}, False),
        "reject_full_normalization_shortcut": ({"goal": eq(iteration3, num(3)), "proof": reflexivity(iteration3)}, False),
        "reject_nonprimitive_refl_rule": ({"goal": eq(0, 0), "proof": {"rule": "refl"}}, False),
    }


def internal_checks():
    results = []

    def record(label, condition):
        if not condition:
            raise AssertionError(label)
        results.append(label)

    N = checker.normalize_term
    raw = I("n", 0, "y", "x")
    substituted = checker.substitute_term(raw, {"x": "y"})
    record("term substitution avoids capture", checker.free_term(substituted) == {"n", "y"})
    record("term substitution preserves binder distinction", substituted[3] != "y")
    formula = ["Q", "y", eq("x", "y")]
    fsub = checker.substitute_formula(formula, {"x": "y"})
    record("formula substitution avoids capture", checker.free_formula(fsub) == {"y"})
    record("formula binder is renamed", fsub[1] != "y")
    environment_result = checker.normalize_term(raw, {"x": "y"})
    record("normalizer environment avoids capture", checker.free_term(environment_result) == {"n", "y"})

    record("zero row", alpha_term(N(I(0, "a", "u", S("u"))), "a"))
    record("one row", alpha_term(N(I(num(1), "a", "u", S("u"))), S("a")))
    record("two row", alpha_term(N(I(num(2), "a", "u", S("u"))), S(S("a"))))
    record("state-free successor row", alpha_term(N(I(S("n"), "a", "u", "b")), "b"))
    erased = I(S("n"), 0, "u", I(0, num(1), "v", "u"))
    record("dependency erased by normalizing the body", alpha_term(N(erased), num(1)))
    identity3 = I(num(3), 0, "u", S("u"))
    record("three iterations are left unreduced", N(identity3)[0] == "I")
    unknown_constant = I("n", 0, "u", num(1))
    record("unknown-counter constant update stays residual", N(unknown_constant)[0] == "I")
    record("alpha-equivalent iterator binders", alpha_term(N(I("n", 0, "u", "u")), N(I("n", 0, "v", "v"))))

    # Open-sequent API tests are explicit about the assumptions and parameters.
    checker.check_proof(eq(S("x"), num(1)),
                        {"rule": "vsub", "x": "x", "t": 0,
                         "u": S("x"), "v": S("x"),
                         "major": {"rule": "hyp"}, "minor": reflexivity(S("x"))},
                        (eq("x", 0),), {"x"})
    results.append("VSub acts on a genuine free parameter in an open sequent")
    body = eq(I("y", 0, "u", "u"), 0)
    checker.check_proof(eq(I(num(3), 0, "u", "u"), 0),
                        {"rule": "qe", "y": "y", "body": body, "t": num(3),
                         "major": {"rule": "hyp"}, "base": reflexivity(0)},
                        (["Q", "y", body],), set())
    results.append("QE specializes an available closure at three")

    random_generator = random.Random(20261112)

    def random_term(depth, variables):
        if depth == 0:
            return random_generator.choice([0, *variables])
        choice = random_generator.randrange(3)
        if choice == 0:
            return random_generator.choice([0, *variables])
        if choice == 1:
            return S(random_term(depth - 1, variables))
        counter = random_generator.choice([num(0), num(1), num(2), num(3), "x", "y"])
        return I(counter, random_term(depth - 1, variables), "u",
                 random_term(depth - 1, variables + ["u"]))

    maximum_calls = 0
    for index in range(60):
        term = random_term(3, ["x", "y"])
        statistics = {}
        normal = checker.normalize_term(term, statistics=statistics)
        maximum_calls = max(maximum_calls, statistics["calls"])
        checker.validate_term(normal, {"x", "y"})
        assert alpha_term(N(normal), normal), ("idempotence", index)
        assert checker.free_term(normal) <= checker.free_term(term), ("free variables", index)
        assert statistics["calls"] <= (4 ** (term_size(term) + 1) - 1) // 3
        substitutions = {"x": S("y"), "y": I(num(2), 0, "v", S("v"))}
        left = N(checker.substitute_term(term, substitutions))
        right = N(checker.substitute_term(normal, substitutions))
        assert alpha_term(left, right), ("substitution coherence", index, term, left, right)
        for x in range(3):
            for y in range(3):
                environment = {"x": x, "y": y}
                assert natural_value(term, environment) == natural_value(normal, environment)
    results.append("60 generated terms: idempotence, free variables, call bound and substitution coherence")
    results.append("540 finite numerical interpretations agree before and after normalization")
    return {"checks": results, "generated_terms": 60,
            "finite_numerical_interpretations": 540, "maximum_observed_evaluator_calls": maximum_calls}


def metrics(path):
    tree = ast.parse(path.read_text())
    text = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {"tokens": sum(token.type not in ignored for token in tokenize.generate_tokens(io.StringIO(text).readline)),
            "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "normalized_utf8_bytes": len(text.encode()),
            "raw_utf8_bytes": len(path.read_bytes()),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    results = {"python": sys.version, "internal": internal_checks(),
               "metrics": metrics(ROOT / "selective_checker.py"), "certificates": []}
    fixture_folder = ROOT / "fixtures"
    fixture_folder.mkdir(exist_ok=True)
    for label, (certificate, expected) in examples().items():
        raw = (json.dumps(certificate, indent=2) + "\n").encode()
        (fixture_folder / (label + ".json")).write_bytes(raw)
        row = {"name": label, "expected_accept": expected, "runs": []}
        for optimized in (False, True):
            command = [sys.executable]
            if optimized:
                command.append("-O")
            command.append(str(ROOT / "selective_checker.py"))
            process = subprocess.run(command, input=raw, capture_output=True, timeout=20)
            accepted = process.returncode == 0 and process.stdout == b"ACCEPT\n"
            row["runs"].append({"optimized": optimized, "accepted": accepted,
                                "returncode": process.returncode,
                                "diagnostic": process.stderr.decode().strip()})
            if accepted != expected:
                raise AssertionError((label, optimized, process.stdout, process.stderr))
        results["certificates"].append(row)
    results["cli_executions"] = 2 * len(results["certificates"])
    results["failed_expectations"] = 0
    (ROOT / "verification.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({"metrics": results["metrics"], "internal": results["internal"],
                      "closed_certificate_cases": len(results["certificates"]),
                      "cli_executions": results["cli_executions"], "failed_expectations": 0}, indent=2))


if __name__ == "__main__":
    main()
