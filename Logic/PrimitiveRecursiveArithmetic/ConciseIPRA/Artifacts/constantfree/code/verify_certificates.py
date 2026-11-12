"""Reproduce certificate checks, boundary rejections, and complete-module sizes.

This support script is untrusted: neither proof checker imports it. It checks
the delivered proof trees and builds structurally complete adversarial inputs.
Finite validation complements, and does not replace, the written proof.
"""

from pathlib import Path
import ast
import copy
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

import checker_constantfree as C


ROOT = Path(__file__).resolve().parents[1]
IGNORED = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
        return node

    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def measure(path):
    raw = path.read_bytes()
    tree = StripDocstrings().visit(ast.parse(raw))
    normalized = (ast.unparse(tree) + "\n").encode()
    return {
        "path": path.relative_to(ROOT).as_posix(),
        "raw_bytes": len(raw),
        "normalized_bytes": len(normalized),
        "significant_tokens": sum(token.type not in IGNORED for token in
                                  tokenize.generate_tokens(
                                      io.StringIO(normalized.decode()).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def proof_nodes(value):
    if isinstance(value, dict):
        if "rule" in value:
            yield value
        for child in value.values():
            yield from proof_nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from proof_nodes(child)


def first(certificate, rule):
    return next(node for node in proof_nodes(certificate) if node["rule"] == rule)


def node(rule, conclusion, **fields):
    return {"rule": rule, "conclusion": conclusion, **fields}


def certificate(proof):
    return {"goal": proof["conclusion"], "proof": proof}


def refl(term):
    return node("refl", C.equality(term, term))


def make_cases():
    cases = []
    stored = {}
    for filename in ("unit_is_one", "anchor_independence", "zero_exists", "zero_unique"):
        payload = (ROOT / "certificates" / (filename + ".json")).read_bytes()
        stored[filename] = json.loads(payload)
        cases.append((filename, payload, True, "delivered mathematical derivation"))

    def add(label, value, expected, purpose):
        payload = (json.dumps(value, separators=(",", ":")) + "\n").encode()
        cases.append((label, payload, expected, purpose))

    variable = ["v", "arbitrary"]
    existential = ["ex", "x", C.equality(["v", "x"], ["v", "x"])]
    inhabited = node("parameter", existential, eigen="arbitrary",
                     proof=node("ex_intro", existential, witness=variable,
                                proof=refl(variable)))
    add("ordinary_nonempty_domain", certificate(inhabited), True,
        "Param proves existence without a closed term or arithmetic axiom")

    bad = copy.deepcopy(stored["unit_is_one"])
    first(bad, "j_zero")["anchor"] = ["v", "outside_scope"]
    add("unbound_axiom_anchor", bad, False, "anchor terms must be in numerical scope")

    bad = copy.deepcopy(stored["unit_is_one"])
    first(bad, "j_zero")["anchor"] = ["v", "t"]
    add("mismatched_axiom_anchor", bad, False,
        "an arithmetic instance must match its explicitly supplied anchor")

    bad = copy.deepcopy(stored["unit_is_one"])
    step = first(bad, "j_step")
    step["output"] = C.successor(step["output"])
    add("changed_graph_output", bad, False, "the claimed graph endpoint is checked")

    bad = copy.deepcopy(stored["unit_is_one"])
    first(bad, "j_step")["body"] = ["v", "outside_scope"]
    add("unbound_step_body", bad, False, "the body has only its stated binding scope")

    bad = copy.deepcopy(stored["unit_is_one"])
    first(bad, "induction")["anchor"] = ["v", "indcounter"]
    add("induction_anchor_depends_on_eigenvariable", bad, False,
        "the anchor is fixed before the induction eigenvariable is introduced")

    bad = copy.deepcopy(stored["unit_is_one"])
    first(bad, "induction")["eigen"] = "a"
    add("induction_reuses_outer_parameter", bad, False,
        "the induction eigenvariable cannot be an outer parameter")

    bad = copy.deepcopy(stored["unit_is_one"])
    all_nodes = [n for n in proof_nodes(bad) if n["rule"] == "all_intro"]
    all_nodes[1]["eigen"] = "a"
    add("universal_reuses_outer_parameter", bad, False,
        "universal introduction enforces its eigenvariable condition")

    bad = copy.deepcopy(stored["zero_exists"])
    bad["proof"] = bad["proof"]["proof"]
    add("zero_existence_without_parameter_scope", bad, False,
        "the zero witness needs Param when the public numerical scope is empty")

    literal = ["0"]
    invalid_exists = node("ex_intro", existential, witness=literal, proof=refl(literal))
    add("forbidden_primitive_zero", certificate(invalid_exists), False,
        "there is no literal-zero term constructor")

    # This proof tree has every base/step/conclusion equation lined up, so its
    # sole forbidden inference is applying induction to a conjunction.
    anchor, induction_variable, eigen = ["v", "a"], ["v", "x"], ["v", "n"]
    compound = ["and", C.equality(induction_variable, induction_variable),
                C.equality(induction_variable, induction_variable)]
    base_term, step_term = C.zero(anchor), C.successor(eigen)
    base_formula = C.substitute(compound, {"x": base_term})
    step_formula = C.substitute(compound, {"x": step_term})
    target_formula = C.substitute(compound, {"x": anchor})
    base = node("and_intro", base_formula, left=refl(base_term), right=refl(base_term))
    step = node("and_intro", step_formula, left=refl(step_term), right=refl(step_term))
    illegal_induction = node("induction", target_formula, variable="x", equation=compound,
                             term=anchor, eigen="n", base=base, step=step, anchor=anchor)
    quantified = node("all_intro", ["all", "a", target_formula],
                      eigen="a", proof=illegal_induction)
    add("compound_induction", certificate(quantified), False,
        "only literal equations may be induction invariants")

    bad = copy.deepcopy(stored["unit_is_one"])
    first(bad, "hyp")["index"] = True
    add("boolean_hypothesis_index", bad, False, "booleans are not integer indices")

    bad = copy.deepcopy(stored["unit_is_one"])
    first(bad, "j_zero")["unstated_axiom_field"] = 0
    add("extra_rule_field", bad, False, "proof instructions have exact field sets")

    cases.append(("duplicate_json_keys", b'{"goal":["bot"],"goal":["bot"],"proof":{}}\n',
                  False, "duplicate object keys are rejected by the JSON front end"))
    cases.append(("nonstandard_json_number", b'{"goal":NaN,"proof":{}}\n', False,
                  "nonstandard JSON numeric constants are rejected"))
    return cases


def substitution_checks():
    x, y = ["v", "x"], ["v", "y"]
    checks = []

    capture = ["j", x, "y", "r", x]
    actual = C.substitute(capture, {"x": y})
    expected = ["j", y, "fresh_unused", "r", y]
    checks.append(("avoids_body_capture", C.same(actual, expected) and C.free(actual) == {"y"}))

    shadow = ["j", x, "x", "r", x]
    actual = C.substitute(shadow, {"x": y})
    expected = ["j", y, "x", "r", x]
    checks.append(("counter_outside_body_binders", C.same(actual, expected)))

    for anchor in (x, ["v", "ji"], ["v", "jr"], shadow):
        checks.append(("macro_free_variables_" + str(len(checks)),
                       C.free(C.unit(anchor)) == C.free(anchor)
                       and C.free(C.zero(anchor)) == C.free(anchor)
                       and C.free(C.successor(anchor)) == C.free(anchor)))
    result = [{"name": name, "passed": passed} for name, passed in checks]
    if not all(row["passed"] for row in result):
        raise RuntimeError("substitution or macro-capture check failed")
    return result


def main():
    program = ROOT / "code/checker_constantfree.py"
    results = []
    for label, payload, expected, purpose in make_cases():
        for optimized in (False, True):
            command = [sys.executable, "-I", "-S", "-B"]
            if optimized:
                command.append("-O")
            result = subprocess.run(command + [str(program)], input=payload,
                                    capture_output=True, timeout=30)
            accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
            results.append({
                "case": label, "purpose": purpose, "optimized": optimized,
                "expected_acceptance": expected, "accepted": accepted,
                "exit_code": result.returncode,
                "payload_sha256": hashlib.sha256(payload).hexdigest(),
                "verdict": result.stdout.decode(errors="replace").strip()[:180],
            })
    failures = [r for r in results if r["accepted"] != r["expected_acceptance"]]
    report = {
        "python": platform.python_version(),
        "scope": "explicit certificate replay and soundness-boundary rejection checks",
        "assurance": "finite implementation validation, not proof-assistant verification",
        "cases": len(results) // 2,
        "process_executions": len(results),
        "failures": failures,
        "substitution_checks": substitution_checks(),
        "metrics": [measure(program), measure(ROOT / "reference/checker_register_graph.py")],
        "results": results,
    }
    destination = ROOT / "evidence"
    destination.mkdir(exist_ok=True)
    (destination / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key != "results"}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
