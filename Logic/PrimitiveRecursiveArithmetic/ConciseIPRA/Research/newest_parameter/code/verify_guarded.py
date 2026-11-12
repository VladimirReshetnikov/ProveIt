"""Reproduce guarded-checker metrics and focused certificate regressions.

This is an untrusted example/certificate generator, not part of the checker.
The tests do not constitute a formal proof of consequence equivalence.
"""
from __future__ import annotations

import ast
import copy
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "code" / "checker_guarded.py"
CONTROL = ROOT / "reference" / "checker_guarded_unrestricted.py"
PATTERN = ROOT / "reference" / "checker_guarded_pattern_dispatch.py"
spec = importlib.util.spec_from_file_location("guarded_kernel", CHECKER)
kernel = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernel)


def successor(t):
    return [0, t]


def numeral(n):
    t = 0
    for _ in range(n):
        t = successor(t)
    return t


def named_successor(t):
    return ("S", t)


def selector(n, a, b):
    return ("I", n, a, "unused_state", b)


def equation(a, b):
    return ("Eq", a, b)


def paired(x, y, body):
    return ("D", x, y, body)


def encode(expression, bound=()):
    if type(expression) is int:
        return expression
    if type(expression) is list:
        return copy.deepcopy(expression)
    if type(expression) is str:
        return bound.index(expression) + 1
    tag = expression[0]
    if tag == "S":
        return [0, encode(expression[1], bound)]
    if tag == "I":
        _, n, a, u, h = expression
        return [encode(n, bound), encode(a, bound), encode(h, (u,) + bound)]
    if tag == "Eq":
        return [encode(expression[1], bound), encode(expression[2], bound)]
    if tag == "D":
        _, x, y, b = expression
        return [encode(b, (y, x) + bound)]
    raise ValueError(tag)


def naming_family(y):
    return paired("x", "u", equation(
        selector("u", 0, selector(y, 0, named_successor("x"))),
        selector("u", 0, y)))


class Context:
    def __init__(self, clauses=(), scope=0):
        self.clauses, self.scope = clauses, scope

    def infer(self, proof):
        return kernel.infer(proof, self.clauses, self.scope)

    def reflexivity(self, t):
        p = ["zero", t, 0]
        return ["tr", [1, t], p, p]

    def symmetry(self, proof):
        s, _ = self.infer(proof)
        return ["tr", [1, s], proof, self.reflexivity(s)]

    def transitivity(self, p, q):
        s, t = self.infer(p)
        t2, _ = self.infer(q)
        if t != t2:
            raise ValueError("nonmatching transitivity endpoints")
        return ["tr", [s, 1], q, p]

    def compute(self, t, budget=100):
        """Prove root computations only; sufficient for the finite examples."""
        if budget <= 0:
            raise ValueError("example computation budget exhausted")
        if type(t) is list and len(t) == 3:
            n, a, h = t
            if n == 0:
                step = ["zero", a, h]
            elif type(n) is list and len(n) == 2 and n[0] == 0:
                step = ["succ", n[1], a, h]
            else:
                return t, self.reflexivity(t)
            _, v = self.infer(step)
            w, tail = self.compute(v, budget - 1)
            return w, self.transitivity(step, tail)
        return t, self.reflexivity(t)

    def computation_equation(self, goal):
        s, t = goal
        sn, p = self.compute(s)
        tn, q = self.compute(t)
        if sn != tn:
            raise ValueError("example equation does not compute to equal roots")
        return self.transitivity(p, self.symmetry(q))

    def introduce(self, matrix, builder):
        z = -self.scope - 1
        body = kernel.sub(matrix, -self.scope, 2)
        base = kernel.sub(body, z if len(matrix) == 2 else 0)
        context = Context(self.clauses + ((kernel.H, base),), self.scope + 1)
        expected = kernel.sub(body, successor(z))
        proof = ["intro", matrix, builder(context, expected)]
        if self.infer(proof) != [matrix]:
            raise ValueError("introduction generator mismatch")
        return proof

    def open(self, major, builder):
        formula = self.infer(major)
        if len(formula) != 1:
            raise ValueError("example major is not paired")
        b = -self.scope - 1
        body = kernel.sub(formula[0], b, 2)
        context = Context(self.clauses + ((kernel.sub(body, 0), body),), self.scope + 1)
        proof = ["open", major, builder(context, len(self.clauses))]
        self.infer(proof)
        return proof


def a_zero(context):
    matrix = encode(naming_family(0))[0]
    return context.introduce(matrix, lambda branch, goal: branch.computation_equation(goal))


def a_successor_parameter(context, z):
    matrix = encode(naming_family(named_successor(z)))[0]
    return context.introduce(matrix, lambda branch, goal: branch.computation_equation(goal))


def arbitrary_a(n):
    """A(n) by compound numerical cases, without the predecessor lemma."""
    root = Context()
    closure = encode(paired("r", "y", naming_family("y")))

    def successor_branch(context, goal):
        p = a_successor_parameter(context, -context.scope)
        if context.infer(p) != goal:
            raise ValueError("case successor mismatch")
        return p

    major = root.introduce(closure[0], successor_branch)
    proof = root.open(major, lambda branch, j: ["use", j, numeral(n), a_zero(branch)])
    return {"goal": encode(naming_family(numeral(n))), "proof": proof}


def to_unrestricted(proof, scope=0):
    tag = proof[0]
    if tag in {"zero", "succ"}:
        return copy.deepcopy(proof)
    if tag == "use":
        return [tag, proof[1], proof[2], to_unrestricted(proof[3], scope)]
    if tag == "tr":
        return [tag, proof[1], to_unrestricted(proof[2], scope), to_unrestricted(proof[3], scope)]
    if tag == "open":
        return [tag, to_unrestricted(proof[1], scope), to_unrestricted(proof[2], scope + 1)]
    if tag == "intro":
        return [tag, proof[1], -scope, to_unrestricted(proof[2], scope + 1)]
    raise ValueError(tag)


def tags(proof):
    tag = proof[0]
    result = {tag}
    children = {"zero": [], "succ": [], "use": proof[3:4],
                "tr": proof[2:4], "open": proof[1:3], "intro": proof[2:3]}[tag]
    for child in children:
        result.update(tags(child))
    return result


def run(path, data, optimized=False):
    args = [sys.executable] + (["-O"] if optimized else []) + [str(path)]
    process = subprocess.run(args, input=json.dumps(data), text=True,
                             capture_output=True, timeout=20)
    return process.returncode == 0 and process.stdout == "ACCEPT\n", process


def metrics(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                v = node.body[0].value
                if isinstance(v, ast.Constant) and isinstance(v.value, str):
                    node.body.pop(0)
    text = ast.unparse(tree) + "\n"
    omitted = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
               tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    count = sum(t.type not in omitted for t in tokenize.generate_tokens(io.StringIO(text).readline))
    return {"tokens": count, "ast_nodes": sum(1 for _ in ast.walk(ast.parse(text))),
            "normalized_bytes": len(text.encode("utf-8"))}


def main():
    examples = ROOT / "examples" / "guarded"
    examples.mkdir(parents=True, exist_ok=True)
    root = Context()
    positive = {
        "zero_computation": {"goal": [[0, 0, 1], 0], "proof": ["zero", 0, 1]},
        "successor_computation": {"goal": [[[0, 0], 0, 1], [0, 0, 1]], "proof": ["succ", 0, 0, 1]},
        "reflexivity_one": {"goal": [numeral(1), numeral(1)], "proof": root.reflexivity(numeral(1))},
        "naming_family_zero_direct": {"goal": encode(naming_family(0)), "proof": a_zero(root)},
        "naming_family_zero_cases": arbitrary_a(0),
        "naming_family_one_cases": arbitrary_a(1),
        "naming_family_two_nonzero_witness": arbitrary_a(2),
        "naming_family_three_nonzero_witness": arbitrary_a(3),
    }
    failures, results = [], []
    exercised = set()

    def record(name, path, data, expected, optimized=False):
        accepted, process = run(path, data, optimized)
        ok = accepted == expected
        if not expected:
            ok = ok and process.returncode != 0 and process.stdout == "REJECT\n"
        row = {"name": name, "checker": path.name, "optimized": optimized,
               "expected_accept": expected, "accepted": accepted, "passed": ok}
        results.append(row)
        if not ok:
            failures.append({**row, "stdout": process.stdout, "stderr": process.stderr})

    for name, data in positive.items():
        kernel.check(data)
        exercised.update(tags(data["proof"]))
        (examples / f"{name}.json").write_text(json.dumps(data, separators=(",", ":")) + "\n")
        for optimized in (False, True):
            record(name, CHECKER, data, True, optimized)
        control_data = {"goal": data["goal"], "proof": to_unrestricted(data["proof"])}
        record(name, CONTROL, control_data, True)
        record(name, PATTERN, data, True)

    negative = {
        "false_conclusion": {"goal": [0, numeral(1)], "proof": root.reflexivity(0)},
        "free_parameter_at_closed_root": {"goal": [[0, -1, 0], -1], "proof": ["zero", -1, 0]},
        "unbound_index_at_closed_root": {"goal": [[0, 1, 0], 1], "proof": ["zero", 1, 0]},
        "erased_body_still_scoped": {"goal": [[0, 0, -1], 0], "proof": ["zero", 0, -1]},
        "boolean_is_not_numerical_zero": {"goal": [[0, False, 0], False], "proof": ["zero", False, 0]},
        "unguarded_atomic_matrix": {"goal": [[0, 0]], "proof": ["intro", [0, 0], root.reflexivity(0)]},
        "unknown_instruction": {"goal": [0, 0], "proof": ["axiom", [0, 0]]},
        "extra_instruction_field": {"goal": [[0, 0, 0], 0], "proof": ["zero", 0, 0, 0]},
        "extra_document_field": {"goal": [0, 0], "proof": root.reflexivity(0), "trusted": True},
        "transport_wrong_minor": {"goal": [0, 0], "proof": ["tr", [1, 0], root.reflexivity(0), root.reflexivity(numeral(1))]},
        "illegal_term_in_formula": {"goal": [[], 0], "proof": root.reflexivity(0)},
    }
    altered = copy.deepcopy(positive["naming_family_zero_direct"])
    altered["proof"].insert(2, 0)
    negative["removed_witness_field_rejected"] = altered

    major = a_zero(root)
    body = kernel.sub(root.infer(major)[0], -1, 2)
    branch = Context(((kernel.sub(body, 0), body),), 1)
    antecedent = branch.computation_equation(kernel.sub(body, 0))
    leaky = ["open", major, ["use", 0, numeral(1), antecedent]]
    negative["eigenparameter_cannot_escape_open"] = {
        "goal": [0, 0], "proof": leaky}
    wrong_index = copy.deepcopy(positive["naming_family_two_nonzero_witness"])
    wrong_index["proof"][2][1] = False
    negative["boolean_clause_index_rejected"] = wrong_index
    wrong_target = copy.deepcopy(positive["naming_family_two_nonzero_witness"])
    wrong_target["proof"][2][2] = -2
    negative["use_target_outside_local_scope"] = wrong_target
    wrong_antecedent = copy.deepcopy(positive["naming_family_two_nonzero_witness"])
    wrong_antecedent["proof"][2][3] = ["zero", 0, 0]
    negative["clause_antecedent_mismatch"] = wrong_antecedent
    for name, data in negative.items():
        for optimized in (False, True):
            record(name, CHECKER, data, False, optimized)

    # This old certificate depends on dispatch choosing the literal name 1.
    # The new calculus proves equivalent theorems, but need not accept an old
    # proof unchanged when it used a different automatically chosen witness.
    pattern_matrix = encode(paired("x", "u", equation(
        selector("u", 0, "x"), selector("u", 0, named_successor(0)))))[0]
    old_body = kernel.sub(pattern_matrix, numeral(1), 2)
    old_base = kernel.sub(old_body, -1)
    old_branch = Context(((kernel.H, old_base),), 1)
    old_step = old_branch.computation_equation(kernel.sub(old_body, successor(-1)))
    old_data = {"goal": [pattern_matrix], "proof": ["intro", pattern_matrix, old_step]}
    record("old_naming_dispatch_certificate", PATTERN, old_data, True)
    record("old_naming_dispatch_certificate", CHECKER, old_data, False)

    # Direct open-judgment checks exercise the ordered newest parameter.
    open_matrix = encode(paired("x", "u", equation(
        selector("u", 0, "x"), selector("u", 0, -2))))[0]
    open_context = Context(scope=2)
    open_proof = open_context.introduce(open_matrix, lambda c, goal: c.computation_equation(goal))
    if open_context.infer(open_proof) != [open_matrix]:
        failures.append({"name": "newest_parameter_in_scope_two"})

    expected_families = {"zero", "succ", "use", "tr", "open", "intro"}
    if exercised != expected_families:
        failures.append({"name": "all_rule_families", "exercised": sorted(exercised)})
    report = {
        "status": "PASS" if not failures else "FAIL",
        "python": sys.version,
        "scope": "Focused finite certificate regressions; not a formal metatheory proof.",
        "positive_certificate_count": len(positive),
        "negative_certificate_count": len(negative),
        "cli_checks": len(results),
        "rule_families_exercised": sorted(exercised),
        "additional_open_judgment_check": "newest parameter at numerical scope two",
        "nonzero_witness_example": "A(2) is derived in the empty environment; its standard reading forces the existential witness to be 1.",
        "old_dispatch_note": "The old naming-specific certificate is accepted by its old checker and rejected unchanged by the new checker; this is a certificate-interface difference, not a theorem inequivalence claim.",
        "metrics": {"newest": metrics(CHECKER), "unrestricted": metrics(CONTROL), "old_pattern_dispatch": metrics(PATTERN)},
        "results": results,
        "failures": failures,
    }
    evidence = ROOT / "evidence"
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence / "guarded_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "positive_certificate_count", "negative_certificate_count", "cli_checks", "rule_families_exercised", "metrics")}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
