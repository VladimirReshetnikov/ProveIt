"""Reproducible rule, scope, replacement, and certificate tests.

Run with Python 3. No third-party dependencies are required. Generated
fixtures include complete closed-theorem certificates and open-sequent
certificates for the verify API. The driver deliberately rejects the latter.
"""

import ast
import copy
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

import checker as c


ROOT = Path(__file__).resolve().parent
Z = []


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


def succ(term):
    return [term]


def iterator(counter, seed, body):
    return [counter, seed, body]


def equation(left, right):
    return [left, right]


def hyp(index):
    return {"rule": "hyp", "index": index}


def reflexivity(term):
    anchor = iterator(Z, term, 0)
    return {"rule": "brep", "equality": equation(anchor, term),
            "major": {"rule": "i0"}, "minor": {"rule": "i0"}}


def symmetry(left, right, proof):
    return {"rule": "brep", "equality": equation(left, left),
            "major": reflexivity(left), "minor": proof}


def join(source, target, result, major, minor):
    return {"rule": "brep", "equality": equation(source, target),
            "major": major, "minor": minor}


def transitivity(left, middle, right, first, second):
    return join(middle, right, left, second,
                symmetry(left, middle, first))


def size(term):
    return 1 + sum(map(size, term)) if type(term) is list else 1


def congruence(template, source, target, proof):
    """Compile congruence from BRep using a fresh computational marker."""
    tag = []
    for _ in range(size(template) + size(source) + size(target) + 1):
        tag = [tag]
    marker = iterator(Z, source, tag)
    source_marker = symmetry(marker, source, {"rule": "i0"})
    target_marker = join(source, marker, target, source_marker, proof)
    at_source = c.substitute_term(template, source)
    at_target = c.substitute_term(template, target)
    at_marker = c.substitute_term(template, marker)
    first = join(source, marker, at_source, source_marker,
                 reflexivity(at_source))
    second = join(target, marker, at_target, target_marker,
                  reflexivity(at_target))
    return transitivity(at_source, at_marker, at_target, first,
                        symmetry(at_target, at_marker, second))


def certificate(n, context, goal, proof):
    return {"n": n, "context": context, "goal": goal, "proof": proof}


def verify_record(record):
    c.verify(record["n"], record["context"], record["goal"], record["proof"])


def run():
    positives = {}
    negatives = {}
    operations = {}
    truth = equation(Z, Z)
    const_body = truth
    const_di = {"rule": "di", "witness": Z, "premise": hyp(0)}
    const_qi = {"rule": "qi", "premise": hyp(0)}

    positives["hyp_open"] = certificate(0, [truth], truth, hyp(0))
    positives["i0_closed"] = certificate(
        0, [], equation(iterator(Z, Z, 0), Z), {"rule": "i0"})
    recursive = iterator(Z, Z, succ(0))
    positives["is_closed"] = certificate(
        0, [], equation(iterator(succ(Z), Z, succ(0)), succ(recursive)),
        {"rule": "is"})
    positives["brep_reflexivity_closed"] = certificate(
        0, [], truth, reflexivity(Z))
    positives["brep_zero_source_closed"] = certificate(
        0, [], truth, {"rule": "brep", "equality": truth,
                       "major": reflexivity(Z), "minor": reflexivity(Z)})
    positives["di_closed"] = certificate(0, [], [const_body], const_di)
    positives["qi_closed"] = certificate(0, [], [0, 0, const_body], const_qi)
    positives["qe_closed"] = certificate(
        0, [], truth, {"rule": "qe", "body": const_body, "term": succ(Z),
                       "major": const_qi, "base": reflexivity(Z)})
    positives["de_closed"] = certificate(
        0, [], truth,
        {"rule": "de", "matrix": const_body, "major": const_di,
         "branch": {"rule": "qe", "body": const_body, "term": 0,
                    "major": hyp(0), "base": reflexivity(Z)}})

    # A nonconstant equation genuinely changes between progress premises.
    positives["qi_variable_equation_closed"] = certificate(
        0, [], [0, 0, equation(0, 0)],
        {"rule": "qi", "premise": reflexivity(succ(0))})
    positives["di_variable_witness_closed"] = certificate(
        0, [], [equation(1, 1)],
        {"rule": "di", "witness": succ(Z), "premise": hyp(0)})

    # Higher-index parameters remain unchanged when the fresh parameter is
    # appended. The opened witness is the new parameter, not an old one.
    matrix = equation(1, 1)
    positives["de_parameter_open"] = certificate(
        2, [[matrix]], equation(1, 1),
        {"rule": "de", "matrix": matrix, "major": hyp(0),
         "branch": reflexivity(1)})

    # Complete generated congruence certificates, including passive copies
    # that a naive global replacement of the original source would alter.
    source, target = 0, succ(0)
    templates = {
        "passive_copies": [0, 1, 2],
        "under_iterator_binder": [Z, Z, 1],
        "nested_iterator_binders": [Z, Z, [Z, Z, 2]],
        "unused_hole": [1],
        "repeated_hole": [0, 0, 1],
    }
    for name, template in templates.items():
        result = equation(c.substitute_term(template, source),
                          c.substitute_term(template, target))
        positives["congruence_" + name] = certificate(
            1, [equation(source, target)], result,
            congruence(template, source, target, hyp(0)))

    # Under this body, index 0 is bound; outer parameter 0 has index 1.
    destination = iterator(Z, Z, 0)
    wrong_changed = iterator(Z, Z, Z)
    major = equation(0, Z)
    negatives["bound_variable_must_not_match_free_source"] = certificate(
        1, [major, equation(wrong_changed, Z)], equation(Z, destination),
        {"rule": "brep", "equality": major, "major": hyp(0), "minor": hyp(1)})

    # Replacing zero by a free parameter must shift that parameter in h.
    destination = iterator(0, 0, Z)
    correct_changed = iterator(0, 0, 1)
    captured_changed = iterator(0, 0, 0)
    positives["replacement_avoids_capture_open"] = certificate(
        1, [major, equation(correct_changed, Z)], equation(Z, destination),
        {"rule": "brep", "equality": major, "major": hyp(0), "minor": hyp(1)})
    negatives["replacement_captures_inserted_parameter"] = certificate(
        1, [major, equation(captured_changed, Z)], equation(Z, destination),
        {"rule": "brep", "equality": major, "major": hyp(0), "minor": hyp(1)})

    operations["no_recursive_replacement_inside_inserted_term"] = (
        c.replace_term(Z, Z, succ(Z)) == succ(Z))
    operations["bound_variable_is_protected"] = (
        c.replace_term(iterator(Z, Z, 0), 0, Z) == iterator(Z, Z, 0))
    operations["inserted_parameter_is_shifted"] = (
        c.replace_term(iterator(0, 0, Z), Z, 0) == iterator(0, 0, 1))
    operations["substitution_avoids_capture_under_iterator"] = (
        c.substitute_term(iterator(Z, Z, 1), 0) == iterator(Z, Z, 1))
    operations["substitution_avoids_capture_under_D"] = (
        c.substitute_formula([equation(2, 0)], 0) == [equation(2, 0)])
    operations["substitution_avoids_capture_under_Q"] = (
        c.substitute_formula([0, 0, equation(1, 0)], 0)
        == [0, 0, equation(1, 0)])
    operations["witness_leaves_y_bound"] = (
        c.witness_body(equation(1, 0), 0) == equation(1, 0))

    bad = copy.deepcopy(positives["i0_closed"])
    bad["goal"][1] = succ(Z)
    negatives["wrong_zero_endpoint"] = bad
    bad = copy.deepcopy(positives["is_closed"])
    bad["goal"][1] = Z
    negatives["wrong_successor_endpoint"] = bad
    bad = copy.deepcopy(positives["di_closed"])
    bad["proof"]["witness"] = 0
    negatives["fresh_parameter_as_existential_witness"] = bad
    bad = copy.deepcopy(positives["de_closed"])
    bad["goal"] = equation(0, Z)
    negatives["eigenparameter_escapes_conclusion"] = bad
    negatives["unbound_iterator_body"] = certificate(
        0, [], equation(iterator(Z, Z, 1), Z), {"rule": "i0"})
    negatives["boolean_is_not_a_variable"] = certificate(
        1, [], equation(True, True), reflexivity(0))
    negatives["boolean_is_not_Q_tag"] = certificate(
        0, [], [False, 0, truth], const_qi)
    negatives["term_array_of_wrong_arity"] = certificate(
        0, [], equation([Z, Z], Z), {"rule": "i0"})
    negatives["progress_on_compound_matrix"] = certificate(
        0, [], [0, 0, [truth]], {"rule": "qi", "premise": hyp(0)})
    bad = copy.deepcopy(positives["qe_closed"])
    bad["goal"] = equation(Z, succ(Z))
    negatives["wrong_closure_target"] = bad
    bad = copy.deepcopy(positives["i0_closed"])
    bad["proof"]["ignored_payload"] = 0
    negatives["extra_proof_fields"] = bad
    bad = copy.deepcopy(positives["hyp_open"])
    bad["proof"]["index"] = -1
    negatives["negative_hypothesis_index"] = bad
    bad = copy.deepcopy(positives["hyp_open"])
    bad["proof"]["index"] = False
    negatives["boolean_hypothesis_index"] = bad
    bad = copy.deepcopy(positives["i0_closed"])
    bad["proof"]["rule"] = "oracle"
    negatives["unknown_rule"] = bad

    for name, record in positives.items():
        try:
            verify_record(record)
        except Exception as error:
            raise AssertionError("positive fixture failed: " + name) from error
    for name, record in negatives.items():
        try:
            verify_record(record)
        except c.InvalidCertificate:
            pass
        else:
            raise AssertionError("negative fixture accepted: " + name)
    for name, passed in operations.items():
        if not passed:
            raise AssertionError("operation test failed: " + name)

    fixtures = ROOT / "fixtures"
    for category, records in (("positive", positives), ("negative", negatives)):
        folder = fixtures / category
        folder.mkdir(parents=True, exist_ok=True)
        for name, record in records.items():
            (folder / (name + ".json")).write_text(
                json.dumps(record, indent=2) + "\n", encoding="utf-8")

    driver_checks = 0
    for record in positives.values():
        completed = subprocess.run(
            [sys.executable, str(ROOT / "checker.py")],
            input=json.dumps(record), text=True, capture_output=True)
        closed = record["n"] == 0 and record["context"] == []
        if (completed.returncode == 0) != closed:
            raise AssertionError("driver contract mismatch: " + completed.stderr)
        driver_checks += 1

    source = (ROOT / "checker.py").read_text(encoding="utf-8")
    normalized_with_docstrings = ast.unparse(ast.parse(source)) + "\n"
    normalized = ast.unparse(StripDocstrings().visit(ast.parse(source))) + "\n"
    (ROOT / "checker.normalized.py").write_text(normalized, encoding="utf-8")
    ignored = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER,
               tokenize.COMMENT}
    tokens = sum(token.type not in ignored
                 for token in tokenize.generate_tokens(io.StringIO(normalized).readline))
    result = {
        "python": platform.python_version(),
        "positive_sequents": len(positives),
        "negative_certificates": len(negatives),
        "operation_tests": len(operations),
        "driver_checks": driver_checks,
        "all_passed": True,
        "checker_metrics": {
            "significant_tokens": tokens,
            "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
            "normalized_utf8_bytes": len(normalized.encode("utf-8")),
            "raw_utf8_bytes": len(source.encode("utf-8")),
            "scope": "entire standalone module, excluding docstrings/comments only",
            "normalization": "recursively strip docstrings; ast.unparse; one final LF",
            "source_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
            "normalized_sha256": hashlib.sha256(normalized.encode("utf-8")).hexdigest(),
        },
        "checker_metrics_with_docstrings": {
            "significant_tokens": sum(token.type not in ignored for token in
                tokenize.generate_tokens(io.StringIO(normalized_with_docstrings).readline)),
            "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized_with_docstrings))),
            "normalized_utf8_bytes": len(normalized_with_docstrings.encode("utf-8")),
        },
        "operations": operations,
        "positive_names": list(positives),
        "negative_names": list(negatives),
    }
    (ROOT / "test_results.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    run()
