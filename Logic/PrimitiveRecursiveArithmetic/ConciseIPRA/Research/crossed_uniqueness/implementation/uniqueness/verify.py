#!/usr/bin/env python3
"""Targeted checks of nontrivial derivations and trust-boundary failures."""

import ast
import copy
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

from build_certificates import generate
from uniqueness_checker import Z, S, Eq, Q, D, Invalid, check


ROOT = Path(__file__).resolve().parent


def reject(record, name):
    try:
        check(record)
    except (Invalid, ValueError, TypeError, IndexError, KeyError):
        return {"name": name, "status": "REJECT"}
    raise RuntimeError("accepted invalid certificate: " + name)


def record(scope, context, goal, proof):
    return {"scope": scope, "context": context, "goal": goal, "proof": proof}


def verify():
    positive = generate()
    cli = []
    for entry in positive:
        path = ROOT / "certificates" / (entry["name"] + ".json")
        p = subprocess.run([sys.executable, str(ROOT / "uniqueness_checker.py")],
                           input=path.read_text(), text=True, capture_output=True)
        if p.returncode != 0 or p.stdout != "ACCEPT\n":
            raise RuntimeError("CLI verification failed: " + entry["name"])
        cli.append({"name": entry["name"], "status": "ACCEPT"})
    negative = []
    negative.append(reject(record(0, [], Eq(Z, S(Z)), ["refl", Z]),
                           "false_equation"))
    negative.append(reject(record(0, [], Eq(Z, Z), ["refl", Z, "extra"]),
                           "extra_rule_field"))
    negative.append(reject(record(0, [], Eq(Z, Z), ["hyp", -1]),
                           "negative_context_index"))
    negative.append(reject(record(1, [], Eq(0, 0), ["refl", True]),
                           "boolean_is_not_variable"))
    negative.append(reject(record(0, [], Eq(Z, Z), ["refl", 0]),
                           "unbound_numerical_variable"))
    # The would-be recurrence eigenvariable cannot be supplied as a passive
    # parameter to h. At scope 0 the only permitted h index is its update
    # argument, index 0. Index 1 is necessarily out of scope.
    negative.append(reject(record(0, [], Eq(Z, Z),
        ["u", Z, Z, 1, Z, ["refl", Z], ["refl", Z]]),
        "U_counter_leak_into_update"))
    negative.append(reject(record(0, [], Eq(Z, Z),
        ["di", Eq(0, 0), 0, ["refl", S(0)]]),
        "DI_fresh_variable_used_as_witness"))
    # Even a reflexive equation mentioning the opened witness cannot escape
    # an existential discharge. This is the actual DE eigenvariable check.
    negative.append(reject(record(0, [], Eq(Z, Z),
        ["de", ["di", Eq(Z, Z), Z, ["refl", Z]], ["refl", 0]]),
        "DE_witness_escape"))
    identity = json.loads((ROOT / "certificates/identity_iteration.json").read_text())
    wrong_step = copy.deepcopy(identity)
    wrong_step["proof"][6] = ["refl", ["s", ["z"]]]
    negative.append(reject(wrong_step, "wrong_U_recurrence"))
    wrong_seed = copy.deepcopy(identity)
    wrong_seed["proof"][2] = ["s", ["z"]]
    negative.append(reject(wrong_seed, "wrong_U_initial_equation"))
    # QE must actually establish its base, not merely carry a closure.
    bad_qe = record(0, [Q(Eq(0, Z))], Eq(S(Z), Z),
                    ["qe", ["hyp", 0], ["refl", S(Z)], S(Z)])
    negative.append(reject(bad_qe, "wrong_QE_base"))

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

    tree = StripDocstrings().visit(ast.parse(
        (ROOT / "uniqueness_checker.py").read_text()))
    source = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    metrics = {"tokens": sum(t.type not in ignored for t in
                             tokenize.generate_tokens(io.StringIO(source).readline)),
               "ast_nodes": sum(1 for _ in ast.walk(ast.parse(source))),
               "normalized_bytes": len(source.encode())}
    results = {"python": platform.python_version(),
               "primitive_rules": ["hyp", "refl", "qe", "de", "di", "u"],
               "positive_certificates": positive, "CLI_replays": cli,
               "negative_checks": negative, "checker_metrics": metrics,
               "formalization_status": "executable certificate checks only; no Lean proof"}
    (ROOT / "VERIFICATION.json").write_text(json.dumps(results, indent=2) + "\n")
    return results


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
