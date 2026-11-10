"""Replay the BJ certificates and targeted corruptions in ordinary and -O Python."""
import ast
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys

import checker
import produce

ROOT = Path(__file__).resolve().parents[1]


def ensure(condition, message):
    if not condition:
        raise RuntimeError(message)


def nodes(tree):
    if isinstance(tree, dict):
        yield tree
        for value in tree.values():
            yield from nodes(value)
    elif isinstance(tree, list):
        for value in tree:
            yield from nodes(value)


def capture_controls():
    # Expected conclusions are built explicitly, independently of substitution.
    v = lambda x: ["v", x]
    B = lambda x, y: ["B", x, y]
    S = lambda x: B(0, x)
    J = lambda n, x, b: ["J", n, x, b]
    a, n, x, u, z = map(v, ("a", "n", "x", "u", "z"))
    transport = {
        "name": "capture_avoiding_congruence",
        "equation": [J(n, "z", B(B(S(a), 0), z)), J(n, "z", B(a, z))],
        "proof": {"r": "cong", "var": "hole",
                  "context": J(n, "a", B(v("hole"), a)),
                  "proof": {"r": "B", "a": a, "b": 0}}}
    body = J(u, "x", B(u, x))
    old = J(x, "u", body)
    successor = {
        "name": "capture_avoiding_JS",
        "equation": [J(S(x), "u", body), J(old, "z", B(old, z))],
        "proof": {"r": "JS", "n": x, "binder": "u", "body": body}}
    good = {"format": "BJ-equations-v1", "lemmas": [transport, successor]}
    bad_transport = deepcopy(good)
    bad_transport["lemmas"][0]["equation"] = [
        J(n, "a", B(B(S(a), 0), a)), J(n, "a", B(a, a))]
    bad_successor = deepcopy(good)
    bad_successor["lemmas"][1]["equation"][1] = J(old, "x", B(old, x))
    return good, bad_transport, bad_successor


def main():
    packet = json.loads((ROOT / "certificates/bj_equations.json").read_text())
    ensure(packet == produce.build(), "distributed certificate differs from producer")
    expected_names = ["sign_zero", "sign_successor", "weak_predecessor_successor",
                      "selector_zero", "selector_successor", "predecessor_zero",
                      "predecessor_successor", "reset_zero", "reset_successor",
                      "orbit_zero", "orbit_successor", "orbit_range",
                      "initializer_zero", "initializer_successor"]
    ensure([p["name"] for p in packet["lemmas"]] == expected_names, "unexpected theorem inventory")
    ensure(len(checker.check(packet)) == 14, "theorem count")
    source = (ROOT / "code/checker.py").read_text()
    ensure(not any(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(source))),
           "checker must not depend on assertions")
    capture, bad_capture, bad_js_capture = capture_controls()
    (ROOT / "certificates/capture_controls.json").write_text(json.dumps(capture, separators=(",", ":")) + "\n")
    cases = [("fourteen_generic_theorems", packet, True),
             ("capture_avoiding_positive_controls", capture, True),
             ("captured_congruence_conclusion", bad_capture, False),
             ("captured_JS_conclusion", bad_js_capture, False)]

    def corrupt(label, mutation):
        altered = deepcopy(packet)
        mutation(altered)
        cases.append((label, altered, False))

    def named(p, label):
        return next(item for item in p["lemmas"] if item["name"] == label)

    corrupt("wrong_B_computation", lambda p: named(p, "weak_predecessor_successor")["proof"].update(a=produce.S(produce.V("n"))))
    corrupt("bad_induction_range", lambda p: named(p, "orbit_range")["proof"].update(lhs=produce.orbit(produce.V("n"), produce.V("a"))))
    corrupt("wrong_h_update", lambda p: named(p, "orbit_successor")["proof"].update(body=produce.H(produce.h(produce.V("u")), produce.V("a"))))
    corrupt("wrong_induction_base", lambda p: named(p, "orbit_range")["proof"].update(base={"r": "refl", "term": 0}))
    corrupt("nonfresh_eigenvariable", lambda p: named(p, "orbit_range")["proof"].update(eigen="a"))
    corrupt("unavailable_induction_hypothesis", lambda p: next(n for n in nodes(named(p, "orbit_range")["proof"]["step"]) if n.get("r") == "hyp").update(index=1))
    corrupt("wrong_successor_counter", lambda p: named(p, "orbit_successor")["proof"].update(n=produce.V("n")))
    corrupt("forged_top_level_hypothesis", lambda p: named(p, "initializer_zero").update(proof={"r": "hyp", "index": 0}))
    corrupt("forward_reference", lambda p: named(p, "sign_zero").update(proof={"r": "ref", "name": "initializer_zero", "sub": {}}))
    corrupt("malformed_B_term", lambda p: named(p, "selector_zero")["equation"].__setitem__(0, ["B", 0]))
    corrupt("boolean_is_not_numerical_zero", lambda p: named(p, "sign_zero")["equation"].__setitem__(1, False))
    corrupt("quantified_induction_matrix", lambda p: named(p, "orbit_range")["proof"].update(lhs=["forall", "x", 0]))

    results = []
    for optimized in (False, True):
        command = [sys.executable] + (["-O"] if optimized else []) + [str(ROOT / "code/checker.py")]
        for label, candidate, expected in cases:
            run = subprocess.run(command, input=json.dumps(candidate), text=True,
                                 capture_output=True, timeout=40)
            accepted = run.returncode == 0 and run.stdout.strip() == "ACCEPT"
            rejected = run.returncode == 1 and run.stdout.strip() == "REJECT"
            ensure(accepted if expected else rejected, f"unexpected result: {label}, optimized={optimized}: {run.stdout} {run.stderr}")
            results.append({"case": label, "optimized": optimized, "expected": "ACCEPT" if expected else "REJECT",
                            "observed": run.stdout.strip(), "exit_code": run.returncode,
                            "diagnostic": run.stderr.strip()})
    counts = Counter(n["r"] for item in packet["lemmas"] for n in nodes(item["proof"]) if "r" in n)
    ensure(counts["ind"] == 1, "expected exactly one literal-equation induction")
    receipt = {"python": platform.python_version(), "scope": "supporting equational certificates; not a complete iPRA kernel or a size record",
               "generic_theorems": 14, "capture_control_theorems": 2, "proof_node_occurrences": sum(counts.values()),
               "rule_occurrences": dict(sorted(counts.items())), "fresh_cli_runs": len(results),
               "positive_runs": sum(r["expected"] == "ACCEPT" for r in results),
               "negative_runs": sum(r["expected"] == "REJECT" for r in results),
               "files": {str(path.relative_to(ROOT)): {"bytes": path.stat().st_size, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                         for path in [ROOT / "code/checker.py", ROOT / "code/produce.py", ROOT / "certificates/bj_equations.json", ROOT / "certificates/capture_controls.json"]},
               "results": results}
    (ROOT / "certificates/validation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k not in ("files", "results")}, indent=2))


if __name__ == "__main__":
    main()
