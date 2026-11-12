"""Reproduce finite checker regressions, macro diagnostics, and source counts."""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

import checker as K
import produce as U

ROOT = Path(__file__).resolve().parent


def accepted(packet):
    try:
        return K.verify(packet)
    except Exception:
        return False


def metrics(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
    normalized = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
               tokenize.ENDMARKER}
    tokens = sum(t.type not in ignored for t in
                 tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {"normalized_tokens": tokens,
            "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "normalized_bytes": len(normalized.encode()),
            "raw_bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    cases = U.fixtures()
    (ROOT / "fixtures.json").write_text(json.dumps({"cases": cases}, indent=2) + "\n")
    replays = []
    for case in cases:
        result = accepted(case["packet"])
        if result != case["accept"]:
            raise AssertionError((case["name"], "in_process", result))
        for flags in ([], ["-O"]):
            p = subprocess.run([sys.executable, *flags, str(ROOT / "checker.py")],
                               input=json.dumps(case["packet"]), text=True,
                               capture_output=True, timeout=20)
            actual = p.returncode == 0 and p.stdout == "ACCEPT\n"
            if actual != case["accept"]:
                raise AssertionError((case["name"], flags, p.returncode, p.stdout, p.stderr))
            if not actual and (p.returncode == 0 or p.stdout != "REJECT\n"):
                raise AssertionError((case["name"], "failure_interface", p.returncode, p.stdout))
            replays.append({"name": case["name"], "optimized": bool(flags),
                            "expected": case["accept"], "accepted": actual})

    diagnostics = 0
    templates = [U.V(0), U.S(U.V(0)), U.G(U.V(0), 0),
                 U.G(U.V(1), U.V(0)),
                 U.J(U.V(0), U.G(U.V(1), U.V(0)))]
    for ambient in range(5):
        for n in range(6):
            for seed in range(5):
                for body in templates:
                    term = U.initialized(U.numeral(n), U.numeral(seed), body)
                    K.term(term, 1, set())
                    if body == U.G(U.V(0), 0):
                        if term != K.countdown(U.numeral(n), U.numeral(seed)):
                            raise AssertionError("specialized countdown differs")
                    expected = seed
                    for _ in range(n):
                        expected = U.evaluate(body, environment=(expected, ambient))
                    actual = U.evaluate(term, environment=(ambient,))
                    if actual != expected:
                        raise AssertionError(("initializer", n, seed, ambient, body, actual, expected))
                    diagnostics += 1
            # Both counter and seed have an ambient bound coordinate.
            term = U.initialized(U.V(0), U.S(U.V(0)), U.G(U.V(1), U.V(0)))
            K.term(term, 1, set())
            expected = ambient + 1
            for _ in range(ambient):
                expected = expected + 1 if ambient == 0 else ambient - 1
            if U.evaluate(term, environment=(ambient,)) != expected:
                raise AssertionError("ambient counter/seed capture")
            diagnostics += 1
            fixed = K.countdown(U.V(0), U.S(U.V(0)))
            if fixed != U.initialized(U.V(0), U.S(U.V(0)), U.G(U.V(0), 0)):
                raise AssertionError("specialized countdown captures a seed")

    result = {"python": platform.python_version(),
              "finite_fixture_count": len(cases),
              "positive_fixtures": sum(c["accept"] for c in cases),
              "negative_fixtures": sum(not c["accept"] for c in cases),
              "in_process_replays": len(cases), "cli_replays": len(replays),
              "standard_model_macro_diagnostics": diagnostics,
              "candidate_complete_checker": metrics(ROOT / "checker.py"),
              "inherited_complete_checker": metrics(ROOT / "baseline_checker.py"),
              "replays": replays,
              "scope": "Finite certificate tests and intended-model diagnostics; not a formal proof of the metatheorems."}
    (ROOT / "validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "replays"}, indent=2))


if __name__ == "__main__":
    main()
