#!/usr/bin/env python3
"""Rebuild and independently verify the delivered ordinary quartics."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    root = Path(__file__).resolve().parent
    tests, src = root / "tests", root / "src"
    artifacts = root / "artifacts/natural"
    prefix = [sys.executable] + ([] if __debug__ else ["-O"])
    with tempfile.TemporaryDirectory(prefix="con-zfc-shared-pell-") as temp:
        tmp = Path(temp)
        def run(args):
            completed = subprocess.run(prefix + [str(a) for a in args],
                                       cwd=root, text=True, capture_output=True)
            require(completed.returncode == 0,
                    "Command failed:\n" + " ".join(map(str, args)) + "\n" +
                    completed.stdout + completed.stderr)
        rebuilt = tmp / "rebuilt"
        run([src / "build.py", "--output", rebuilt])
        run([src / "integer_export.py", "--input", rebuilt])
        filenames = [
            "raw_builder.json", "before_terminal.json", "equation.json",
            "expanded_polynomial.json", "elimination_trace.json",
            "envelope_certificate.json", "integer/equation.json",
            "integer/expanded_polynomial.json", "integer/guard_certificate.json"]
        for name in filenames:
            require((rebuilt / name).read_bytes() == (artifacts / name).read_bytes(),
                    "Rebuilt literal differs: " + name)
        receipts = {}
        for kind in ("affine", "terminal", "integer"):
            dest = tmp / (kind + ".json")
            run([tests / ("verify_" + kind + "_independent.py"),
                 artifacts, "--output", dest])
            receipts[kind] = json.loads(dest.read_text())
        dest = tmp / "semantics.json"
        run([tests / "audit_final_semantics.py",
             "--source-dir", src, "--artifacts", artifacts,
             "--source-proof-helper", tests / "audit_reductions.py",
             "--original-source", root / "provenance/inherited/original_direct_calculus.py",
             "--output", dest])
        semantic = json.loads(dest.read_text())
        literal = load_module("literal_print_check", tests / "verify_printed_equation.py")
        printed = literal.check(root)
        lemmas = load_module("lemma_tests", tests / "alternative_math_new_lemma_checks.py")
        lemma_results = {
            "factorial": lemmas.check_factorial(),
            "shared_pell": [lemmas.shared_pell(2, [1, 2]), lemmas.shared_pell(3, [2, 3])],
            "complete_shared_power": lemmas.complete_shared_power(),
            "shared_radix": lemmas.shared_radix()}
        powers = load_module("power_tests", tests / "alternative_math_power_fixtures.py")
        power_results = [powers.check(powers.certificate(n, k))
                         for n, k in [(1, 1), (2, 1), (1, 2)]]
        corruption_count = sum(len(r["corruption_controls"]) for r in receipts.values())
        require(corruption_count == 8, "Corruption-control inventory")
        result = {
            "status": "PASS", "optimized_python": not __debug__,
            "byte_exact_rebuilt_artifacts": len(filenames),
            "independent_audits": list(receipts),
            "rejected_corruption_controls": corruption_count,
            "literal_interface_rows_checked": semantic["literal_interface_rows_checked"],
            "printed_equation": printed,
            "natural": json.loads((artifacts / "equation.json").read_text())["metrics"],
            "integer": json.loads((artifacts / "integer/equation.json").read_text())["metrics"],
            "lemma_fixtures": lemma_results, "power_fixtures": power_results,
            "scope": "Exact finite verification and arithmetic controls; universal proof in report."}
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
