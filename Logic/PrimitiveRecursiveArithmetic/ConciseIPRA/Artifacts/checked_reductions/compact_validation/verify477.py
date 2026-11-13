"""Offline reproduction for the 477-byte guarded checker.

Run without arguments for all 454 subprocess invocations. --smoke performs
only a small portable run; --audit checks file integrity and source metrics.
No network, repository checkout, ZIP archive, or third-party package is used.
"""
import argparse
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORED = {
    tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
    tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER,
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def measure(source):
    tree = ast.parse(source)
    normalized = ast.unparse(tree) + "\n"
    significant = sum(
        token.type not in IGNORED
        for token in tokenize.generate_tokens(io.StringIO(normalized).readline)
    )
    return [significant, len(list(ast.walk(tree))), len(normalized.encode())]


def protected_zero(tree, depth=0):
    """The scope-header proof's necessary zero condition, not a grammar check."""
    if isinstance(tree, list):
        return any(protected_zero(child, depth + 5 - len(tree)) for child in tree)
    return type(tree) is int and tree == 0 and depth > 0 and depth % 2 == 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--smoke", action="store_true")
    mode.add_argument("--audit", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "fixture_manifest.json").read_text())
    for name, expected in manifest["source_files"].items():
        assert digest((ROOT / name).read_bytes()) == expected, name
    records = manifest["fixtures"]
    assert len(records) == manifest["fixture_count"] == 67
    for record in records:
        payload = (ROOT / record["path"]).read_bytes()
        assert digest(payload) == record["sha256"], record["path"]
        certificate = json.loads(payload)
        assert protected_zero(certificate[-1][0]) == record["protected_zero_in_goal"]
    control_source = (ROOT / "control478.py").read_text()
    candidate_source = (ROOT / "compact477.py").read_text()
    assert candidate_source == control_source.replace(
        "bool(m or 3 % len(a))", "any((m, 3 % len(a)))"
    )
    metrics = {"control": measure(control_source), "candidate": measure(candidate_source)}
    assert metrics == {"control": [271, 305, 478], "candidate": [273, 305, 477]}
    report = {
        "python": platform.python_version(),
        "mode": "audit" if args.audit else "smoke" if args.smoke else "full",
        "all_source_and_fixture_hashes_match": True,
        "exact_declared_source_change": True,
        "metrics": metrics,
        "results": [],
        "positive_floor_attacks": [],
        "executions": 0,
    }
    if args.smoke:
        selected = {
            "fixtures/compact_context/computation_zero_local.json",
            "fixtures/compact_context/guarded_induction_with_used_hypothesis_local.json",
            "fixtures/compact_context/false_float_capture.json",
            "fixtures/inherited_empty_auxiliary_boundary.json",
        }
        records = [record for record in records if record["path"] in selected]
        assert len(records) == len(selected)

    def run(program, certificate, optimized=False):
        command = [sys.executable] + (["-O"] if optimized else []) + [str(ROOT / program)]
        completed = subprocess.run(
            command, input=json.dumps(certificate), text=True,
            capture_output=True, timeout=5,
        )
        report["executions"] += 1
        return completed.returncode == 0 and completed.stdout == "ACCEPT\n"

    if not args.audit:
        for record in records:
            certificate = json.loads((ROOT / record["path"]).read_text())
            for optimized in (False, True):
                outcomes = {
                    "control": run("control478.py", certificate, optimized),
                    "candidate": run("compact477.py", certificate, optimized),
                }
                assert outcomes == record["expectations"][str(optimized).lower()], record["path"]
                assert not (outcomes["candidate"] and not outcomes["control"])
                report["results"].append({
                    "fixture": record["path"], "optimized": optimized, **outcomes,
                })
        for record in records:
            if record["path"] == "fixtures/inherited_empty_auxiliary_boundary.json":
                continue
            certificate = json.loads((ROOT / record["path"]).read_text())
            if run("compact477.py", certificate):
                for floor in (1, 2, 7):
                    attack = certificate[:-1] + [[certificate[-1][0], floor]]
                    accepted = run("compact477.py", attack)
                    assert not (accepted and record["protected_zero_in_goal"]), record["path"]
                    report["positive_floor_attacks"].append({
                        "fixture": record["path"], "floor": floor,
                        "protected_zero_in_goal": record["protected_zero_in_goal"],
                        "accepted": accepted,
                    })
        if not args.smoke:
            assert report["executions"] == 454
    report["summary"] = {
        "paired_cases": len(report["results"]),
        "candidate_accept_control_reject": sum(
            row["candidate"] and not row["control"] for row in report["results"]
        ),
        "control_accept_candidate_reject": sum(
            row["control"] and not row["candidate"] for row in report["results"]
        ),
        "positive_floor_accepted_with_protected_zero": sum(
            row["accepted"] and row["protected_zero_in_goal"]
            for row in report["positive_floor_attacks"]
        ),
    }
    output = ROOT / ("verification477_portable_" + report["mode"] + ".json")
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"mode": report["mode"], "metrics": metrics,
                      "executions": report["executions"], **report["summary"]}, indent=2))


if __name__ == "__main__":
    main()
