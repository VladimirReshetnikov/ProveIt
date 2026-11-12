"""Reproduce complete-module measurements and packet-translation regression tests."""

import ast
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path

from translate import group, flatten


ROOT = Path(__file__).resolve().parent
IGNORED = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def measure(path):
    raw = path.read_bytes()
    source = ast.unparse(ast.parse(raw)) + "\n"
    return {
        "path": str(path.relative_to(ROOT)),
        "significant_tokens": sum(
            token.type not in IGNORED
            for token in tokenize.generate_tokens(io.StringIO(source).readline)
        ),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(source))),
        "normalized_bytes": len(source.encode("utf-8")),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }


def run(path, certificate):
    result = subprocess.run(
        [sys.executable, str(path)], input=json.dumps(certificate).encode(),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5,
    )
    return result.returncode == 0 and result.stdout.strip() == b"ACCEPT"


def main():
    cases = json.loads((ROOT / "fixtures/cases.json").read_text())
    compact_control = ROOT / "code/control_tokens.py"
    compact_candidate = ROOT / "code/checker_grouped.py"
    strict_control = ROOT / "code/control_tokens_strict.py"
    strict_candidate = ROOT / "code/checker_grouped_strict.py"
    rows = []
    for case in cases:
        original = json.loads((ROOT / "fixtures/flat" / case["name"]).read_text())
        grouped = json.loads((ROOT / "fixtures/grouped" / case["name"]).read_text())
        assert group(original) == grouped, case["name"]
        control_accepts = run(compact_control, original)
        grouped_accepts = run(compact_candidate, grouped)
        strict_control_accepts = run(strict_control, original)
        strict_grouped_accepts = run(strict_candidate, grouped)
        assert control_accepts == grouped_accepts == case["expected"], case["name"]
        assert strict_control_accepts == strict_grouped_accepts, case["name"]
        if grouped_accepts:
            assert run(compact_control, flatten(grouped)), case["name"]
        rows.append({
            "name": case["name"], "expected_compact": case["expected"],
            "compact_control": control_accepts,
            "compact_grouped": grouped_accepts,
            "strict_control": strict_control_accepts,
            "strict_grouped": strict_grouped_accepts,
        })
    accepted = next(
        json.loads((ROOT / "fixtures/flat" / case["name"]).read_text())
        for case, row in zip(cases, rows) if row["strict_control"]
    )
    for label, extra in [("boolean", True), ("float", 0.0),
                         ("null", None), ("string", "unused"),
                         ("object", {})]:
        original = [extra] + accepted
        grouped = group(original)
        assert not run(strict_control, original), label
        assert not run(strict_candidate, grouped), label
        rows.append({"name": "strict_unused_" + label,
                     "strict_control": False, "strict_grouped": False})
    metrics = [measure(p) for p in [compact_control, compact_candidate,
                                  strict_control, strict_candidate]]
    result = {
        "python": platform.python_version(),
        "normalization": "ast.unparse plus one final LF; complete modules",
        "metrics": metrics,
        "inherited_compact_coordinate_envelope": {
            "significant_tokens": 251, "ast_nodes": 275,
            "normalized_bytes": 502,
        },
        "candidate_beats_only_token_coordinate": True,
        "fixture_cases": rows,
        "all_checks_passed": True,
        "scope": "Finite tests supplement the exact regrouping proof; they are not a proof of the inherited arithmetic bridge.",
    }
    (ROOT / "evidence/results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"metrics": metrics, "checks": len(rows),
                      "all_checks_passed": True}, indent=2))


if __name__ == "__main__":
    main()
