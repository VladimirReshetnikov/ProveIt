"""Offline checks of the two three-field acceptance modules and producers.

This harness is not imported by either measured checker. It tests genuine
canonical proofs and concrete malformed/capture/leak attacks. Finite tests
supplement the written soundness and canonical-completeness arguments.
"""
from pathlib import Path
import ast
import collections
import hashlib
import io
import json
import subprocess
import sys
import tokenize

from translate import to_four_fields, to_three_fields

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests" / "three_field"
PROGRAMS = {
    "global": ROOT / "code" / "checker_tokens.py",
    "local": ROOT / "code" / "checker_ast.py",
}
CONTROLS = {
    key: ROOT / "controls" / ("three_field_" + key + "_control.py")
    for key in PROGRAMS
}


def run(program, payload, optimized):
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    command.append(str(program))
    proc = subprocess.run(
        command, input=json.dumps(payload).encode(), capture_output=True, timeout=20
    )
    return proc.returncode == 0 and proc.stdout == b"ACCEPT\n"


def metric(path):
    source = path.read_bytes()
    normalized = ast.unparse(ast.parse(source)) + "\n"
    skip = {
        tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT, tokenize.NL,
        tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
    }
    return {
        "path": str(path.relative_to(ROOT)),
        "significant_tokens": sum(
            token.type not in skip
            for token in tokenize.generate_tokens(io.StringIO(normalized).readline)
        ),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "normalized_bytes": len(normalized.encode()),
        "sha256": hashlib.sha256(source).hexdigest(),
    }


checks = []
round_trips = []
actions = collections.Counter()
for protocol, program in PROGRAMS.items():
    for path in sorted((FIXTURES / protocol).glob("*.json")):
        data = json.loads(path.read_text())
        expanded = to_four_fields(data)
        regenerated, trace = to_three_fields(expanded, protocol)
        round_trips.append({
            "fixture": str(path.relative_to(ROOT)),
            "protocol": protocol,
            "same_packet_stream": regenerated == data,
            "consumed_instructions": len(trace["events"]),
        })
        actions.update(event["action"] for event in trace["events"])
        for optimized in (False, True):
            for label, checked_program, checked_data in (
                ("three_field", program, data),
                ("expanded_four_field", CONTROLS[protocol], expanded),
            ):
                accepted = run(checked_program, checked_data, optimized)
                checks.append({
                    "fixture": str(path.relative_to(ROOT)),
                    "protocol": protocol,
                    "implementation": label,
                    "optimized": optimized,
                    "expected": True,
                    "accepted": accepted,
                    "passed": accepted,
                })
    for path in sorted((FIXTURES / "adversarial").glob("*.json")):
        data = json.loads(path.read_text())
        for optimized in (False, True):
            accepted = run(program, data, optimized)
            checks.append({
                "fixture": str(path.relative_to(ROOT)),
                "protocol": protocol,
                "implementation": "three_field",
                "optimized": optimized,
                "expected": False,
                "accepted": accepted,
                "passed": not accepted,
            })

metrics = [metric(path) for path in PROGRAMS.values()]
metric_checks = [
    metrics[0]["significant_tokens"] == 249,
    metrics[0]["ast_nodes"] == 278,
    metrics[0]["normalized_bytes"] == 607,
    metrics[1]["significant_tokens"] == 255,
    metrics[1]["ast_nodes"] == 271,
    metrics[1]["normalized_bytes"] == 606,
]
result = {
    "python": sys.version,
    "standalone_cli_checks": len(checks),
    "failed_cli_checks": sum(not row["passed"] for row in checks),
    "canonical_round_trips": len(round_trips),
    "failed_round_trips": sum(not row["same_packet_stream"] for row in round_trips),
    "canonical_instruction_kinds": dict(actions),
    "metrics": metrics,
    "expected_metrics_match": all(metric_checks),
    "checks": checks,
    "round_trips": round_trips,
    "limits": [
        "Tests are finite; universal claims use the written proofs.",
        "Static-expansion acceptance is checked only for canonical compiled proofs.",
        "The selected no-major protocol can change raw computation supply contexts; exact all-input trace equivalence is not claimed.",
        "The compact programs assume the documented integer/list and guarded public-goal contract.",
    ],
}
(ROOT / "evidence" / "three_field_validation.json").write_text(
    json.dumps(result, indent=2) + "\n"
)
print(json.dumps({
    key: result[key] for key in (
        "standalone_cli_checks", "failed_cli_checks", "canonical_round_trips",
        "failed_round_trips", "canonical_instruction_kinds", "metrics",
        "expected_metrics_match",
    )
}, indent=2))
if result["failed_cli_checks"] or result["failed_round_trips"] or not all(metric_checks):
    raise SystemExit(1)
