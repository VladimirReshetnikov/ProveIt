"""Reproduce fixed CLI verdicts for the two reordered standalone checkers.

No checker imports this file. Cases are frozen from ProveIt commit
8662bc0a00f4e77e482f7d141d7a4f919f70f9aa, Research/coverage_and_kernel.
"""
from pathlib import Path
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def accepts(path, packet, optimized=False):
    result = subprocess.run(
        [sys.executable] + (["-O"] if optimized else []) + [str(path)],
        input=packet, text=True, capture_output=True, timeout=15,
    )
    return result.returncode == 0 and result.stdout == "ACCEPT\n"


def main():
    cases = json.loads((ROOT / "tests/cases.json").read_text())
    boundary = [
        ("", "empty_input", False), ("{}", "object_input", False),
        ("null", "null_input", False), ("true", "boolean_input", False),
        ("42", "number_input", False), ('"x"', "string_input", False),
        ('["x"]', "nonempty_string_goal", False),
        ("[[]]", "empty_array_truth", True),
        ("[0]", "scalar_fake_truth", False),
        ("[[0,[0]]]", "false_equation", False),
        ("[[[-0.5],0]]", "free_fractional_parameter", False),
        ("[[true,0,0,0],[0,[0]]]", "malformed_packet", False),
    ]
    rows = []
    for profile in ("ast", "bytes"):
        for directory in ("reference", "code"):
            path = ROOT / directory / f"checker_{profile}.py"
            inputs = [(json.dumps(x["packet"]), x["name"], x["accept"]) for x in cases]
            inputs += boundary
            # The generic iterable profile already accepts these two truth aliases.
            inputs += [('[""]', "empty_string_alias", profile == "ast"),
                       ('[{}]', "empty_object_alias", profile == "ast")]
            for packet, name, expected in inputs:
                for optimized in (False, True):
                    actual = accepts(path, packet, optimized)
                    rows.append({"program": str(path.relative_to(ROOT)), "case": name,
                                 "optimized": optimized, "expected": expected,
                                 "accepted": actual, "ok": actual == expected})
    controls = []
    with tempfile.TemporaryDirectory() as td:
        specs = [
            ("mutable_context", "ast", "g=([],)", "g=[[]]", "context_leak_counterexample"),
            ("wrong_induction_selector", "bytes", "len(a) % 2 == u",
             "len(a) % 2 == s", "compound_source_attack"),
        ]
        for name, profile, old, new, case in specs:
            source = (ROOT / "code" / f"checker_{profile}.py").read_text()
            if source.count(old) != 1:
                raise ValueError(name + ": unexpected source")
            path = Path(td) / (name + ".py")
            path.write_text(source.replace(old, new))
            packet = json.dumps(next(x["packet"] for x in cases if x["name"] == case))
            for optimized in (False, True):
                actual = accepts(path, packet, optimized)
                controls.append({"mutation": name, "case": case, "optimized": optimized,
                                 "accepted_false_proof": actual, "ok": actual})
        source = (ROOT / "code/checker_bytes.py").read_text().splitlines()
        index = next(i for i, line in enumerate(source) if line.strip().startswith("h = "))
        if source[index + 1].strip() != "k -= 1":
            raise ValueError("unexpected allocation order")
        source[index], source[index + 1] = source[index + 1], source[index]
        path = Path(td) / "allocation_before_witness.py"
        path.write_text("\n".join(source) + "\n")
        packet = json.dumps(next(x["packet"] for x in cases if x["name"] == "future_witness_capture"))
        for optimized in (False, True):
            actual = accepts(path, packet, optimized)
            controls.append({"mutation": "allocation_before_witness", "case": "future_witness_capture",
                             "optimized": optimized, "accepted_false_proof": actual, "ok": actual})
    summary = {"inherited_cases": len(cases), "boundary_cases": len(boundary) + 2,
               "cli_runs": len(rows), "mutation_runs": len(controls),
               "mismatches": sum(not r["ok"] for r in rows + controls),
               "finite_evidence_only": True}
    result = {"summary": summary, "results": rows, "mutation_controls": controls}
    (ROOT / "tests/results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    if summary["mismatches"]:
        print(json.dumps([r for r in rows + controls if not r["ok"]], indent=2))
        raise SystemExit(1)


if __name__ == "__main__":
    main()
