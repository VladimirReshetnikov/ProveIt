"""Reproduce the return-reservation measurements and focused regression suite."""
import ast
import gzip
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
BASE = ROOT
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL, tokenize.NEWLINE,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def execute(path, data, optimized=False):
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    command.append(str(path))
    result = subprocess.run(command, input=data, capture_output=True, timeout=30)
    return {"accepted": result.returncode == 0 and result.stdout == b"ACCEPT\n",
            "exit_code": result.returncode,
            "exception": result.stderr.decode().splitlines()[-1] if result.stderr else ""}


def measure(path):
    source = (ast.unparse(ast.parse(path.read_bytes())) + "\n").encode()
    return {"program": path.name,
            "tokens": sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source.decode()).readline)),
            "ast": sum(1 for _ in ast.walk(ast.parse(source))),
            "bytes": len(source),
            "gzip9": len(gzip.compress(source, compresslevel=9, mtime=0))}


def main():
    spec = importlib.util.spec_from_file_location("translator", ROOT / "code/translate.py")
    translator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(translator)
    programs = [ROOT / n for n in ["code/checker_tokens.py", "code/checker_ast.py", "code/readable_stream.py"]]
    destination = ROOT / "fixtures/reserved"
    destination.mkdir(exist_ok=True)
    rows, translations = [], []
    for fixture in sorted((BASE / "fixtures/source").glob("*.jsonl")):
        original = execute(BASE / "controls/shared_ast262.py", fixture.read_bytes())
        if original["accepted"]:
            payload, stats = translator.translate(fixture.read_text())
            (destination / fixture.name).write_text(payload)
            translations.append({"fixture": fixture.name, **stats})
            cases = [("translated-positive", payload.encode(), True)]
            false_goal = "[0,[0]]\n" + "\n".join(payload.splitlines()[1:]) + "\n"
            cases.append(("false-public-goal", false_goal.encode(), False))
        else:
            cases = [("negative-control", fixture.read_bytes(), False)]
        for kind, payload, expected in cases:
            for program in programs:
                for optimized in (False, True):
                    rows.append({"fixture": fixture.name, "kind": kind,
                                 "program": program.name, "optimized": optimized,
                                 "expected": expected,
                                 **execute(program, payload, optimized)})

    # A valid guarded false D goal and an actual future witness. The third
    # line is a well-formed neutral packet; rejection must precede its read.
    attack = "[[[5,0,7],[5,0,5]]]\n[0,0,[-1]]\n[0,0,0]\n"
    (destination / "future_witness_before_major.jsonl").write_text(attack)
    boundary_checks = []
    for program in programs:
        lines = iter(attack.splitlines())
        reads = []

        def supplied_input():
            line = next(lines)
            reads.append(line)
            return line

        try:
            exec(compile(program.read_text(), str(program), "exec"),
                 {"input": supplied_input, "print": lambda *args: None})
            exception = "NONE"
        except Exception as exc:
            exception = type(exc).__name__
        boundary_checks.append({"program": program.name, "exception": exception,
                                "json_lines_consumed": len(reads),
                                "neutral_major_packet_unread": len(reads) == 2})

    failures = [r for r in rows if r["accepted"] != r["expected"]]
    failures += [r for r in boundary_checks if r["exception"] != "TypeError" or not r["neutral_major_packet_unread"]]
    used = next(r for r in translations if "induction_with_used" in r["fixture"])
    if not used["used_hypotheses"].get("progress", 0):
        failures.append({"error": "The induction fixture did not use its progressive assumption"})
    report = {"python": sys.version, "metrics": [measure(p) for p in programs],
              "executions": len(rows), "failures": failures,
              "scope_boundary_checks": boundary_checks,
              "translations": translations, "results": rows,
              "proof_status": "Finite regression evidence; universal correspondence is a separate written argument."}
    (ROOT / "evidence/stream_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"metrics": report["metrics"], "executions": len(rows),
                      "failures": failures, "scope_boundary_checks": boundary_checks,
                      "used_induction": {k: v for k, v in used.items() if k != "allocations"}}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
