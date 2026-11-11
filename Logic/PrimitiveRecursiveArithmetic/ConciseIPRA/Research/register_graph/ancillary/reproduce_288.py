"""Reproduce source sizes and the retained canonical certificate suite.

The tests exercise finite executions. They are not a proof-assistant proof
of the inherited mathematics or the universal kernel simulation theorem.
"""

import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def measure(path):
    source = path.read_bytes()
    tree = ast.parse(source)
    normalized = (ast.unparse(tree) + "\n").encode()
    ignored = {tokenize.ENCODING, tokenize.NEWLINE, tokenize.NL,
               tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
               tokenize.ENDMARKER}
    tokens = sum(item.type not in ignored for item in
                 tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    return dict(raw_bytes=len(source), normalized_bytes=len(normalized),
                tokens=tokens, ast_nodes=sum(1 for _ in ast.walk(tree)),
                gzip9_normalized=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                source_sha256=hashlib.sha256(source).hexdigest())


def run(path, packet, optimized):
    command = [sys.executable, *(["-O"] if optimized else []), str(path)]
    result = subprocess.run(command, input=json.dumps(packet), text=True,
                            capture_output=True, timeout=20)
    return result.returncode == 0 and result.stdout == "ACCEPT\n"


def main():
    programs = {"new": ROOT / "checker_288.py",
                "reference": ROOT / "reference/code/checker_structure.py"}
    cases = json.loads((ROOT / "reference/tests/cases.json").read_text())
    results = []
    for optimized in (False, True):
        for name, path in programs.items():
            for case in cases:
                accepted = run(path, case["packet"], optimized)
                results.append(dict(checker=name, optimized=optimized,
                                    case=case["name"], expected=case["accept"],
                                    accepted=accepted, passed=accepted == case["accept"]))
    original = json.loads((ROOT / "reference/tests/reject_false_major_sentinel.json").read_text())
    for optimized in (False, True):
        for marker in (0, False, 0.0):
            packet = json.loads(json.dumps(original))
            packet[-2][0] = marker
            accepted = run(programs["new"], packet, optimized)
            results.append(dict(checker="new", optimized=optimized,
                                case="false_major_" + repr(marker), expected=False,
                                accepted=accepted, passed=not accepted))
    report = dict(python=sys.version, metrics=measure(programs["new"]),
                  reference_metrics=measure(programs["reference"]),
                  cases=len(cases), runs=len(results),
                  failures=[row for row in results if not row["passed"]])
    print(json.dumps(report, indent=2))
    if report["failures"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
