"""Reproduce the complete-module comparison and inherited fixture results."""
import ast
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize


ROOT = Path(__file__).resolve().parent
IGNORED = {
    tokenize.ENCODING,
    tokenize.ENDMARKER,
    tokenize.NEWLINE,
    tokenize.NL,
    tokenize.INDENT,
    tokenize.DEDENT,
    tokenize.COMMENT,
}


def metrics(path):
    tree = ast.parse(path.read_text(encoding="utf-8"))
    normalized = ast.unparse(tree) + "\n"
    return {
        "tokens": sum(
            token.type not in IGNORED
            for token in tokenize.generate_tokens(io.StringIO(normalized).readline)
        ),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "normalized_utf8_bytes": len(normalized.encode("utf-8")),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def git_blob_sha(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def main():
    provenance = json.loads((ROOT / "PROVENANCE.json").read_text())
    control = ROOT / "controls/checker271.py"
    if git_blob_sha(control.read_bytes()) != provenance["baseline_blob_sha"]:
        raise ValueError("Upstream control blob does not match provenance")
    for entry in provenance["fixtures"]:
        raw = (ROOT / entry["local_path"]).read_bytes()
        if git_blob_sha(raw) != entry["git_blob_sha"]:
            raise ValueError(f"Fixture blob mismatch: {entry['local_path']}")
        if hashlib.sha256(raw).hexdigest() != entry["sha256"]:
            raise ValueError(f"Fixture SHA-256 mismatch: {entry['local_path']}")

    programs = ["controls/checker271.py", "code/checker269.py"]
    results = {
        "python": sys.version,
        "metrics": {name: metrics(ROOT / name) for name in programs},
        "cases": [],
    }
    for fixture in sorted((ROOT / "tests").rglob("*.json")):
        expected = fixture.parent.name == "local"
        row = {
            "file": str(fixture.relative_to(ROOT)),
            "expected_accept": expected,
            "runs": [],
        }
        for optimized in (False, True):
            for program in programs:
                command = [sys.executable]
                if optimized:
                    command.append("-O")
                command.append(str(ROOT / program))
                process = subprocess.run(
                    command,
                    input=fixture.read_bytes(),
                    capture_output=True,
                    timeout=30,
                )
                accepted = (
                    process.returncode == 0 and process.stdout == b"ACCEPT\n"
                )
                row["runs"].append(
                    {
                        "program": program,
                        "optimized": optimized,
                        "accepted": accepted,
                        "expected_verdict_met": accepted == expected,
                    }
                )
        results["cases"].append(row)
    results["executions"] = sum(len(row["runs"]) for row in results["cases"])
    results["failures"] = [
        row["file"]
        for row in results["cases"]
        if not all(run["expected_verdict_met"] for run in row["runs"])
    ]
    (ROOT / "verification.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({
        "metrics": results["metrics"],
        "fixtures": len(results["cases"]),
        "executions": results["executions"],
        "failures": results["failures"],
    }, indent=2))
    if results["failures"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
