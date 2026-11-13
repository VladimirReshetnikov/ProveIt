"""Reproduce the delivered evidence in a disposable copy; no network needed."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import shutil
import subprocess
import sys
import tempfile
import tokenize

ROOT = Path(__file__).resolve().parent


def measure(path):
    normalized = ast.unparse(ast.parse(path.read_text())) + "\n"
    data = normalized.encode("utf-8")
    skip = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
            tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
            tokenize.ENDMARKER}
    return {
        "tokens": sum(t.type not in skip for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "normalized_bytes": len(data),
        "gzip9_bytes": len(gzip.compress(data, compresslevel=9, mtime=0)),
        "normalized_sha256": hashlib.sha256(data).hexdigest(),
    }


def main():
    ledger = ROOT / "MANIFEST.sha256"
    if ledger.exists():
        entries = ledger.read_text().splitlines()
        for entry in entries:
            digest, name = entry.split("  ", 1)
            actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            if actual != digest:
                raise SystemExit(f"Manifest mismatch: {name}")
        print(f"Manifest verified: {len(entries)} files")
    measurements = {}
    for folder in (ROOT / "code", ROOT / "reference/controls"):
        for path in sorted(folder.glob("*.py")):
            measurements[str(path.relative_to(ROOT))] = measure(path)
    print(json.dumps({"python": sys.version, "metrics": measurements}, indent=2))
    with tempfile.TemporaryDirectory(prefix="ipra-reproduction-") as temporary:
        work = Path(temporary) / "package"
        shutil.copytree(ROOT, work)
        for script in ("tests/translate.py", "tests/verify.py"):
            process = subprocess.run([sys.executable, str(work / script)],
                                     text=True, capture_output=True, timeout=120)
            if process.returncode:
                print(process.stdout)
                print(process.stderr, file=sys.stderr)
                raise SystemExit(process.returncode)
        translations = json.loads((work / "evidence/translation_results.json").read_text())
        verification = json.loads((work / "evidence/verification.json").read_text())
        print(json.dumps({
            "translated_proofs": len(translations),
            "translations_accepted": sum(x["accepted"] for x in translations),
            "isolated_process_runs": verification["executions"],
            "unexpected_outcomes": len(verification["unexpected"]),
        }, indent=2))
        if verification["unexpected"]:
            raise SystemExit("Verification failed")


if __name__ == "__main__":
    main()
