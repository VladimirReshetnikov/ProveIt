"""Reproduce the delivered evidence without any network access."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def measure(path):
    text = ast.unparse(ast.parse(path.read_text())) + "\n"
    ignored = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER,
               tokenize.COMMENT}
    return {
        "path": path.relative_to(ROOT).as_posix(),
        "tokens": sum(t.type not in ignored for t in
                      tokenize.generate_tokens(io.StringIO(text).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(text))),
        "normalized_bytes": len(text.encode()),
        "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def run(args):
    result = subprocess.run([sys.executable, *args], cwd=ROOT,
                            check=True, text=True, capture_output=True)
    return json.loads(result.stdout)


def main():
    manifest = ROOT / "MANIFEST.sha256"
    verified = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected, name = line.split("  ", 1)
            actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            if actual != expected:
                raise SystemExit("Hash mismatch: " + name)
            verified += 1
    result = {
        "python_version": sys.version.split()[0],
        "manifest_files_verified": verified,
        "candidate_verification": run(["code/verify.py"]),
        "independent_audit": run(["validation/h3_independent_audit.py",
                                  "code", "h3_seed_checker.py"]),
        "incumbent_measurements": [
            measure(p) for p in sorted((ROOT / "reference/frontier").rglob("*.py"))
        ],
        "global_frontier_target_achieved": False,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
