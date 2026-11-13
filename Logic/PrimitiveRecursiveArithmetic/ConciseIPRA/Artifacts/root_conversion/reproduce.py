"""Reproduce delivered checks in a temporary directory; preserve the package."""

import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tokenize

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def measure(path):
    source = path.read_bytes()
    tree = ast.parse(source)
    normalized = (ast.unparse(tree) + "\n").encode()
    excluded = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
                tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {
        "significant_tokens": sum(
            t.type not in excluded
            for t in tokenize.tokenize(io.BytesIO(normalized).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "normalized_bytes": len(normalized),
        "raw_bytes": len(source),
        "gzip9_normalized_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "gzip9_raw_bytes": len(gzip.compress(source, compresslevel=9, mtime=0)),
        "source_sha256": hashlib.sha256(source).hexdigest(),
    }


def check_manifest():
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        return {"present": False, "checked_files": 0}
    count = 0
    for line in manifest.read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = ROOT / name
        require(path.is_file(), "missing file: " + name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                "hash mismatch: " + name)
        count += 1
    return {"present": True, "checked_files": count}


def public_rejections(code):
    zero = ["z"]
    eq = ["=", zero, zero]
    cases = {
        "null_record": None,
        "missing_proof": {"goal": eq},
        "extra_field": {"goal": eq, "proof": ["refl", zero], "extra": 0},
        "free_goal_variable": {"goal": ["=", 0, 0], "proof": ["refl", 0]},
        "boolean_variable": {"goal": eq, "proof": ["refl", False]},
        "wrong_goal": {"goal": ["=", zero, ["s", zero]], "proof": ["refl", zero]},
        "unknown_rule": {"goal": eq, "proof": ["oracle", eq]},
        "bad_arity": {"goal": eq, "proof": ["refl", zero, zero]},
        "false_root_step": {"goal": eq, "proof": ["root", ["s", zero], ["refl", zero]]},
        "negative_hypothesis": {"goal": eq, "proof": ["hyp", -1]},
        "bad_term_tag": {"goal": eq, "proof": ["refl", ["eval", 0]]},
        "empty_proof": {"goal": eq, "proof": []},
    }
    results = []
    for module in ("checker.py", "checker_seven.py"):
        for optimized in (False, True):
            for name, certificate in cases.items():
                command = [sys.executable, "-B"] + (["-O"] if optimized else [])
                command += [str(code / module)]
                result = subprocess.run(command, input=json.dumps(certificate).encode(),
                                        capture_output=True, timeout=15)
                require(result.returncode != 0 and result.stdout == b"REJECT\n",
                        f"unexpected public result: {module}, {optimized}, {name}")
                results.append({"checker": module, "optimized": optimized,
                                "case": name, "rejected": True})
    return results


def main():
    receipt = {"python": sys.version, "manifest": check_manifest()}
    receipt["measurements"] = {
        name: measure(ROOT / "code" / name)
        for name in ("checker_seven.py", "checker.py")
    }
    receipt["baseline_measurements"] = {
        name: measure(ROOT / "reference" / name)
        for name in ("baseline_checker_tokens.py", "baseline_checker_ast.py",
                     "baseline_checker_bytes.py")
    }
    audit = json.loads((ROOT / "evidence/baseline_audit.json").read_text())
    for witness in audit["witnesses"]:
        name = "baseline_" + witness["path"].rsplit("/", 1)[-1]
        observed = receipt["baseline_measurements"][name]
        require(observed["source_sha256"] == witness["source_sha256"],
                "baseline source changed: " + name)
        if sys.version_info[:3] == (3, 12, 14):
            for key, recorded in (("significant_tokens", "significant_tokens"),
                                  ("ast_nodes", "ast_nodes"),
                                  ("normalized_bytes", "normalized_utf8_bytes"),
                                  ("gzip9_normalized_bytes", "gzip9_normalized_bytes")):
                require(observed[key] == witness[recorded], "baseline metric mismatch: " + key)
    with tempfile.TemporaryDirectory(prefix="ipra-root-reproduce-") as temp:
        code = Path(temp) / "code"
        shutil.copytree(ROOT / "code", code,
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        receipt["certificate_suites"] = []
        for seven in (False, True):
            command = [sys.executable, "-B", str(code / "verify.py")]
            if seven:
                command.append("--seven")
            result = subprocess.run(command, capture_output=True, text=True, timeout=45)
            require(result.returncode == 0, result.stderr + result.stdout)
            generated = json.loads(result.stdout)
            receipt["certificate_suites"].append({
                "rules": 7 if seven else 8,
                "positive_constructions": len(generated["positive_cases"]),
                "negative_controls": len(generated["negative_cases"]),
                "closed_cli_runs": len(generated["cli"]),
                "checker_sha256": generated["checker_sha256"],
            })
        receipt["public_rejections"] = public_rejections(code)
    receipt["status"] = "all checks passed"
    receipt["proof_status"] = "finite executable evidence; metatheorems are written proofs"
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
