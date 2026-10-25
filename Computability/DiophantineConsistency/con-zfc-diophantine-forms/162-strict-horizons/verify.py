#!/usr/bin/env python3
"""Verify the released finite equations and optionally reconstruct them.

Python standard library only; offline and read-only unless --receipt is used.
This does not constitute a proof-assistant verification of the unbounded
number-theoretic arguments or the inherited logical calibration.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
FLAGS = ["-B"] + (["-O"] if sys.flags.optimize else [])
SOURCE_FILES = [
    "raw_source.json", "mutation.json", "factored_source.json",
    "factorization_certificate.json", "projected.json",
    "projection_certificate.json", "equation.json", "expanded_polynomial.json",
    "translation_certificate.json", "METRICS.json",
]
ENDPOINT_FILES = [
    "equation.json", "expanded_polynomial.json", "METRICS.json", "certificate.json",
]


def run(relative, *arguments):
    process = subprocess.run(
        [sys.executable, *FLAGS, str(ROOT / relative), *map(str, arguments)],
        cwd=ROOT, capture_output=True, text=True,
    )
    if process.returncode:
        raise RuntimeError(relative + " failed:\n" + process.stdout + "\n" + process.stderr)
    return json.loads(process.stdout)


def manifest_check():
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        raise ValueError("MANIFEST.sha256 is absent; use --skip-manifest while editing")
    checked = 0
    for line in manifest.read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = (ROOT / name).resolve()
        if ROOT not in path.parents:
            raise ValueError("Manifest path escapes package")
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError("Manifest mismatch: " + name)
        checked += 1
    return {"status": "PASS", "checked_files": checked}


def compare(fresh, stored, files):
    for name in files:
        if (fresh / name).read_bytes() != (stored / name).read_bytes():
            raise ValueError("Reconstruction differs: " + str(stored / name))
    return len(files)


def rebuild():
    with tempfile.TemporaryDirectory(prefix="conzfc-strict-rebuild-") as temporary:
        target = Path(temporary)
        source = target / "source"
        run("code/build_strict_source.py", "--output", source)
        count = compare(source, ROOT / "direct/source", SOURCE_FILES)
        run("code/build_endpoints.py", "--source", source, "--output", target)
        for name in ("principal236", "dense235"):
            count += compare(target / name, ROOT / "direct" / name, ENDPOINT_FILES)
        check = run("code/check_endpoints.py", "--source", source, "--output", target)
    return {"status": "PASS", "byte_identical_direct_json_files": count,
            "fresh_endpoint_audit": check["status"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    parser.add_argument("--skip-parent", action="store_true",
                        help="skip rechecking the retained parent dependency tree")
    parser.add_argument("--skip-manifest", action="store_true")
    parser.add_argument("--manifest-only", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    result = {"status": "PASS", "optimized_python": bool(sys.flags.optimize)}
    if not args.manifest_only:
        result["source_edit"] = run("code/check_source_edit.py")
        result["power_interface"] = run("code/check_power_interface.py")
        result["direct_algebra"] = run("code/check_endpoints.py")
        result["readable_exports"] = run("code/export_equations.py", "--check")
        result["compact_exact_algebra"] = run("compact/verify.py")
        result["compact_independent_formula_review"] = run("review/check_compact_independent.py")
        result["compact_reconstruction"] = run("compact/build.py", "--check")
        result["fixed_coefficient_reconstruction"] = run(
            "compact/upstream_lucas/parent/rebuild_coefficients.py")
        result["cofinal_pell_experiment"] = run(
            "experiments/cofinal_pell/verify_pell_generator.py")
        if not args.skip_parent:
            result["retained_parent"] = run(
                "sources/factorial_free/verify.py", "--skip-manifest")
        if args.rebuild:
            result["reconstruction"] = rebuild()
    if not args.skip_manifest:
        result["manifest"] = manifest_check()
    result["scope"] = (
        "Exact finite polynomial data, source identities, transformation "
        "certificates, coefficient payloads, readable exports and checksums. "
        "Unbounded arithmetic proofs and inherited logical/Pell calibration "
        "are stated separately in report/main.tex and retained proof sources. "
        "No full Lean/Rocq or internal-ZFC proof object is supplied."
    )
    output = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
