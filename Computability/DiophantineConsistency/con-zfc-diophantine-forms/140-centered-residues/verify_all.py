#!/usr/bin/env python3
"""Offline release verification, without modifying the delivered package.

Runs exact algebra in ordinary and optimized Python, checks all coefficient
payloads, reconstructs selected outputs, binds the TeX appendices to JSON,
and verifies the release manifest. These finite checks do not replace the
unbounded mathematical proofs or the inherited syntactic calibration.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(value, message):
    if not value:
        raise ValueError(message)


def manifest():
    path = ROOT / "MANIFEST.sha256"
    require(path.is_file(), "Missing release manifest")
    listed = set()
    for line in path.read_text().splitlines():
        digest, name = line.split("  ", 1)
        relative = Path(name)
        require(not relative.is_absolute() and ".." not in relative.parts,
                "Unsafe manifest entry")
        require(name not in listed, "Duplicate manifest entry: " + name)
        listed.add(name)
        item = ROOT / relative
        require(item.is_file(), "Missing release file: " + name)
        require(hashlib.sha256(item.read_bytes()).hexdigest() == digest,
                "Release hash mismatch: " + name)
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*")
              if p.is_file() and p.name != "MANIFEST.sha256"
              and "__pycache__" not in p.parts and p.suffix != ".pyc"}
    # A retained component manifest is itself a release file.
    actual |= {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("MANIFEST.sha256")
               if p != path}
    require(listed == actual,
            "Release census mismatch: missing=%r extra=%r" %
            (sorted(listed - actual), sorted(actual - listed)))
    return "PASS"


def run(script, args=(), optimized=False):
    command = [sys.executable, "-B"]
    if optimized:
        command.append("-O")
    command += [str(script), *map(str, args)]
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    process = subprocess.run(command, cwd=ROOT, env=env, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(process.returncode == 0,
            "Check failed: %s\n%s\n%s" % (script.name, process.stdout, process.stderr))
    try:
        result = json.loads(process.stdout)
    except json.JSONDecodeError:
        result = {"stdout": process.stdout}
    return result


def all_checks():
    result = {
        "status": "PASS",
        "release_manifest": manifest(),
        "scope": "Exact finite algebra and artifact identity. The ordinary proofs establish the unbounded arithmetic; the named inherited sources supply the logical calibration.",
        "report_inputs": run(ROOT / "render_report_inputs.py", ["--check"]),
        "modes": [],
    }
    # The compact producer writes its receipt beside itself. Use temporary
    # copies so verification cannot invalidate the sealed distribution.
    with tempfile.TemporaryDirectory(prefix="conzfc_complete_release_") as temporary:
        scratch = Path(temporary)
        for optimized in (False, True):
            compact = scratch / ("compact_optimized" if optimized else "compact_normal")
            shutil.copytree(ROOT / "compact", compact)
            arithmetic_args = [] if optimized else ["--rebuild"]
            item = {
                "optimized": optimized,
                "arithmetic": run(ROOT / "arithmetic/verify.py", arithmetic_args, optimized),
                "signed_independent": run(ROOT / "reviews/check_signed_radius_independent.py",
                                          ["--root", ROOT / "arithmetic"], optimized),
                "compact": run(compact / "verify.py", optimized=optimized),
                "compact_independent": run(compact / "independent_verify.py", optimized=optimized),
                "coefficient_reconstruction": run(compact / "rebuild_coefficients.py", optimized=optimized),
            }
            run(compact / "build.py", optimized=optimized)
            filenames = ["equation_XY_V2.json", "equation_XY_bV.json",
                         "equation_q4_V2.json", "equation_q4_bV.json", "build_metrics.json"]
            for name in filenames:
                require((compact / name).read_bytes() == (ROOT / "compact" / name).read_bytes(),
                        "Compact rebuild differs: " + name)
            item["compact_rebuilt_identical_files"] = filenames
            result["modes"].append(item)
    require(manifest() == "PASS", "Verification changed the release")
    result["release_unchanged_after_verification"] = True
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path,
                        help="Optional new receipt; use a path outside this sealed release")
    parser.add_argument("--manifest-only", action="store_true")
    args = parser.parse_args()
    result = ({"status": "PASS", "release_manifest": manifest()}
              if args.manifest_only else all_checks())
    if args.receipt:
        require(ROOT not in args.receipt.resolve().parents,
                "Write the new receipt outside this sealed release")
        args.receipt.write_text(json.dumps(result, indent=2) + "\n")
    summary = {k: v for k, v in result.items() if k not in ("modes",)}
    if "modes" in result:
        summary["checked_modes"] = ["normal", "optimized"]
        summary["arithmetic_profiles"] = 6
        summary["compact_circuits"] = 4
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
