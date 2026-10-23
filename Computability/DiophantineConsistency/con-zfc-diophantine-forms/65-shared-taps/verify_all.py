#!/usr/bin/env python3
"""Replay the delivered finite certificates without modifying the release.

Python 3 standard library only. This checks finite identities and literal data;
the universal solvability equivalences are proved in report.pdf and the named
inherited mathematical dependencies. No refutation search is performed.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def check_manifest():
    manifest = HERE / "MANIFEST.sha256"
    require(manifest.is_file(), "Missing MANIFEST.sha256")
    records = []
    for line in manifest.read_text(encoding="utf-8").splitlines():
        expected, relative = line.split("  ", 1)
        path = HERE / relative
        require(path.resolve().is_relative_to(HERE), "Unsafe manifest path")
        require(path.is_file(), "Missing release file: " + relative)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == expected, "Release hash mismatch: " + relative)
        records.append(relative)
    require(len(records) == len(set(records)), "Repeated manifest entry")
    return {"status": "PASS", "files": len(records)}


def run_json(component, script):
    flags = ["-O"] if sys.flags.optimize else []
    result = subprocess.run(
        [sys.executable, *flags, str(component / script)],
        cwd=component, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if result.returncode:
        raise RuntimeError(script + "\n" + result.stdout + "\n" + result.stderr)
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError("Non-JSON output from " + script + "\n" + result.stdout) from error


def audit_nine(work):
    source = HERE / "nine"
    binding = read_json(source / "coefficients/COEFFICIENT_BINDING.json")
    rebuilt = run_json(work, "coefficients/build_coefficients.py")
    original_ports = {record["port"]: record["sha256"] for record in binding["files"]}
    rebuilt_ports = {record["port"]: record["sha256"] for record in rebuilt["files"]}
    require(original_ports == rebuilt_ports, "Native source-31 coefficient reconstruction")
    finite = run_json(work, "verify.py")
    require(finite["status"] == "PASS", "Nine-variable component")
    return {
        "native_tuple_reconstructed": True,
        "native_port_raw_hashes": rebuilt_ports,
        "finite_checks": finite,
    }


def audit_pell(work):
    result = run_json(work, "verify_all.py")
    require(result["status"] == "PASS", "Pell component")
    return result


def audit_sun(work):
    provenance = read_json(work / "PROVENANCE.json")
    for record in provenance["files"]:
        actual = hashlib.sha256((work / record["path"]).read_bytes()).hexdigest()
        require(actual == record["sha256"], "Sun provenance: " + record["path"])
    compared = ["generated/sun10.json", "generated/METRICS.json"]
    expected = {name: (work / name).read_bytes() for name in compared}
    run_json(work, "build.py")
    for name, raw in expected.items():
        require((work / name).read_bytes() == raw, "Sun byte-identical rebuild: " + name)
    result = run_json(work, "verify.py")
    require(result["status"] == "PASS", "Sun component")
    return {"byte_identical_rebuilds": compared, "finite_checks": result}


def cross_component_checks():
    provenance = read_json(HERE / "PROVENANCE.json")
    for record in provenance["comparison_sources"]:
        raw = (HERE / record["local"]).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == record["sha256"], "Comparison source SHA256")
        git_blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        require(git_blob == record["expected_git_blob_sha1"], "Comparison source Git blob")
    for name in ["source_system65.json", "layout.json", "kernels.json"]:
        require(
            read_json(HERE / "nine/data" / name) == read_json(HERE / "sun/data" / name),
            "Shared source data differ: " + name,
        )
    for port in ["beta", "K", "MC", "MF_source"]:
        relative = "coefficients/payloads/" + port + ".bin.gz"
        nine = gzip.decompress((HERE / "nine" / relative).read_bytes())
        sun = gzip.decompress((HERE / "sun" / relative).read_bytes())
        require(nine == sun, "Source-31 native port differs: " + port)
    return {
        "status": "PASS",
        "shared_source_syntax": True,
        "shared_primary_layout_and_kernels": True,
        "all_four_source31_ports_identical": True,
        "source44_tuple_kept_separate": True,
        "comparison_sources_authenticated": len(provenance["comparison_sources"]),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest-only", action="store_true", help="check release hashes only")
    parser.add_argument(
        "--skip-manifest", action="store_true",
        help="maintainer option for preparing a new release before writing its manifest",
    )
    args = parser.parse_args()
    require(not (args.manifest_only and args.skip_manifest), "Conflicting manifest options")
    if not args.skip_manifest:
        integrity = check_manifest()
    if args.manifest_only:
        print(json.dumps(integrity, indent=2))
        return
    shared = cross_component_checks()
    jobs = {"nine": audit_nine, "pell": audit_pell, "sun": audit_sun}
    with tempfile.TemporaryDirectory(prefix="conzfc_release_") as temporary:
        temporary = Path(temporary)
        for component in jobs:
            shutil.copytree(
                HERE / component, temporary / component,
                ignore=shutil.ignore_patterns("__pycache__", "*.pyc"),
            )
        with ThreadPoolExecutor(max_workers=3) as pool:
            futures = {
                name: pool.submit(audit, temporary / name)
                for name, audit in jobs.items()
            }
            results = {name: future.result() for name, future in futures.items()}
    receipt = {
        "status": "PASS",
        "scope": "Finite release replay; universal solvability proofs and inherited interfaces are in the article.",
        "repository_commit": "beb0192cb8dc36f78c369c080f2adfbc1887a486",
        "assertions_disabled": bool(sys.flags.optimize),
        "cross_component_checks": shared,
        "components": results,
    }
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
