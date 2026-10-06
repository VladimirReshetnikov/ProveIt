#!/usr/bin/env python3
"""Verify all package hashes, optionally re-run checks or fully replay the build."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True

from package_tools import (PAYLOAD_FILES, SOURCE_FILES, REPORT, PackageError,
                           deterministic_environment, digest, extract_zip, require,
                           verify_directory)


def run_checks_again(source, workspace, timeout):
    destination = workspace/"check-source"
    destination.mkdir()
    for name in SOURCE_FILES:
        path = destination/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes((source/name).read_bytes())
    saved = json.loads((source/"verification.json").read_bytes())
    flags = ["--extended"] if saved["mode"] == "extended" else []
    from build_package import python_command
    outputs = []
    for optimize in (False, True):
        result = subprocess.run(python_command(destination/"companion/run_checks.py", flags, optimize),
                                cwd=destination, env=deterministic_environment(),
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
        require(result.returncode == 0, "replayed checks failed: "+result.stderr.decode(errors="replace"))
        outputs.append(json.loads(result.stdout))
    require(outputs[0] == outputs[1], "normal and -O results differ")
    for name in ("schema", "mode", "passed", "exact", "symbolic", "guard_self_check"):
        require(outputs[0][name] == saved[name], f"stored and replayed exact check differs: {name}")
    return {"exact_checks_replayed": True, "normal_and_optimized_equal": True,
            "floating_diagnostics": "recomputed, but not byte-compared across libm implementations"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="Report174 directory or Report174.zip")
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--checks-only", action="store_true", help="also rerun exact/symbolic checks; no TeX needed")
    action.add_argument("--replay", action="store_true", help="rebuild twice-compiled PDF and ZIP in isolation; compare all payload bytes")
    parser.add_argument("--timeout", type=int, default=300, help="per-command limit, seconds (1..3600)")
    args = parser.parse_args()
    try:
        require(1 <= args.timeout <= 3600, "timeout must be in 1..3600")
        with tempfile.TemporaryDirectory(prefix="Report174-verify-") as temporary:
            workspace = Path(temporary)
            if args.package.is_file():
                source = extract_zip(args.package, workspace/"extracted")
            else:
                source = args.package.resolve()
            manifest = verify_directory(source)
            result = {"sha256_verified": True, "verified_payload_files": len(manifest["files"]),
                      "integrity_scope": "hash consistency, not publisher authentication"}
            if args.checks_only:
                result.update(run_checks_again(source, workspace, args.timeout))
            if args.replay:
                from build_package import build
                info = json.loads((source/"build_info.json").read_bytes())
                built = build(source, workspace/"replay", info["verification_mode"] == "extended", args.timeout)
                rebuilt = Path(built["package"])
                differences = [name for name in (*PAYLOAD_FILES, "manifest.json")
                               if (source/name).read_bytes() != (rebuilt/name).read_bytes()]
                require(not differences, "replay differs in "+", ".join(differences)+
                        "; byte replay needs the recorded Python/libm/TeX/fonts/zlib toolchain")
                if args.package.is_file():
                    require(digest(args.package) == digest(built["zip"]), "replayed ZIP bytes differ")
                result.update({"full_build_replayed": True, "all_payload_bytes_identical": True,
                               "replayed_zip_sha256": built["zip_sha256"]})
            print(json.dumps(result, indent=2, sort_keys=True))
    except (PackageError, OSError, subprocess.SubprocessError, ValueError, KeyError) as exc:
        print(f"package verification failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
