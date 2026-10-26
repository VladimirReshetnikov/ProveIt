#!/usr/bin/env python3
"""Check audited source identity and patch applicability without editing the checkout.

The three original-source patches are checked independently, not cumulatively.
With --with-after-01, patch 01 is applied only to temporary copied sources and
patch 03b is checked against that candidate. Patch applicability is not a Lean
compilation check. Temporary directories honor TMPDIR and are removed afterward.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile
import time

PACKAGE = Path(__file__).resolve().parents[1]
ORIGINAL_PATCHES = ("01-certificate-dependency.patch", "02-shifted-numerator.patch",
                    "03a-constant-predicate-original.patch")
AFTER_PATCH = "03b-constant-predicate-after-01.patch"
SOURCE_DIR = "Computability/DiophantineConsistency/Lean/DiophantineConsistency"


def now():
    return datetime.now(timezone.utc).isoformat()


def git_blob(data):
    return hashlib.sha1(("blob " + str(len(data)) + "\0").encode("ascii") + data).hexdigest()


def run(argv, cwd, logfile):
    # Ignore inherited Git directory overrides so all Git commands use cwd.
    env = os.environ.copy()
    for key in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
                "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES"):
        env.pop(key, None)
    print("Running: " + " ".join(str(x) for x in argv), flush=True)
    start = time.monotonic()
    try:
        process = subprocess.run(argv, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, check=False)
        output, code = process.stdout, process.returncode
    except OSError as exc:
        output, code = (str(exc) + "\n").encode(), 127
    logfile.write_bytes(output)
    if output:
        sys.stdout.buffer.write(output)
        sys.stdout.buffer.flush()
    return {"command": [str(x) for x in argv], "cwd": str(cwd), "exit_code": code,
            "elapsed_seconds": time.monotonic() - start, "log": str(logfile)}


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="Example: python scripts/check_patches.py --repo /path/to/ProveIt "
               "--with-after-01 --output /path/to/new-patch-check.json\n"
               "Original checks never apply a patch to --repo. An existing result is not overwritten.\n"
               "03a and 03b are alternatives: 03a targets original sources; 03b follows patch 01.")
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--git", default="git", help="Git executable (default: git on PATH)")
    parser.add_argument("--with-after-01", action="store_true", help="Also check 03b in an isolated candidate")
    parser.add_argument("--output", type=Path, help="New JSON receipt; logs are saved beside it")
    args = parser.parse_args()
    repo = args.repo.expanduser().resolve()
    report = (args.output.expanduser().resolve() if args.output else
              Path(tempfile.mkdtemp(prefix="proveit-patch-check-")) / "result.json")
    logs = report.with_name(report.stem + ".logs")
    if report.exists() or logs.exists():
        parser.error("Output receipt or its log directory already exists; choose a fresh --output.")
    report.parent.mkdir(parents=True, exist_ok=True)
    logs.mkdir()
    receipt = {"purpose": "source-identity and patch-applicability check; no Lean compilation",
               "started_utc": now(), "repo": str(repo), "package": str(PACKAGE),
               "source_checks": [], "commands": [],
               "after_01": {"status": "not-requested"}}
    result, sources = 2, {}
    try:
        audit_path = PACKAGE / "audit" / "final_refresh_identity.json"
        audit = json.loads(audit_path.read_text())
        entries = audit["candidate_source_identity"]
        receipt["audit"] = {"path": str(audit_path), "old_pin": audit["old_pin"],
                            "final_pin": audit["final_pin"]}
        if len(entries) != 8 or len({x["path"] for x in entries}) != 8:
            raise ValueError("Expected eight distinct audited candidate source paths.")
        for entry in entries:
            path = PurePosixPath(entry["path"])
            if path.is_absolute() or ".." in path.parts or path.suffix != ".lean":
                raise ValueError("Invalid audited Lean source path: " + str(path))
            if not entry["identical"] or entry["old_blob"] != entry["fresh_blob"]:
                raise ValueError("The audit does not certify unchanged source: " + str(path))
            data = (repo / path).read_bytes()
            actual = git_blob(data)
            matched = actual == entry["fresh_blob"]
            receipt["source_checks"].append({"path": str(path), "expected_blob": entry["fresh_blob"],
                                              "actual_blob": actual, "matches": matched})
            sources[str(path)] = data
        if not all(item["matches"] for item in receipt["source_checks"]):
            raise ValueError("Working-tree source bytes differ from the eight audited Git blobs.")
        git = shutil.which(args.git)
        if git is None:
            raise ValueError("Git was not found; supply its executable with --git.")
        required = ORIGINAL_PATCHES + ((AFTER_PATCH,) if args.with_after_01 else ())
        for name in required:
            if not (PACKAGE / "patches" / name).is_file():
                raise ValueError("Missing patch: " + name)
        result = 0
        for name in ORIGINAL_PATCHES:
            checked = run([git, "apply", "--check", str(PACKAGE / "patches" / name)],
                          repo, logs / (name + ".log"))
            checked.update(patch=name, stage="original")
            receipt["commands"].append(checked)
            if checked["exit_code"] != 0:
                result = 1
        if args.with_after_01:
            receipt["after_01"] = {"status": "not-run"}
            with tempfile.TemporaryDirectory(prefix="proveit-patch-candidate-") as directory:
                candidate = Path(directory)
                for relative, data in sources.items():
                    target = candidate / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(data)
                # A temporary repository prevents discovery of any parent checkout,
                # including when a caller's TMPDIR is inside their own repository.
                initialized = run([git, "init", "--quiet"], candidate, logs / "candidate-init.log")
                receipt["commands"].append(dict(initialized, stage="temporary-candidate-init"))
                if initialized["exit_code"] != 0:
                    raise ValueError("Could not initialize the isolated temporary candidate.")
                applied = run([git, "apply", str(PACKAGE / "patches" / ORIGINAL_PATCHES[0])],
                              candidate, logs / "candidate-apply-01.log")
                receipt["commands"].append(dict(applied, stage="temporary-apply-01"))
                if applied["exit_code"] == 0:
                    migration = []
                    for name in ("EnumeratorSemantics.lean", "Computability.lean", "DirectScalarEnumerator.lean"):
                        generated = (candidate / SOURCE_DIR / name).read_bytes()
                        reference = (PACKAGE / "reference" / "certificate-migration" / name).read_bytes()
                        migration.append({"file": name, "matches_reference": generated == reference})
                    receipt["after_01"]["migration_reference_checks"] = migration
                    if not all(item["matches_reference"] for item in migration):
                        raise ValueError("Applying patch 01 did not reproduce the recorded migration files.")
                    checked = run([git, "apply", "--check", str(PACKAGE / "patches" / AFTER_PATCH)],
                                  candidate, logs / (AFTER_PATCH + ".log"))
                    receipt["commands"].append(dict(checked, patch=AFTER_PATCH, stage="after-01"))
                    receipt["after_01"]["status"] = "passed" if checked["exit_code"] == 0 else "failed"
                    if checked["exit_code"] != 0:
                        result = 1
                else:
                    receipt["after_01"].update(status="failed", reason="patch 01 did not apply to temporary sources")
                    result = 1
            receipt["after_01"]["temporary_candidate_removed"] = True
        receipt["source_bytes_unchanged_after_check"] = all(
            (repo / relative).read_bytes() == data for relative, data in sources.items())
        if not receipt["source_bytes_unchanged_after_check"]:
            result = 1
        receipt["status"] = "passed" if result == 0 else "failed"
    except (OSError, ValueError, KeyError, TypeError) as exc:
        result = 2
        receipt.update(status="error", error=str(exc))
        print("Error: " + str(exc), file=sys.stderr)
    finally:
        receipt.update(finished_utc=now(), exit_code=result)
        report.write_text(json.dumps(receipt, indent=2) + "\n")
        print("Receipt: " + str(report), flush=True)
    return result


if __name__ == "__main__":
    sys.exit(main())
