"""Check the upstream Git snapshot, its interface and its toolchain pins.

Usage: python checks/source_identity.py /path/to/grh-lean
Reads immutable Git objects. The working tree can be at a different revision.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PIN = "72fead102f663d5c7a407964a13dc0cf9d977207"
ARCHIVE = "9138cf2f5862e64f823ed676e8d37333c0717e1a13cd8f74f6b735ab2d1ba57c"
MATHLIB = "56a005855ea17e0b0958f73ec801ae140b0a1679"
if len(sys.argv) != 2:
    raise SystemExit(__doc__)
git = ["git", "--no-replace-objects", "-C", str(Path(sys.argv[1]).resolve())]


def file_at_pin(path):
    return subprocess.check_output(git + ["show", PIN + ":" + path])


def require(value, message):
    if not value:
        raise SystemExit(message)


archive = subprocess.check_output(git + ["-c", "tar.umask=0002", "archive", "--format=tar", PIN])
digest = hashlib.sha256(archive).hexdigest()
require(digest == ARCHIVE, "Git archive digest differs from the published one.")
print("commit", PIN)
print("git archive SHA-256", digest)
statement_files = []
for edition in ("grh", "grh-compact"):
    pins = json.loads(file_at_pin(edition + "/lake-manifest.json"))["packages"]
    revision, = [p["rev"] for p in pins if p["name"] == "mathlib"]
    require(revision == MATHLIB, "Wrong Mathlib pin.")
    toolchain = file_at_pin(edition + "/lean-toolchain").decode().strip()
    require(toolchain == "leanprover/lean4:v4.35.0", "Wrong Lean version.")
    statement_files.append(file_at_pin(edition + "/src/Statements.lean"))
    comparator = json.loads(file_at_pin(edition + "/comparator.json"))
    print(edition, toolchain, revision)
    print("permitted axioms:", ", ".join(comparator["permitted_axioms"]))
    print("theorems:", ", ".join(comparator["theorem_names"]))
require(statement_files[0] == statement_files[1], "Different public interfaces.")
print("identical statement files SHA-256", hashlib.sha256(statement_files[0]).hexdigest())
