#!/usr/bin/env python3
"""Audit a local git checkout. Requires Python 3 and Git. Reads only pinned blobs."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import re
import subprocess
import sys

REV = "72fead102f663d5c7a407964a13dc0cf9d977207"
ROOT = Path(sys.argv[1] if len(sys.argv) == 2 else ".")
if len(sys.argv) > 2:
    sys.exit("Usage: python3 check_repository.py /path/to/grh-lean")


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def blob(path):
    return git("show", REV + ":" + path)


if git("rev-parse", REV + "^{commit}").decode().strip() != REV:
    sys.exit("Pinned revision unavailable")

print("Commit", REV)
# Independently published at https://math.mit.edu/~drew/shortgrh/
mit_hash = "9138cf2f5862e64f823ed676e8d37333c0717e1a13cd8f74f6b735ab2d1ba57c"
actual = sha256(git("archive", "--format=tar", REV)).hexdigest()
if actual != mit_hash:
    sys.exit("Archive digest differs from the MIT verification record: " + actual)
print("Git archive SHA-256 matches the published MIT digest:", actual)
paths = git("ls-tree", "-r", "--name-only", REV).decode().splitlines()
for edition in ["grh", "grh-compact"]:
    print("\nEdition", edition)
    sources = [p for p in paths if p.startswith(edition + "/src/") and p.endswith(".lean")]
    groups = Counter(p.split("/")[2] for p in sources)
    print("Source files", len(sources), dict(sorted(groups.items())))
    for suffix in ["lean-toolchain", "lake-manifest.json", "src/Statements.lean",
                   "src/Main.lean", "scripts/PrintAxioms.lean"]:
        data = blob(edition + "/" + suffix)
        print(sha256(data).hexdigest(), suffix)
    print("Toolchain", blob(edition + "/lean-toolchain").decode().strip())
    statements = blob(edition + "/src/Statements.lean").decode()
    print("Statement imports", re.findall(r"^import (.+)$", statements, re.M))
    main = blob(edition + "/src/Main.lean").decode()
    print("Public declarations", re.findall(r"^theorem (\w+)", main, re.M))
print("\nSource inventory only. See the project README for Lean build and axiom checks.")
