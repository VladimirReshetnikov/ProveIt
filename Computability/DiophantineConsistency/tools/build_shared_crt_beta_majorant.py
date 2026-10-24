#!/usr/bin/env python3
"""Build a separate shared-CRT variant using its literal beta-row majorant.

The frozen shared-crt-prime-lift candidate and its integer companion are
never changed. Only two authenticated original compiler lines are patched.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
DEST = ROOT/"candidates/shared-crt-beta-majorant"
ARCHIVE = REPO/"docs/incoming/ConZFC_Shared_Certificates_2026-10-24.zip"
ARCHIVE_SHA = "61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1"
NAMES = ["build_equation.py", "direct_calculus.py", "wire_eliminated_source.json",
         "affine_shared_step.json", "check_equation.py", "audit_power_graph.py",
         "audit_calculus.py"]
CHANGES = [
    (b"    V = b.add(m, U)\n",
     b"    V = U  # Independent private-coordinate bound; prime-supported CRT lift.\n"),
    (b"    H = b.sum([ep, fp, t, V, ONE])\n",
     b"    H = b.sum([ep, fp])  # Literal beta-row majorant; endpoint forces H>=t.\n"),
]


def need(ok, text):
    if not ok:
        raise RuntimeError(text)


def generate(home):
    raw_archive = ARCHIVE.read_bytes()
    need(sha256(raw_archive).hexdigest() == ARCHIVE_SHA, "actual original archive")
    source = home/"source"
    source.mkdir(parents=True, exist_ok=True)
    pins = {}
    with zipfile.ZipFile(ARCHIVE) as z:
        for name in NAMES:
            member = "con_zfc_shared_certificates/direct/"+name
            original = z.read(member)
            candidate = original
            if name == "build_equation.py":
                for before, after in CHANGES:
                    need(candidate.count(before) == 1, "unique source patch")
                    candidate = candidate.replace(before, after)
            (source/name).write_bytes(candidate)
            pins[name] = dict(original_member=member,
                              original_sha256=sha256(original).hexdigest(),
                              candidate_sha256=sha256(candidate).hexdigest())
        (home/"LICENSE.upstream").write_bytes(z.read("con_zfc_shared_certificates/LICENSE"))
    parent_proof = ROOT/"candidates/shared-crt-prime-lift/PROOF.md"
    parent_bytes = parent_proof.read_bytes()
    expected_parent = "91f8f7db5bbdf7fc26f56e9f7c06a88f467749a41735613ae0fee57a3e26b6c1"
    need(sha256(parent_bytes).hexdigest() == expected_parent, "frozen prime-lift proof")
    (home/"PRIME_LIFT_PROOF.md").write_bytes(parent_bytes)
    (home/"SOURCE_PINS.json").write_text(json.dumps(dict(
        archive=str(ARCHIVE.relative_to(REPO)), archive_sha256=ARCHIVE_SHA,
        changes=["Private bounds m+U become U; label bounds stay m.",
                 "Factorial argument E+F+t+m+U+1 becomes E+F."],
        files=pins, prime_lift_proof=dict(path="PRIME_LIFT_PROOF.md", sha256=expected_parent)
    ), indent=2)+"\n")
    optimization_flags = ["-O"] if sys.flags.optimize else []
    for name, flags in [("affine", []), ("retained", ["--keep-linear-wires"])]:
        subprocess.run([sys.executable, "-B", *optimization_flags, str(source/"build_equation.py"),
                        *flags, "--output", str(home/name)],
                       check=True, text=True, capture_output=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    if args.check:
        with tempfile.TemporaryDirectory(prefix="proveit-shared-beta-majorant-") as tmp:
            fresh = Path(tmp)
            generate(fresh)
            for path in fresh.rglob("*"):
                if path.is_file() and "__pycache__" not in path.parts:
                    old = DEST/path.relative_to(fresh)
                    need(old.is_file() and path.read_bytes() == old.read_bytes(),
                         "deterministic file: "+str(path.relative_to(fresh)))
    else:
        DEST.mkdir(parents=True, exist_ok=True)
        generate(DEST)
    print(json.dumps(dict(status="PASS", check=args.check, variants={
        name: json.loads((DEST/name/"BUILD.json").read_text())["metrics"]
        for name in ["affine", "retained"]}), indent=2))


if __name__ == "__main__":
    main()
