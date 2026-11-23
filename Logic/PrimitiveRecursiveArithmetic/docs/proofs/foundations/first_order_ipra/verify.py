"""Replay the executable examples, Lean checks, and optional pinned native checker."""
import argparse
import copy
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROGRAMS = (
    "ef_certificates.py",
    "code/normal_certificates.py",
    "code/machine_witnesses.py",
    "code/finite_invariants.py",
)
AUDITS = {
    "BackAndForth": [],
    "CanonicalForcing": ["FirstOrderIPRA.CanonicalForcing.canonical_completeness"],
    "GroundResolution": ["FirstOrderIPRA.GroundResolution.check_sound",
                         "FirstOrderIPRA.GroundResolution.refute_checked"],
    "NegativeTranslation": ["FOLNegative.negative_translation_iff",
                            "FOLNegative.equiconsistency", "FOLNegative.finite_sound",
                            "FOLNegative.consistency"],
    "Substitution": ["FirstOrderPacket.Substitution.Formula." + x for x in
                     ("truthSubst", "truthRename", "coincidence", "substId")],
}
CHECKER_SHA = "6af3134ce7c917d54b77ce552038ac23bac359b2b77ef78b181ddde291848556"


def run(command, **kwargs):
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, cwd=ROOT, **kwargs)
    if result.stdout:
        print(result.stdout.rstrip(), flush=True)
    result.check_returncode()
    return result.stdout


def replay_native(checker):
    checker = checker.resolve()
    if hashlib.sha256(checker.read_bytes()).hexdigest() != CHECKER_SHA:
        raise ValueError("pinned upstream checker hash mismatch")
    cert = json.loads((ROOT / "native/equality_transport.json").read_text())
    no_premise = copy.deepcopy(cert)
    no_premise["context"].pop()
    captured = copy.deepcopy(cert)
    captured["goal"][2][3][2] = ["v", 2]
    for name, data, expected in (("original", cert, 0), ("missing premise", no_premise, 1),
                                  ("wrong binder index", captured, 1)):
        result = subprocess.run([sys.executable, str(checker)], input=json.dumps(data),
                                capture_output=True, text=True)
        if result.returncode != expected or (expected == 0 and result.stdout.strip() != "ACCEPT"):
            raise AssertionError((name, result.returncode, result.stdout, result.stderr))
        print(f"Native checker, {name}: exit {expected}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Lean 4.32 executable")
    parser.add_argument("--python-only", action="store_true", help="skip Lean checks")
    parser.add_argument("--native-checker", type=Path, help="raw_checker.py from native/README.md")
    args = parser.parse_args()
    print("Python", sys.version.split()[0], flush=True)
    for path in PROGRAMS:
        print(path, flush=True)
        run([sys.executable, str(ROOT / path)])
    if not args.python_only:
        lean = shutil.which(args.lean)
        if not lean:
            parser.error("Lean 4.32 is required unless --python-only is given")
        run([lean, "--version"])
        with tempfile.TemporaryDirectory() as folder:
            for stem, decls in AUDITS.items():
                print(stem + ".lean", flush=True)
                source = (ROOT / "lean" / (stem + ".lean")).read_text()
                target = Path(folder) / (stem + ".lean")
                target.write_text(source + "\n" + "".join(f"#print axioms {d}\n" for d in decls))
                log = run([lean, str(target)])
                if "sorryAx" in log or "declaration uses 'sorry'" in log:
                    raise ValueError("admitted theorem in " + stem)
    if args.native_checker:
        replay_native(args.native_checker)


if __name__ == "__main__":
    main()
