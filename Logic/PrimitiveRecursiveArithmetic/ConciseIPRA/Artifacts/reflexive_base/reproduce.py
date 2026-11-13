"""Reproduce the delivered measurements and targeted proof checks offline."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    pairs = [
        ("code/checker.py", "validation/reflexive_base.py"),
        ("reference/zero_seven.py", "validation/zero_seven.py"),
    ]
    for a, b in pairs:
        if (ROOT / a).read_bytes() != (ROOT / b).read_bytes():
            raise RuntimeError("Validation kernel differs from deliverable: " + a)

    provenance = json.loads((ROOT / "evidence/source_provenance.json").read_text())
    for row in provenance["files"]:
        data = (ROOT / row["local_path"]).read_bytes()
        git_hash = hashlib.sha1(b"blob " + str(len(data)).encode()
                               + b"\0" + data).hexdigest()
        if git_hash != row["git_sha"]:
            raise RuntimeError("Upstream source mismatch: " + row["local_path"])

    subprocess.run([sys.executable, str(ROOT / "measure.py")], check=True)
    subprocess.run([sys.executable, str(ROOT / "validation/verify_translations.py")],
                   check=True)

    checker = load(ROOT / "code/checker.py", "selected")
    readable = load(ROOT / "code/checker_readable.py", "readable")
    normalized = load(ROOT / "evidence/normalized/checker.py", "normalized")
    count = 0
    for path in sorted((ROOT / "validation/examples").glob("*.json")):
        if path.name.endswith("_seven.json") or path.name.endswith("_roundtrip.json"):
            continue
        value = json.loads(path.read_text())
        expected = "rejected" not in path.name
        for module in [checker, readable, normalized]:
            try:
                module.check(value)
                actual = True
            except (ValueError, TypeError, IndexError, KeyError, RecursionError):
                actual = False
            if actual != expected:
                raise RuntimeError("Unexpected acceptance: " + path.name)
            count += 1
    destination = ROOT / "tests/certificates"
    destination.mkdir(parents=True, exist_ok=True)
    sample = ROOT / "validation/examples/derived_reflexivity_six.json"
    (destination / "reflexivity.json").write_bytes(sample.read_bytes())
    test = json.loads((ROOT / "validation/translation_verification.json").read_text())
    report = dict(
        all_passed=True,
        authenticated_upstream_files=len(provenance["files"]),
        substantive_cases=len(test["translation_cases"]),
        malformed_input_cases=len(test["rejection_cases"]),
        standalone_process_checks=test["standalone_process_checks"],
        selected_readable_normalized_checks=count,
        proof_assistant_verification=False)
    (ROOT / "evidence/verification.json").write_text(json.dumps(report, indent=2) + "\n")
    summary = (
        "The executed suite passed "
        + str(report["substantive_cases"])
        + " substantive translation and control cases, "
        + str(report["malformed_input_cases"])
        + " malformed-input controls, and "
        + str(report["standalone_process_checks"])
        + " standalone process checks, including optimized Python. "
        + "A further " + str(count)
        + " checks compared the selected, readable and source-normalized "
        + "implementations on the delivered guarded certificates. "
        + "All expected outcomes agreed.\n\n"
        + "The examples exercise an actually used induction hypothesis, "
        + "a nonreflexive induction base, a nested binder, retained outer "
        + "assumptions, nonzero-witness progress, and literal-zero-witness "
        + "cases. Two substitution tests change the guard from false to "
        + "true: variable identification and zero contraction. Naive "
        + "syntax-only substitution is rejected; the elaborated "
        + "substitution is accepted. Both translation directions "
        + "check their input and output with the corresponding kernels "
        + "and preserve the complete sequent.\n\n"
        + "These finite checks support the implementation; they do not "
        + "replace the structural equivalence proof. Complete results and "
        + "actual certificates are included.\n")
    (ROOT / "evidence/validation_summary.tex").write_text(summary)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
