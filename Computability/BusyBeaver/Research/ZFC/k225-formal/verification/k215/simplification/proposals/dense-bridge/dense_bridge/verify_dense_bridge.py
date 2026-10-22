#!/usr/bin/env python3
"""Recheck the dense bridge replacement against the pinned ProveIt sources.

No generated olean files are required by the delivery. This script copies only
Core, KZip and KDenseBridge to isolated build directories, then checks both
versions and an exact public-type/axiom audit. It never edits the repository.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

BASELINE = "57541fe0cfe3af62b4cb58747d8d1d7c16b338d5"
SOURCE_DIR = Path("Computability/BusyBeaver/Lean")
MODULE = Path("BusyBeaver/ZFC/KDenseBridge.lean")
DEPS = [Path("BusyBeaver/Core.lean"), Path("BusyBeaver/ZFC/KZip.lean")]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--work-dir", required=True, type=Path)
    args = ap.parse_args()
    repo = args.repo.resolve()
    output = args.work_dir.resolve()
    delivery = Path(__file__).resolve().parent
    lean = shutil.which(args.lean)
    if lean is None:
        raise SystemExit("Lean executable was not found")
    output.mkdir(parents=True, exist_ok=True)
    expected = json.loads((delivery / "evidence/metrics.json").read_text())
    inputs = {}
    for rel in [*DEPS, MODULE]:
        # Fetch exact committed bytes even if the caller has uncommitted work.
        inputs[rel] = subprocess.check_output(
            ["git", "show", f"{BASELINE}:{SOURCE_DIR / rel}"], cwd=repo
        )
    proposed = (delivery / MODULE).read_bytes()
    assert digest(inputs[MODULE]) == expected["before"]["sha256"]
    assert digest(proposed) == expected["after"]["sha256"]
    before, after = inputs[MODULE].decode(), proposed.decode()
    marker = "theorem blank_iff"
    assert before[: before.index(marker)] == after[: after.index(marker)]
    assert before[before.index(marker):].split(" := by", 1)[0] == \
           after[after.index(marker):].split(" := by", 1)[0]
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    if "version 4.32.0" not in version:
        raise SystemExit(f"Expected Lean 4.32.0; found {version}")
    records = []
    audits = {}
    for label, replacement in [("baseline", inputs[MODULE]), ("modified", proposed)]:
        tree = output / label
        tree.mkdir(exist_ok=True)
        for rel, data in inputs.items():
            dst = tree / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(replacement if rel == MODULE else data)
        shutil.copy2(delivery / "Audit.lean", tree / "Audit.lean")
        env = dict(os.environ, LEAN_PATH=str(tree))
        for rel in [*DEPS, MODULE]:
            log = tree / (rel.stem + ".log")
            cmd = [lean, "-o", str(rel.with_suffix(".olean")), str(rel)]
            with log.open("w") as stream:
                proc = subprocess.run(cmd, cwd=tree, env=env,
                                      stdout=stream, stderr=subprocess.STDOUT)
            records.append({"variant": label, "module": str(rel),
                            "exit_code": proc.returncode, "log": str(log)})
            if proc.returncode:
                raise SystemExit(f"Compilation failed; inspect {log}")
        audit = subprocess.run([lean, "Audit.lean"], cwd=tree, env=env,
                               text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT)
        (tree / "Audit.log").write_text(audit.stdout)
        records.append({"variant": label, "module": "Audit.lean",
                        "exit_code": audit.returncode})
        if audit.returncode:
            raise SystemExit(f"Audit failed; inspect {tree / 'Audit.log'}")
        audits[label] = audit.stdout
    assert audits["baseline"] == audits["modified"], "Axiom audit changed"
    assert "[propext, Quot.sound]" in audits["modified"]
    assert "sorryAx" not in audits["modified"]
    result = {"baseline": BASELINE, "compiler": version,
              "same_public_statement": True, "same_axiom_audit": True,
              "builds": records, "full_endpoint_rebuilt": False}
    (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
