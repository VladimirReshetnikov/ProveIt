#!/usr/bin/env python3
"""Replay this contribution's finite certificates and diagnostics.

The mathematical universal claims are proved in the manuscript. This driver
does not search for a new machine, establish solver infeasibility, or build a
proof-assistant endpoint. The inherited full runtime replay is a separate
command documented in README.txt.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
if sys.flags.optimize:
    raise RuntimeError("Assertions are required; run without Python -O.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "verification")
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    records = []

    def run(name, relative_script, *arguments):
        command = [sys.executable, "-B", str(ROOT / relative_script),
                   *map(str, arguments)]
        result = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=180)
        (out / (name + ".log")).write_text(result.stdout)
        if result.returncode:
            print(result.stdout)
            raise RuntimeError(f"{name} failed: exit {result.returncode}")
        records.append({"name": name, "status": "PASS"})
        print("PASS", name, flush=True)

    table = ROOT / "reference/zfc245/machine/zfc245.tm"
    expected_hash = "17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13"
    assert hashlib.sha256(table.read_bytes()).hexdigest() == expected_hash
    rows = [line.split() for line in table.read_text().splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    assert len(rows) == 490
    keys = set()
    for q, read, write, direction, target in rows:
        q, read, write, target = map(int, (q, read, write, target))
        assert q in range(245) and read in (0, 1) and write in (0, 1)
        assert direction in ("L", "R") and target in range(246)
        assert (q, read) not in keys
        keys.add((q, read))
    assert keys == {(q, b) for q in range(245) for b in (0, 1)}
    records.append({"name": "reference-table-identity", "status": "PASS",
                    "working_states": 245, "rows": 490})
    print("PASS reference-table-identity", flush=True)

    variants = out / "commuting_ax_variants.json"
    run("disjoint-source-certificates", "semantic/commutations.py",
        "--count", 256, "--output", variants)
    expected = json.loads((ROOT / "semantic/commuting_ax_variants.json").read_text())
    actual = json.loads(variants.read_text())
    assert actual == expected
    assert actual["distinct_words"] == 224

    # Reconstruct each control witness and every exact matrix. Comparing the
    # complete certificate also checks the actual sentinel and cycle addresses.
    sys.path.insert(0, str(ROOT / "semantic"))
    import affine_commutations as affine
    saved = json.loads((ROOT / "semantic/affine_commutations.json").read_text())
    built = {c: {"ast": affine.C.asts[c], "matrix": affine.maps[c],
                 "control": affine.cert[c]} for c in affine.maps}
    assert json.loads(json.dumps(built)) == saved["linear_atoms"]
    letters = sorted(affine.C.asts)
    pairs = [[a, b] for a in letters for b in letters
             if a < b and affine.independent(a, b)]
    extra = [[a, b] for a, b in pairs if not affine.C.independent(a, b)]
    assert pairs == saved["independent_pairs"] and len(pairs) == 178
    assert extra == saved["extra_affine_pairs"] and len(extra) == 44
    assert len(affine.maps) == 22
    records.append({"name": "affine-source-certificates", "status": "PASS",
                    "affine_atoms": 22, "commuting_pairs": 178,
                    "extra_affine_pairs": 44})
    print("PASS affine-source-certificates", flush=True)

    run("grammar-finite-replay", "grammar/reproduce.py", "verify",
        "--output", out / "grammar")
    run("label-twist-diagnostics", "logic/check_label_twist.py",
        "--output", out / "label_twist_checks.json")
    run("anchored-rank-diagnostics", "logic/check_anchored_rank.py",
        "--output", out / "anchored_rank_checks.json")
    for name in ("label_twist_checks.json", "anchored_rank_checks.json"):
        assert json.loads((out / name).read_text()) == json.loads(
            (ROOT / "logic" / name).read_text())

    for name, script, certificate in (
        ("local-increment-contract", "prove_left_increment.py",
         "left_increment_local_proofs.json"),
        ("integration-counterexample", "check_integration_counterexample.py",
         "integration_counterexample.json"),
        ("gap-budget-counterexample", "check_gap_budget.py",
         "gap_budget_counterexamples.json"),
    ):
        path = ROOT / "interpreter" / certificate
        previous = json.loads(path.read_text())
        run(name, "interpreter/" + script)
        assert json.loads(path.read_text()) == previous

    summary = {
        "status": "PASS_NEW_RESEARCH_CERTIFICATES",
        "new_verified_sub245_machine": False,
        "checks": records,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "scope": [
            "Exact finite source, grammar, table-identity and counterexample checks.",
            "Universal source/local lemmas require the ordinary induction proofs in the manuscript.",
            "Logical finite diagnostics are not finite models of CP/GIC.",
            "No new binary consistency-machine endpoint, global state lower bound, or solver proof log.",
            "The inherited full 245-state replay is recorded separately and is optional here.",
        ],
    }
    (out / "verification-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
