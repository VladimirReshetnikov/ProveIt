#!/usr/bin/env python3
"""Reproduce the package checks with Python 3.10+ and its standard library.

Use --quick to omit fresh universal-tape and graph-novelty runs. Neither
mode proves the missing absolute iPRA/Con(PA) calibration or invokes Lean.
Fresh outputs go to a temporary directory so the retained evidence stays
unchanged. Assertions must be enabled.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(label, script, *args):
    print("\n" + label, flush=True)
    env = dict(os.environ)
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    result = subprocess.run(
        [sys.executable, "-B", str(ROOT / script), *map(str, args)],
        cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    # Preserve enough context to diagnose failures, without printing thousands
    # of paired symbolic contracts on a successful run.
    lines = result.stdout.splitlines()
    print("\n".join(lines if result.returncode else lines[-24:]), flush=True)
    require(result.returncode == 0, label + " failed")


def main():
    require(__debug__ and not sys.flags.optimize,
            "Run with Python assertions enabled; do not use -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()

    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    for entry in manifest["files"]:
        path = ROOT / entry["path"]
        require(path.is_file(), "Missing file: " + entry["path"])
        require(path.stat().st_size == entry["bytes"], "Size mismatch: " + entry["path"])
        require(digest(path) == entry["sha256"], "Hash mismatch: " + entry["path"])
    print("Verified", len(manifest["files"]), "manifest file identities.", flush=True)

    with tempfile.TemporaryDirectory(prefix="pa194-replay-") as td:
        temp = Path(td)
        run("Reconstruct both literal machines and replay construction contracts",
            "construction/rebuild.py", "--receipt", temp / "rebuild.json")
        run("Check factor-two clocks and replay all three complete startups",
            "construction/check_clock_comparison.py",
            "--parent", ROOT / "construction/inputs",
            "--left", ROOT / "construction/AX11QH4L",
            "--right", ROOT / "construction/AX11QH4R",
            "--output", temp / "clock_comparison.json")
        run("Check the additional polynomial resource bound",
            "construction/check_clocks.py", "--output", temp / "clock_bound.json")
        run("Reconstruct and audit the quantified-gate proof templates",
            "research/logical/check_gate_exchange.py", "--output", temp / "gate")
        for name in ("gate_exchange_certificate.json", "gate_exchange_q_certificate.json"):
            require(digest(temp / "gate" / name) ==
                    digest(ROOT / "research/logical/evidence" / name),
                    "Rebuilt gate certificate differs: " + name)

        if not args.quick:
            copied = []
            for name in ("AX11QH4L", "AX11QH4R"):
                dest = temp / name
                shutil.copytree(ROOT / "construction" / name, dest)
                copied.append(dest)
            run("Independently replay all 4,778 literal-tape outcomes per new machine",
                "verification/check.py", *copied)
            for dest in copied:
                for name in ("contracts.json", "list_lemmas.json"):
                    require(digest(dest / "independent" / name) ==
                            digest(ROOT / "construction" / dest.name / "independent" / name),
                            "Replayed independent certificate differs: " + dest.name + "/" + name)
            run("Compare complete graph canonical forms with all 95 historical classes",
                "comparison/check_novelty.py",
                "--candidate", ROOT / "construction/AX11QH4L/machine.tm",
                "--candidate", ROOT / "construction/AX11QH4R/machine.tm",
                "--output", temp / "novelty.json")
            novelty = json.loads((temp / "novelty.json").read_text())
            require(novelty["candidate_forms_pairwise_distinct"], "The two graphs coincide")
            require(all(c["novel_within_scope"] and not c["matches"]
                        for c in novelty["candidates"]), "A candidate matches a historical graph")

    print("\nPASS:", "quick" if args.quick else "full", "reproduction checks.")
    print("No sub-194 construction, absolute Con(PA) calibration, or new Lean endpoint is claimed.")


if __name__ == "__main__":
    main()
