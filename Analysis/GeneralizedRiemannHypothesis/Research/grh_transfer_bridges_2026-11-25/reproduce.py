#!/usr/bin/env python3
"""Replay new certificates; optionally replay the two unchanged prior archives."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent


def run_check(command, cwd, transcript):
    result = subprocess.run(command, cwd=cwd, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    transcript.write_text(result.stdout)
    if result.returncode != 0:
        print(result.stdout)
        raise RuntimeError(f"Certificate failed: {command}")
    return dict(command=[str(x) for x in command], exit_code=result.returncode,
                transcript=transcript.relative_to(ROOT).as_posix(),
                transcript_sha256=hashlib.sha256(transcript.read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--include-prior", action="store_true",
                        help="Also replay the two included previous CM archives.")
    args = parser.parse_args()
    if not __debug__ or os.environ.get("PYTHONOPTIMIZE"):
        raise SystemExit("Run without Python optimization; the older certificates use assertions.")
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    records = []
    for script, log in [
        ("check_ray_characters.py", "ray_character_replay.txt"),
        ("check_confluent_refinement.py", "confluent_replay.txt"),
    ]:
        records.append(run_check([sys.executable, ROOT / "checks" / script],
                                 ROOT, evidence / log))
        print(f"PASS: {script}", flush=True)

    if args.include_prior:
        pairs = [
            ("grh_cm_four_terms_and_prime_bias.zip", "grh_cm_and_prime_bias",
             "prior_four_term_replay.txt"),
            ("grh_sparse_singular_moduli.zip", "grh_sparse_singular_moduli",
             "prior_five_term_replay.txt"),
        ]
        for name, directory, log in pairs:
            with tempfile.TemporaryDirectory(prefix="grh-prior-") as tmp:
                base = Path(tmp).resolve()
                with zipfile.ZipFile(ROOT / "prior" / name) as archive:
                    for item in archive.infolist():
                        target = (base / item.filename).resolve()
                        if target != base and base not in target.parents:
                            raise RuntimeError("Unexpected archive path")
                    archive.extractall(base)
                script = base / directory / "reproduce.py"
                record = run_check([sys.executable, script], script.parent, evidence / log)
                record["command"] = ["python3", f"prior/{name}:{directory}/reproduce.py"]
                records.append(record)
                print(f"PASS: {name}", flush=True)
    (evidence / "reproduction_summary.json").write_text(
        json.dumps({"all_requested_checks_passed": True,
                    "prior_archives_replayed_in_this_invocation": args.include_prior,
                    "records": records}, indent=2) + "\n")
    print("All requested exact certificates passed.")


if __name__ == "__main__":
    main()
