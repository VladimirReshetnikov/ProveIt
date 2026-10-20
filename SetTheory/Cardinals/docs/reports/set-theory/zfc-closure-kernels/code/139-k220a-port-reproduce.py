#!/usr/bin/env python3
"""Offline reconstruction and independent verification of three K220 alternatives.

Default: audit the complete inherited baseline chain, freshly reconstruct all
three alternatives, and freshly run both universal all-tape checkers plus exact
canonical/native initialization. --full-baseline also freshly rederives the
baseline's final runtime; --deep-baseline asks its driver to rederive ancestors.
No mode claims a new proof-assistant theorem for the exact alternative bytes.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
BASE_SHA = "132cbb326fcbf6e54957a03095c5f790e207f4ed8ebfb6ceb6e272f329e4ee00"
BASE_NAME = "K220_Construction_2026-10-20"
VARIANTS = ("row103", "row157", "both")


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe(name):
    p = PurePosixPath(name)
    need(isinstance(name, str) and name and not p.is_absolute()
         and all(x not in ("", ".", "..") for x in name.rstrip("/").split("/"))
         and "\\" not in name and ":" not in name and "\0" not in name,
         "Unsafe archive/manifest member")
    return p


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--full-baseline", action="store_true")
    parser.add_argument("--deep-baseline", action="store_true")
    parser.add_argument("--skip-baseline-replay", action="store_true",
                        help="For debugging only: weaker alternative-only replay.")
    args = parser.parse_args()
    need(__debug__ and not sys.flags.optimize and not os.environ.get("PYTHONOPTIMIZE"),
         "Assertions must remain enabled")
    output = args.output_dir.resolve()
    need(output != ROOT and ROOT not in output.parents, "Output must be outside this packet")
    need(not output.exists() or not any(output.iterdir()), "Output must be initially empty")
    output.mkdir(parents=True, exist_ok=True)
    (output / "logs").mkdir()
    start = time.monotonic()
    receipt = {
        "status": "RUNNING",
        "mode": "alternative_only_debug" if args.skip_baseline_replay else
                ("fresh_baseline_runtime" if args.full_baseline or args.deep_baseline
                 else "inherited_certificate_audit"),
        "deep_baseline": args.deep_baseline,
        "phases": [],
    }

    def save():
        receipt["seconds"] = time.monotonic() - start
        (output / "replay.json").write_text(json.dumps(receipt, indent=2) + "\n")

    def phase(name, command):
        print(name, flush=True)
        began = time.monotonic()
        log = output / "logs" / (name + ".log")
        with log.open("w") as stream:
            result = subprocess.run(
                [sys.executable, "-B", *map(str, command)],
                stdout=stream, stderr=subprocess.STDOUT,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
        receipt["phases"].append({
            "name": name, "returncode": result.returncode,
            "seconds": time.monotonic() - began, "log": str(log.relative_to(output)),
        })
        save()
        need(result.returncode == 0, "Failed phase " + name + "; inspect " + str(log))

    try:
        manifest = json.loads((ROOT / "manifest.json").read_text())
        need(manifest["schema_version"] == 1, "Manifest version")
        seen = set()
        for item in manifest["files"]:
            name = item["path"]
            need(name not in seen and name not in ("manifest.json", "SHA256SUMS"),
                 "Duplicate/self manifest entry")
            seen.add(name)
            path = ROOT / safe(name)
            need(path.is_file() and not path.is_symlink() and ROOT in path.resolve().parents,
                 "Missing or escaping manifest member")
            need(path.stat().st_size == item["size"] and sha(path) == item["sha256"],
                 "Manifest mismatch: " + name)
        actual = set()
        for path in ROOT.rglob("*"):
            need(not path.is_symlink(), "Symlink packet member")
            if path.is_file() and path not in (ROOT / "manifest.json", ROOT / "SHA256SUMS"):
                actual.add(path.relative_to(ROOT).as_posix())
        need(actual == seen, "Manifest does not cover exact packet inventory")
        receipt["manifest_files"] = len(seen)
        archive = ROOT / "vendor" / (BASE_NAME + ".zip")
        need(sha(archive) == BASE_SHA, "Pinned baseline ZIP mismatch")
        with zipfile.ZipFile(archive) as zipped:
            names = set()
            for member in zipped.infolist():
                relative = safe(member.filename)
                need(relative.parts[0] == BASE_NAME and str(relative) not in names,
                     "Duplicate/unexpected archive member")
                names.add(str(relative))
                mode = stat.S_IFMT(member.external_attr >> 16)
                need(mode in (0, stat.S_IFREG, stat.S_IFDIR) and not member.flag_bits & 1,
                     "Nonregular/encrypted archive member")
                target = output / "vendor" / relative
                need(output in target.resolve().parents, "Escaping archive member")
                if member.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with zipped.open(member) as src, target.open("xb") as dst:
                        shutil.copyfileobj(src, dst)
                    need(target.stat().st_size == member.file_size, "Truncated archive member")
        baseline = output / "vendor" / BASE_NAME
        if not args.skip_baseline_replay:
            flags = [] if args.full_baseline or args.deep_baseline else ["--quick"]
            if args.deep_baseline:
                flags.append("--full-baseline")
            phase("01_inherited_baseline", [
                baseline / "portable/reproduce.py", *flags,
                "--output-dir", output / "baseline_replay",
            ])
        prior = json.loads((ROOT / "verification/baseline_full_replay.json").read_text())
        need(prior["status"] == "FULL_K220_REPLAY_PASS" and
             prior["native_table_sha256"] == "4466ec4f947a9c5112397c30ca25b0e70e3ac39ee54878b3e4493a0297d732e4" and
             prior["canonical_table_sha256"] == "f80c57e800d4f999d9b4902a8e96bd36d1b6180b3ad322ca8ed0ab67b47f2a5f" and
             prior["source_sha256"] == "837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7" and
             prior["mode"] == "fresh_final_unbounded_runtime" and
             len(prior["phases"]) == 5 and all(p["returncode"] == 0 for p in prior["phases"]),
             "Historical full baseline replay receipt does not match exact baseline")
        receipt["historical_full_baseline_receipt_sha256"] = sha(ROOT / "verification/baseline_full_replay.json")
        source = ROOT / "machine/sites220.json"
        need(source.read_bytes() == (baseline / "machine/sites220.json").read_bytes(),
             "Common source differs from baseline")
        old = baseline / "machine/k220.native.tm"
        machines = output / "machine"
        phase("02_construct_variants", [
            ROOT / "portable/construct.py", "--baseline", old, "--output", machines,
        ])
        phase("03_all_tape_macro_diamonds", [
            ROOT / "portable/verify_alternate_rows.py", "--old", old,
            "--machines", machines, "--output", output / "alternate_rows_proof.json",
        ])
        summaries = []
        for name in VARIANTS:
            table = machines / name / "k220.native.tm"
            phase("04_independent_joint_" + name, [
                ROOT / "portable/check_joint_fold.py", "--old", old, "--new", table,
                "--output", output / ("joint_" + name + ".json"),
            ])
            phase("05_canonical_blank_" + name, [
                ROOT / "portable/canonicalize.py", "--table", table,
                "--source", source, "--output", machines / name,
            ])
            for filename in ("k220.native.tm", "k220.tm", "canonicalization.json"):
                need((machines / name / filename).read_bytes()
                     == (ROOT / "machine" / name / filename).read_bytes(),
                     "Rebuilt delivered bytes differ: " + name + "/" + filename)
            record = json.loads((machines / name / "canonicalization.json").read_text())
            summaries.append({
                "variant": name,
                "native_sha256": record["native_sha256"],
                "canonical_sha256": record["canonical_sha256"],
                "working_states": record["working_states"],
                "graph_reachable_working_states": record["graph_reachable_working_states"],
                "rows": record["rows"], "start": record["start"], "halt": record["halt"],
                "blank_startup_steps": record["startup"]["steps"],
            })
        need(len({item["canonical_sha256"] for item in summaries}) == 3,
             "Alternatives collapsed to the same canonical table")
        receipt.update(
            status="ALTERNATIVES_ONLY_REPLAY_PASS" if args.skip_baseline_replay
                   else "SELF_CONTAINED_THREE_ALTERNATIVES_REPLAY_PASS",
            variants=summaries,
            baseline_zip_sha256=BASE_SHA,
            baseline_runtime_fresh_this_run=bool(args.full_baseline or args.deep_baseline) and not args.skip_baseline_replay,
            source_sha256=sha(source),
            proof_boundary="Fresh ordinary executable all-tape equivalence proofs "
                           "transfer the retained K220 logical calibration. No new "
                           "compiled exact-byte Rocq/Lean theorem or internal PA endpoint. "
                           "No unconditional nonhalting or minimality claim.",
            exploratory_in_scope=False,
        )
        save()
        print(receipt["status"], flush=True)
    except Exception as error:
        receipt.update(status="FAILED", error=repr(error))
        save()
        raise


if __name__ == "__main__":
    main()
