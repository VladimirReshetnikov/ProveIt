#!/usr/bin/env python3
"""Replay the positive construction and finite comparison certificates offline.

Python 3.10+ standard library only. No repository, network, Lean, or C++
installation is required. Exploratory searches have their own replay commands.
Nothing in this replay claims the missing absolute iPRA calibration to Con(PA).
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
MACHINE_HASH = "7e1c6442816e5df05e961f2057719252a1976c9a195a786978bf1e2d3c8e466d"


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def integrity():
    require(sha((ROOT / "machine/machine.tm").read_bytes()) == MACHINE_HASH,
            "candidate table hash")
    inherited = []
    for name, key in [("construction/PROVENANCE.json", "inherited_exact_files"),
                      ("proof/PROVENANCE.json", "inherited_Lean_source")]:
        for entry in read_json(ROOT / name)[key]:
            data = (ROOT / entry["local_file"]).read_bytes()
            require(sha(data) == entry["sha256"], entry["local_file"] + " SHA256")
            git_id = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            require(git_id == entry["git_blob_sha1"], entry["local_file"] + " Git blob")
            inherited.append(entry["local_file"])
    literal = ROOT / "verification/independent/recorded"
    raw = gzip.decompress((literal / "contracts.json.gz").read_bytes())
    require(sha(raw) == read_json(literal / "receipt.json")["contracts_sha256"],
            "lossless archived literal contracts")
    manifest = ROOT / "SHA256SUMS"
    count = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest, relative = line.split("  ", 1)
            path = (ROOT / relative).resolve()
            require(path.is_relative_to(ROOT), "manifest path escapes release")
            require(sha(path.read_bytes()) == digest, "manifest mismatch: " + relative)
            count += 1
    return {"status": "PASS", "pinned_inherited_files": len(inherited),
            "archived_contracts_losslessly_verified": True,
            "release_manifest_files_checked": count,
            "release_manifest_present": manifest.exists()}


def replay(output: Path, jobs: int):
    started = time.monotonic()
    output.mkdir(parents=True, exist_ok=True)
    initial = integrity()
    py = [sys.executable, "-B"]
    stages = [
        ("construction", ["construction/build.py", "--output", str(output / "rebuilt")]),
        ("literal_tape", ["verification/independent/check.py", "--output", str(output / "literal")]),
        ("source_binding", ["verification/source_binding.py", "--output", str(output / "source_binding.json")]),
        ("command_words", ["proof/check_commands.py", "--machine", str(ROOT / "machine"),
                           "--output", str(output / "command_words.json")]),
        ("native_exchange", ["proof/check_native_exchange.py", "--output", str(output / "exchange.json")]),
        ("independent_exchange", ["proof/check_exchange_independent.py", "proof/native_exchange.json",
                                  "--output", str(output / "exchange_independent.json")]),
        ("exchange_export", ["proof/rebuild_native_exchange.py", "--output", str(output / "native_exchange.json")]),
        ("comparison", ["comparison/verify_comparison.py", "--receipt", str(output / "comparison.json")]),
        ("startup193", ["research/startup193/verify.py", "--receipt", str(output / "startup193.json")]),
    ]
    env = dict(os.environ)
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"

    def run_stage(stage):
        name, arguments = stage
        print("START " + name, flush=True)
        t0 = time.monotonic()
        log = output / (name + ".log")
        with log.open("w") as stream:
            process = subprocess.run(py + arguments, cwd=ROOT, env=env,
                                     stdout=stream, stderr=subprocess.STDOUT)
        if process.returncode:
            print(log.read_text()[-20000:], file=sys.stderr, flush=True)
            raise RuntimeError(name + " failed; log: " + str(log))
        elapsed = round(time.monotonic() - t0, 3)
        print("PASS " + name + " (" + str(elapsed) + " s)", flush=True)
        return name, {"status": "PASS", "seconds": elapsed}

    completed = {}
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        for future in as_completed([executor.submit(run_stage, stage) for stage in stages]):
            name, result = future.result()
            completed[name] = result

    for name in ["machine.tm", "machine.native.tm", "raw.native.tm"]:
        require((output / "rebuilt" / name).read_bytes() == (ROOT / "machine" / name).read_bytes(),
                "byte-exact rebuilt " + name)
    require((output / "native_exchange.json").read_bytes() == (ROOT / "proof/native_exchange.json").read_bytes(),
            "byte-exact native certificate re-export")
    recorded = ROOT / "verification/independent/recorded"
    fresh = output / "literal/PA194AX11G"
    for name in ["receipt.json", "list_lemmas.json", "startup.json"]:
        require(read_json(fresh / name) == read_json(recorded / name),
                "independent replay equals retained " + name)
    require((fresh / "contracts.json").read_bytes() == gzip.decompress((recorded / "contracts.json.gz").read_bytes()),
            "every literal symbolic contract reproduced byte for byte")
    for fresh_name, saved_name in [("source_binding.json", "verification/source_binding.json"),
                                   ("command_words.json", "verification/command_receipt.json"),
                                   ("comparison.json", "comparison/verification.json"),
                                   ("startup193.json", "research/startup193/verification.json")]:
        require(read_json(output / fresh_name) == read_json(ROOT / saved_name),
                "replayed receipt differs: " + fresh_name)
    result = {
        "status": "PASS", "machine_sha256": MACHINE_HASH,
        "working_states": 194, "transition_rows": 388,
        "integrity": initial, "stages": dict(sorted(completed.items())),
        "rebuilt_tables_byte_equal": True,
        "native_proof_reexport_byte_equal": True,
        "all_literal_symbolic_contracts_byte_equal": True,
        "source_outcomes_replayed_by_each_engine": 4779,
        "prior_graph_classes_compared": 94,
        "physical_193_blank_starts_replayed": 10036,
        "python_version": sys.version.split()[0],
        "seconds": round(time.monotonic() - started, 3),
        "scope": "Finite construction, universal symbolic contracts, complete startup, command words, proof certificate, source splice, novelty, and rejected-start replay. Ordinary relative iPRA proof is in report/main.pdf. No absolute Con(PA) calibration or new Lean/Rocq endpoint is claimed."
    }
    (output / "aggregate_receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2), flush=True)
    return result


def main():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError("Run with assertions enabled; do not use python -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="retain all fresh results at this location")
    parser.add_argument("--jobs", type=int, default=3, help="parallel independent replays (default 3)")
    args = parser.parse_args()
    require(args.jobs >= 1, "jobs must be positive")
    if args.output:
        replay(args.output.resolve(), args.jobs)
    else:
        with tempfile.TemporaryDirectory(prefix="pa194ax11g-replay-") as temp:
            replay(Path(temp), args.jobs)


if __name__ == "__main__":
    main()
