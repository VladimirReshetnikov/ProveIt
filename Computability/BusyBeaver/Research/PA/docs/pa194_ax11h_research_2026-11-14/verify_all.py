#!/usr/bin/env python3
"""Reproduce the AX11H certificates offline with Python's standard library.

This is a certificate replay, not a proof-assistant verification of
iPRA |- Con(PA) <-> nonhalting. It does not rerun the optional long searches.
Run without -O: the inherited mathematical checkers use assertions.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
EXPECTED = "c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="New receipt directory; defaults to a temporary directory.")
    args = parser.parse_args()
    if not __debug__ or sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
        raise SystemExit("Run with assertions enabled and without PYTHONOPTIMIZE.")
    out = (args.output or Path(tempfile.mkdtemp(prefix="ax11h-verification-"))).resolve()
    out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    records = []

    def run(label, script, *arguments):
        print("Checking " + label + " ...", flush=True)
        before = time.monotonic()
        command = [sys.executable, str(ROOT / script), *map(str, arguments)]
        proc = subprocess.run(command, cwd=ROOT, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / (label + ".log")).write_text(proc.stdout)
        if proc.returncode:
            print(proc.stdout)
            raise SystemExit(f"FAILED: {label}, exit code {proc.returncode}")
        records.append({"check": label, "status": "PASS",
                        "seconds": round(time.monotonic() - before, 3)})

    # Check file transport integrity when the final archive manifest is present.
    manifest = ROOT / "SHA256SUMS"
    manifest_count = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            wanted, relative = line.split("  ", 1)
            file = ROOT / relative
            if digest(file) != wanted:
                raise SystemExit("Manifest mismatch: " + relative)
            manifest_count += 1
        print(f"Manifest: {manifest_count} files verified.", flush=True)

    if digest(ROOT / "machine/machine.tm") != EXPECTED:
        raise SystemExit("The supplied dense table is not the audited AX11H table.")

    with tempfile.TemporaryDirectory(prefix="ax11h-rebuild-") as temporary:
        rebuilt = Path(temporary) / "machine"
        run("construction", "build.py", "--output", rebuilt)
        names = ("machine.tm", "machine.native.tm", "raw.native.tm", "labels.json",
                 "grammar.tree.json", "nodes.json", "grammar.json", "sites.json",
                 "instructions.json", "folds.json", "local_folds.json", "receipt.json")
        for name in names:
            if (rebuilt / name).read_bytes() != (ROOT / "machine" / name).read_bytes():
                raise SystemExit("Rebuild differs from frozen artifact: " + name)

    run("source_binding", "check_source.py", "--output", out / "source_binding.json")
    run("emitter_binding", "proof/check_emitter.py", "--output", out / "emitter_binding.json")
    run("command_words", "proof/check_words.py", "--output", out / "command_words.json")
    run("literal_tape", "verification/check_literal.py", "--output", out / "literal")
    for name in ("contracts.json", "list_lemmas.json", "receipt.json"):
        if (out / "literal" / name).read_bytes() != (ROOT / "machine/independent" / name).read_bytes():
            raise SystemExit("Literal certificate differs: " + name)
    run("graph_novelty", "proof/check_novelty.py", "--candidate", ROOT / "machine/machine.tm",
        "--census", ROOT / "comparison", "--output", out / "graph_novelty.json")
    novelty = json.loads((out / "graph_novelty.json").read_text())
    if novelty["status"] != "PASS" or novelty["frontier_objects"] != 83 or novelty["matches"]:
        raise SystemExit("Graph novelty check did not pass.")
    run("guard_numerals", "proof/guard_padding/check_codes.py")
    result = {
        "status": "PASS",
        "candidate_sha256": EXPECTED,
        "working_states": 194,
        "transition_rows": 388,
        "rebuild_identical": True,
        "literal_certificates_identical": True,
        "checks": records,
        "manifest_files_checked": manifest_count,
        "seconds": round(time.monotonic() - started, 3),
        "kernel_checked": False,
        "unconditional_ipra_ConPA_equivalence_claimed": False,
        "scope": "Exact construction, relative source/command certificates, symbolic literal-tape replay, startup and corpus graph novelty.",
    }
    (out / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print("Receipts: " + str(out))


if __name__ == "__main__":
    main()
