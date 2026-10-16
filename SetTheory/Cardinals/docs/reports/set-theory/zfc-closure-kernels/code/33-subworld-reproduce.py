#!/usr/bin/env python3
"""Quick, offline checks for the report artifacts; no consistency-machine claim."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON record; otherwise print only")
    args = parser.parse_args()
    if not __debug__:
        parser.error("Run without -O: the checks use assertions")
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    stages = []

    def run(name, command, cwd=ROOT):
        p = subprocess.run(command, cwd=cwd, env=env, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if p.returncode:
            raise RuntimeError(name + " failed:\n" + p.stdout)
        stages.append({"name": name, "exit_code": p.returncode})
        return p.stdout

    # The seven ProveIt sources and six upstream compiler inputs are pinned.
    upstream = json.loads((ROOT / "compiler_experiments/UPSTREAM.json").read_text())
    for item in upstream:
        path = ROOT / item["path"]
        assert digest(path) == item["sha256"], item["path"]
        if "git_blob" in item:
            b = path.read_bytes()
            blob = hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
            assert blob == item["git_blob"], item["path"]
    stages.append({"name": "compiler_dependency_hashes", "files": len(upstream), "pass": True})

    for script, expected in [("kernel_counts.py", "kernel_counts.json"),
                             ("check_pair_endpoints.py", "check_pair_endpoints.json")]:
        actual = json.loads(run(script, [sys.executable, "-B", str(ROOT / "code" / script)]))
        assert actual == json.loads((ROOT / "data" / expected).read_text()), script
        stages[-1]["exact_record_match"] = True

    test_output = run("reference_checker", [sys.executable, "-B", "-m", "unittest",
                                          "-v", "test_k2_tableau.py"],
                      ROOT / "reference_checker")
    assert "Ran 7 tests" in test_output and "\nOK\n" in test_output
    stages[-1]["test_groups"] = 7

    with tempfile.TemporaryDirectory(prefix="zfc_report_replay_") as work:
        temp = Path(work)
        row_record = temp / "rows.json"
        run("independent_row_witnesses",
            [sys.executable, "-B", "verify_row_witnesses.py", "--json", str(row_record)],
            ROOT / "machine_experiments")
        rows = json.loads(row_record.read_text())
        assert rows["distinct_transition_rows"] == 504
        assert rows["witness_replay_steps"] == 26035
        assert rows["trailing_spare_blocks_zero"] is True
        stages[-1].update(rows=504, replay_steps=26035,
                          symbolic_oracles=False, zero_spare_blocks=True)

        for basis, folder, states in [("original", "original_expanded", 268),
                                      ("protected", "protected_correct_cost", 269)]:
            stored = ROOT / "compiler_experiments" / folder
            target = temp / basis
            run("compiler_" + basis,
                [sys.executable, "-B", str(ROOT / "compiler_experiments/basis_experiment.py"),
                 "--basis", basis, "--recipe", str(stored / "results.json"),
                 "--iterations", "0", "--output", str(target)])
            for name in ["candidate.tm", "candidate.named.tm",
                         "candidate.labels.json", "candidate.dag.json"]:
                assert (target / name).read_bytes() == (stored / name).read_bytes(), (basis, name)
            record = json.loads((target / "results.json").read_text())
            assert record["table"]["working_states"] == states
            assert record["word_expansion_exact"] and record["operation_silent_closed"]
            stages[-1].update(working_states=states,
                              numeric_table_sha256=digest(target / "candidate.tm"),
                              four_artifacts_byte_identical=True)

    report = {
        "status": "PASS",
        "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "python": sys.version.split()[0],
        "driver_sha256": digest(Path(__file__)),
        "scope": "Finite reference/coverage/compiler checks; excludes the full search and Lean build.",
        "stages": stages,
    }
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.resolve().write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
