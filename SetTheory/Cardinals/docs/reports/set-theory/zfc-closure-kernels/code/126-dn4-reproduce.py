#!/usr/bin/env python3
"""Offline reconstruction and verification of the DN4 225-state machine.

The requested strict bound (<225) has NOT been attained by this packet.
Default: reconstruct, check source semantics, audit the retained universal
certificate, and recompute the entire blank startup in two representations.
--full additionally reproves every universal source-instruction case from the
literal new transition table. --baseline-audit replays the inherited packet.
No mode claims a new end-to-end proof-assistant theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parent
ZIP_SHA = "75b58ce7b5840ef3a3158341f7cf1e601aab67d19ab147d96cf37d1186cb6cbc"
KLABEL_SHA = "3b958e7bc60964dbd95c0d244c3183cc91920a89ed12139cde8e973ae55754f4"
LEGACY_SHA = "0696032e808dfcb8ef334c683008290e7efaaa8b569263cc871a2986d62797c8"
SOURCE_SHA = "172cb099fb980b6389674e99132b637116690dac2d0884e7d3e7bdd738e428d9"
CASES_SHA = "f09621ef287bcd821dfe11bd29422a64cabab6c429abfe32179abb39f1ad2499"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def parse(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, t = line.split()
        key = int(q), int(b)
        require(key not in rows and d in ("L", "R"), "Bad/duplicate table row")
        require(int(b) in (0, 1) and int(w) in (0, 1), "Nonbinary table row")
        rows[key] = [int(w), d, int(t)]
    states = {q for q, b in rows}
    require(len(rows) == 2 * len(states), "Incomplete transition table")
    require(all(t in states or t == 254 for w, d, t in rows.values()), "Unknown target")
    return rows


def encode(rows, start, mapping=None):
    if mapping is None:
        mapping = {q: q for q, b in rows}
        mapping[254] = 254
    mapped = {(mapping[q], b): (w, d, mapping[t]) for (q, b), (w, d, t) in rows.items()}
    return ("#! start " + str(mapping[start]) + "\n" + "".join(
        f"{q} {b} {w} {d} {t}\n" for (q, b), (w, d, t) in sorted(mapped.items())
    )).encode()


def runtime_audit(receipt, table, source, portable):
    report = json.loads(receipt.read_text())
    cases_path = receipt.with_name(report["cases_file"])
    cases = json.loads(cases_path.read_text())
    require(report["status"] == "UNIVERSAL_MATHEMATICAL_PASS", "Runtime did not pass")
    require(report["table_sha256"] == sha(table) == LEGACY_SHA, "Runtime table pin")
    require(report["source_sha256"] == sha(source) == SOURCE_SHA, "Runtime source pin")
    require(report["cases_sha256"] == sha(cases_path) == CASES_SHA, "Runtime case-array pin")
    for key, name in (("engine_sha256", "vendor/proveit/symbolic_runtime.py"),
                      ("helper_sha256", "vendor/proveit/independent_runtime.py"),
                      ("adapter_sha256", "verification/runtime.py")):
        require(report[key] == sha(portable / "baseline226" / name), "Runtime dependency pin: " + key)
    require(report["cases"] == report["expected_cases"] == len(cases) == 6168, "Runtime case census")
    require(report["states"] == 225 and report["rows"] == 450, "Runtime state census")
    require(report["all_rows_used"] and len(set(map(tuple, report["used_rows"]))) == 450, "Runtime row coverage")
    require(set(map(tuple, report["used_rows"])) == set(parse(table)), "Runtime row identity")
    sites = json.loads(source.read_text())
    expected = {(i, positive) for i, (_, op, arg) in enumerate(sites)
                for positive in ((False, True) if op == "CD" else (False,))}
    require(len(expected) == len(cases) and {(c["site_index"], c["positive"]) for c in cases} == expected,
            "Missing or duplicate source guard")
    require(sum(c["symbolic_steps"] for c in cases) == report["symbolic_steps"] == 1483121,
            "Runtime proof-step sum")
    for case in cases:
        duration = case["duration"]
        require(len(duration) == 13 and all(type(x) is int and x >= 0 for x in duration)
                and duration[0] > 0, "Block duration is not provably positive")
    return {k: report[k] for k in ("status", "cases", "states", "rows", "symbolic_steps",
                                  "minimum_actual_steps", "table_sha256", "source_sha256", "cases_sha256")}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output-dir", type=Path, required=True)
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--baseline-audit", action="store_true")
    args = ap.parse_args()
    require(__debug__ and not sys.flags.optimize and not os.environ.get("PYTHONOPTIMIZE"),
            "Python assertions must remain enabled")
    out = args.output_dir.resolve()
    require(out != ROOT and ROOT not in out.parents, "Choose an output directory outside this packet")
    out.mkdir(parents=True, exist_ok=True)
    (out / "logs").mkdir(exist_ok=True)
    start = time.monotonic()
    result = {"status": "IN_PROGRESS", "mode": "full" if args.full else "quick",
              "target_strictly_below_225_met": False, "fresh_end_to_end_kernel_theorem": False, "phases": []}

    def save():
        result["seconds"] = time.monotonic() - start
        dump(out / "replay.json", result)

    def run(label, script, *arguments):
        print(label, flush=True)
        log = out / "logs" / (label + ".log")
        with log.open("w") as f:
            proc = subprocess.run([sys.executable, "-B", str(script), *map(str, arguments)],
                                  stdout=f, stderr=subprocess.STDOUT)
        require(proc.returncode == 0, label + " failed: " + log.read_text()[-3000:])
        result["phases"].append(label)
        save()

    try:
        if (ROOT / "manifest.json").exists():
            manifest = json.loads((ROOT / "manifest.json").read_text())
            for name, digest in manifest["files"].items():
                relative = Path(name)
                require(not relative.is_absolute() and ".." not in relative.parts, "Unsafe manifest path")
                require(sha(ROOT / relative) == digest, "Manifest mismatch: " + name)
            result["manifest_files_checked"] = len(manifest["files"])
        archive = ROOT / "inputs/K225_Construction_2026-10-19.zip"
        require(sha(archive) == ZIP_SHA, "Wrong retained baseline archive")
        with zipfile.ZipFile(archive) as z:
            for name in z.namelist():
                part = Path(name)
                require(not part.is_absolute() and ".." not in part.parts, "Unsafe archive member")
            z.extractall(out / "inherited")
        portable = out / "inherited/K225_Construction_2026-10-19/portable"
        require(portable.is_dir(), "Wrong baseline archive layout")
        inherited_manifest = json.loads((portable / "manifest.json").read_text())
        for name, digest in inherited_manifest["files"].items():
            relative = Path(name)
            require(not relative.is_absolute() and ".." not in relative.parts, "Unsafe inherited path")
            require(sha(portable / relative) == digest, "Inherited manifest mismatch: " + name)
        result["inherited_manifest_files_checked"] = len(inherited_manifest["files"])
        if args.baseline_audit:
            run("baseline225", portable / "reproduce.py", "--full", "--output-dir", out / "baseline225")

        patch = json.loads((ROOT / "inputs/table_patch.json").read_text())
        baseline_table = portable / "results/candidate225.klabels.tm"
        require(sha(baseline_table) == patch["baseline_sha256"], "Table patch baseline mismatch")
        table = parse(baseline_table)
        for row in patch["rows"]:
            key = row["state"], row["read"]
            require(table.get(key) == row["before"], "Table patch precondition failed")
            if row["after"] is None:
                del table[key]
            else:
                table[key] = row["after"]
        new_k = out / "k225_dn.klabels.tm"
        new_k.write_bytes(encode(table, 0))
        require(sha(new_k) == patch["result_sha256"] == KLABEL_SHA, "Constructed table mismatch")
        require(new_k.read_bytes() == (ROOT / "machine/k225_dn.klabels.tm").read_bytes(), "Retained table mismatch")
        require(len(parse(new_k)) == 450, "Wrong working-state count")
        states = sorted({q for q, b in table})
        dense = {q: i for i, q in enumerate(states)}
        dense[254] = 225
        require(len(set(dense.values())) == len(dense), "Dense relabeling is not bijective")
        (out / "k225_dn.tm").write_bytes(encode(table, 0, dense))
        retained_dense = ROOT / "machine/k225_dn.tm"
        if retained_dense.exists():
            require(retained_dense.read_bytes() == (out / "k225_dn.tm").read_bytes(), "Dense table mismatch")
        legacy = {int(k): v for k, v in json.loads((portable / "baseline226/source/legacy_state_map.json").read_text())["k230_to_old"].items()}
        # In the inherited map key 230 names a HALT label. Here 230 is a new
        # working state, so it must be mapped explicitly to a fresh label.
        legacy.update({230: 530, 231: 531, 232: 532, 254: 254})
        restricted_legacy = {q: legacy[q] for q in states + [254]}
        require(len(set(restricted_legacy.values())) == len(restricted_legacy), "Legacy relabeling is not bijective")
        new_l = out / "k225_dn.legacy.tm"
        new_l.write_bytes(encode(table, 0, restricted_legacy))
        require(sha(new_l) == LEGACY_SHA and new_l.read_bytes() == (ROOT / "machine/k225_dn.legacy.tm").read_bytes(),
                "Legacy table mismatch")
        dump(out / "renumbering.json", {"normalized_to_dense": dense, "normalized_to_legacy": restricted_legacy,
                                       "dense_start": dense[0], "dense_dispatcher": dense[84], "dense_halt": dense[254]})
        result["phases"].append("exact_table_reconstruction_and_bijective_relabeling")

        builder = portable / "baseline226/vendor/proveit/build_zfc235.py"
        dag = portable / "baseline226/vendor/k230-rocq/coq/prog/Dag230.v"
        base_source = portable / "results/sites225.json"
        recipe = ROOT / "inputs/recipe_dn4.json"
        run("source_reconstruction", ROOT / "verification/reconstruct_full_dn.py",
            "--baseline", base_source, "--recipe", recipe, "--builder", builder, "--output", out / "sites.compact.json")
        new_source = out / "sites.json"
        dump(new_source, json.loads((out / "sites.compact.json").read_text()))
        require(sha(new_source) == SOURCE_SHA and new_source.read_bytes() == (ROOT / "machine/sites.json").read_bytes(),
                "Constructed source mismatch")
        run("source_semantics", ROOT / "verification/verify_full_dn_semantics.py",
            "--baseline", base_source, "--source", new_source, "--recipe", recipe,
            "--builder", builder, "--dag", dag, "--output", out / "source_semantics.json")
        run("complete_blank_startup", portable / "baseline226/verification/startup.py", new_l,
            "--steps", 409835, "--output", out / "startup.json")
        result["retained_runtime_audit"] = runtime_audit(ROOT / "receipts/runtime225.json", new_l, new_source, portable)
        if args.full:
            run("universal_binary_runtime", portable / "baseline226/verification/runtime.py",
                new_l, new_source, out / "runtime225.json")
            result["fresh_runtime_audit"] = runtime_audit(out / "runtime225.json", new_l, new_source, portable)
        result.update(status="FULL_REPLAY_PASS" if args.full else "QUICK_REPLAY_PASS", working_states=225,
                      rows=450, source_leaves=4745, source_dag_nodes=211, maximum_depth=38,
                      maximum_zero_run=6, startup_steps=409835,
                      dense_table_sha256=sha(out / "k225_dn.tm"),
                      mathematical_scope="Literal TM-to-source simulation by ordinary induction, plus the separate written numeric-calculus proof. No new end-to-end kernel theorem.")
        save()
        print(json.dumps(result, indent=2), flush=True)
    except Exception as error:
        result.update(status="FAIL", error=repr(error))
        save()
        raise


if __name__ == "__main__":
    main()
