#!/usr/bin/env python3
"""Offline, standard-library verification of this report's technical artifacts.

Default: source/table hashes, table structures, exact 253 regeneration, raw252
normalization, countermodel regressions, and the three frozen compiler recipes.
--full also repeats the 288-control cost search and seven newer PSC recipes.
No proof assistant is run.
--all-hashes optionally checks the final report-wide SHA256SUMS, if supplied.
"""
from __future__ import annotations

import argparse
from collections import deque
from contextlib import redirect_stdout
import hashlib
import importlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

if not __debug__:
    raise SystemExit("Verification requires enabled assertions; do not use python -O or -OO.")

sys.dont_write_bytecode = True


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def table(path, expected):
    rows = {}
    start = None
    for number, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        if line.startswith("#!"):
            fields = line.split()
            require(fields[:2] == ["#!", "start"] and len(fields) == 3
                    and start is None, f"{path.name}:{number}: invalid directive")
            start = fields[2]
        elif not line.startswith("#"):
            fields = line.split()
            require(len(fields) == 5, f"{path.name}:{number}: wrong row width")
            q, bit, write, move, target = fields
            require(bit in "01" and len(bit) == 1 and write in "01" and len(write) == 1
                    and move in ("L", "R"), f"{path.name}:{number}: nonbinary/non-LR action")
            require((q, bit) not in rows, f"{path.name}:{number}: duplicate row")
            rows[q, bit] = (write, move, target)
    states = {q for q, _ in rows}
    require(start in states, f"{path.name}: invalid start")
    require(len(states) == expected["working_states"], f"{path.name}: state count")
    require(len(rows) == expected["explicit_transition_rows"], f"{path.name}: row count")
    terminals = {action[2] for action in rows.values()} - states
    require(terminals == {str(expected["terminal"])}, f"{path.name}: terminal targets")
    missing = [[q, b] for q in sorted(states) for b in ("0", "1") if (q, b) not in rows]
    require(missing == expected.get("missing_transition_rows", []), f"{path.name}: missing rows")
    if expected["numeric"]:
        require(states == {str(i) for i in range(len(states))} and start == "0",
                f"{path.name}: noncanonical numeric labels")
    reached, pending = {start}, deque([start])
    while pending:
        q = pending.popleft()
        for bit in ("0", "1"):
            action = rows.get((q, bit))
            if action and action[2] not in reached:
                reached.add(action[2])
                if action[2] in states:
                    pending.append(action[2])
    require(states <= reached, f"{path.name}: counted graph-unreachable states")
    return start, rows


def totalized_raw_bytes(start, rows):
    states = {q for q, _ in rows}
    require(("1.inc", "1") not in rows, "Raw table unexpectedly has the missing row")
    rows = dict(rows)
    rows["1.inc", "1"] = ("1", "R", "halt")
    ordered = [start] + sorted(states - {start})
    labels = {q: i for i, q in enumerate(ordered)}
    labels["halt"] = len(ordered)
    lines = ["#! start 0"]
    for q in ordered:
        for bit in ("0", "1"):
            write, move, target = rows[q, bit]
            lines.append(f"{labels[q]} {bit} {write} {move} {labels[target]}")
    return ("\n".join(lines) + "\n").encode("ascii")


def source_hashes(root, manifest):
    for item in manifest["files"]:
        path = root / item["path"]
        require(path.is_file(), "Missing source: " + item["path"])
        require(path.stat().st_size == item["bytes"] and digest(path) == item["sha256"],
                "Source bytes differ: " + item["path"])
        if item.get("git_blob_sha1"):
            data = path.read_bytes()
            blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            require(blob == item["git_blob_sha1"], "Git blob differs: " + item["path"])


def all_hashes(root):
    path = root / "SHA256SUMS"
    require(path.exists(), "--all-hashes requires a finalized SHA256SUMS")
    checked = 0
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        sha, name = line.split(maxsplit=1)
        name = name.removeprefix("*")
        target = (root / name).resolve()
        require(target.is_relative_to(root.resolve()), "Unsafe path in SHA256SUMS")
        require(digest(target) == sha, "Final archive hash differs: " + name)
        checked += 1
    return checked


def compiler_recipes(root, temporary, evidence):
    repo = root / "vendor/proveit"
    source = repo / "Computability/BusyBeaver/Research/ZFC"
    backend_dir = temporary / "backend"
    backend_dir.mkdir()
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        shutil.copyfile(repo / "lib/jeff-busy-beaver-zfc254/ZF/generator" / name,
                        backend_dir / name)
    sys.path.insert(0, str(source))
    sys.path.insert(0, str(backend_dir))
    api = importlib.import_module("theory_backend_experiment")
    backend = importlib.import_module("TMBuilder")
    experiment = importlib.import_module("repair_cost_experiment")
    nodes, names = api.parse_dag(api.git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    api.old_contract(nodes)
    builder, baseline = experiment.compile_program(
        api, backend, nodes, names, api.equality_free_rows(reordered=True, dual=True),
        "raw_equality_free_C_G_shared_dual_base3")
    baseline_file = temporary / "raw252.tm"
    builder.tm.save(str(baseline_file))
    require(baseline_file.read_bytes() == (root / "machines/raw252-named.tm").read_bytes(),
            "Raw 252 compiler output changed")
    costs = {"raw": baseline["working_states"]}
    for control, filename in (("U", "diagnostic-U-259-named.tm"),
                              ("P", "diagnostic-P-264-named.tm")):
        record = evidence["controls"][control]
        recipe = record["best_recipe"]
        program, _ = experiment.make_program(api, control,
                                             [9-i for i in recipe["rho_order"]],
                                             recipe["bundle_tree"])
        builder, result = experiment.compile_program(api, backend, nodes, names,
                                                      program, "diagnostic_" + control)
        output = temporary / filename
        builder.tm.save(str(output))
        require(output.read_bytes() == (root / "machines" / filename).read_bytes(),
                control + " diagnostic table differs from its frozen recipe")
        require(result["working_states"] == record["minimum_working_states_in_this_search"],
                control + " diagnostic state count differs")
        costs[control] = result["working_states"]
    return costs


def exclusion_checks(model, evidence):
    def decode(p, labels):
        if p == 1:
            return model.F
        kind, a, b = p
        if kind == "rel":
            return model.R(labels[a], labels[b])
        if kind == "all":
            return model.All(labels[a], decode(b, labels))
        if kind == "imp":
            return model.Imp(decode(a, labels), decode(b, labels))
        raise ValueError("Unknown control AST node")
    for control, item in evidence["countermodel_exclusion_witnesses"].items():
        formula = decode(evidence["controls"][control]["formula_AST"], item["labels"])
        environment = {int(k): v for k, v in item["assignment"].items()}
        require(not model.evaluate(formula, environment), "Control does not exclude witness: " + control)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--full", action="store_true")
    parser.add_argument("--all-hashes", action="store_true")
    parser.add_argument("--output", type=Path, help="Optional path for this verification's JSON record")
    args = parser.parse_args()
    root = args.root.resolve()
    started = time.monotonic()
    manifest = json.loads((root / "evidence/source_manifest.json").read_text())
    source_hashes(root, manifest)
    tables = json.loads((root / "evidence/table_manifest.json").read_text())
    parsed = {}
    for item in tables["machines"]:
        path = root / item["path"]
        require(digest(path) == item["sha256"], "Table hash differs: " + item["path"])
        parsed[path.name] = table(path, item)
    print(f"Checked {len(manifest['files'])} pinned/authored source hashes and {len(parsed)} tables.", flush=True)
    sys.path.insert(0, str(root / "code"))
    regeneration = importlib.import_module("regenerate_253")
    require(regeneration.generate(root / "machines/zfc_254.tm") ==
            (root / "machines/zfc_253.tm").read_bytes(), "253 regeneration differs")
    require(totalized_raw_bytes(*parsed["raw252-named.tm"]) ==
            (root / "machines/raw-candidate-252.tm").read_bytes(), "Raw normalization differs")
    print("Regenerated exact 253 table and exact normalized raw 252 table.", flush=True)

    model = importlib.import_module("equality_free_countermodel")
    with redirect_stdout(io.StringIO()):
        actual = model.main()
    expected = json.loads((root / "evidence/countermodel_results.json").read_text())
    require(actual == expected, "Countermodel regressions differ from recorded results")
    repair = json.loads((root / "evidence/repair_cost_results.json").read_text())
    exclusion_checks(model, repair)
    print("Countermodel regressions and both control-exclusion witnesses passed.", flush=True)

    with tempfile.TemporaryDirectory(prefix="zfc-report-verify-") as directory:
        temporary = Path(directory)
        costs = compiler_recipes(root, temporary, repair)
        print("Frozen compiler recipes reproduced exactly: raw252, diagnostic259, diagnostic264.", flush=True)
        if args.full:
            output = temporary / "full-results.json"
            command = [sys.executable, "-B", str(root / "code/repair_cost_experiment.py"),
                       "--repo", str(root / "vendor/proveit"),
                       "--backend", str(temporary / "full-backend"),
                       "--output-dir", str(temporary / "full-tables"),
                       "--results", str(output)]
            completed = subprocess.run(command, text=True, capture_output=True, check=True)
            full = json.loads(output.read_text())
            require(full["control_compilations"] == 288, "Wrong full-search case count")
            for control in ("U", "P"):
                for key in ("cost_distribution", "minimum_working_states_in_this_search",
                            "best_table_sha256", "cases", "records"):
                    require(full["controls"][control][key] == repair["controls"][control][key],
                            "Full-search result differs: " + control + "/" + key)
            print("All 288 sampled repair variants reproduced with exact recorded costs and recipes.", flush=True)
            psc_dir = root / "supplement/psc-e7c4cadf"
            psc_output = temporary / "psc-results.json"
            environment = dict(os.environ)
            environment["PYTHONPATH"] = str(root / "vendor/proveit/Computability/BusyBeaver/Research/ZFC")
            subprocess.run([sys.executable, "-B", str(psc_dir / "psc_backend_experiment.py"),
                            "--scratch", str(temporary / "psc-backend"),
                            "--output-evidence", str(psc_output)],
                           env=environment, text=True, capture_output=True, check=True)
            actual_psc = json.loads(psc_output.read_text())
            expected_psc = json.loads((psc_dir / "reproduced-results.json").read_text())
            require(actual_psc == expected_psc, "Latest PSC fixed recipes or core checks differ")
            require((temporary / "psc-backend/offset_bottom4_repair93.tm").read_bytes() ==
                    (psc_dir / "offset_bottom4_repair93.tm").read_bytes(),
                    "Distinct latest PSC252 table differs")
            print("Seven latest PSC fixed recipes and all core checks reproduced exactly.", flush=True)
    checked_final_hashes = all_hashes(root) if args.all_hashes else None
    result = {"status": "PASS", "network_used": False,
              "local_Coq_build": False, "local_Lean_build": False,
              "proof_assistant_result_claimed": False,
              "countermodel_case_counts": actual["cases"],
              "compiler_recipe_states": costs,
              "source_files_checked": len(manifest["files"]),
              "machine_tables_checked": len(parsed),
              "full_288_control_search": args.full,
              "latest_PSC_seven_fixed_recipes_reproduced": args.full,
              "latest_PSC_144_and_200_searches_rerun": False,
              "final_archive_hashes_checked": checked_final_hashes,
              "python_version": sys.version.split()[0],
              "elapsed_seconds": round(time.monotonic() - started, 3)}
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
