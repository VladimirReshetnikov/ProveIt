#!/usr/bin/env python3
"""Read-only, source-level census of the maintained K215 Lean import closure.

This is not a Lean build, theorem checker, or timing benchmark.
Uses standard-library Python 3.11+ and the checkout's lakefile.toml roots.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tomllib

TARGET = "BusyBeaver.ZFC.KEndpoint215"
PREFIX = "Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215"


def strip_comments_strings(text: str) -> str:
    """Remove nested Lean comments and string contents, preserving newlines."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == "/-":
            depth += 1
            i += 2
        elif depth and text[i:i+2] == "-/":
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text[i:i+2] == "--":
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(out)


def imports(text: str) -> list[str]:
    clean = strip_comments_strings(text)
    return [m for line in re.findall(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)", clean)
            for m in line.split()]


def summarize(rows: dict, selected: set[str]) -> dict:
    return {
        "module_count": len(selected),
        "source_bytes": sum(rows[m]["bytes"] for m in selected),
        "source_lines": sum(rows[m]["lines"] for m in selected),
        "modules": sorted(selected),
    }


def census(repo: Path) -> dict:
    cfg = tomllib.loads((repo / "lakefile.toml").read_text())
    roots = {x["name"]: x.get("srcDir", ".") for x in cfg["lean_lib"]}
    rows, external, unresolved, active = {}, set(), set(), set()

    def visit(module: str) -> None:
        if module in rows or module in unresolved or module in external:
            return
        if module == "Init" or module.startswith(("Init.", "Lean.", "Std.")) or module in ("Lean", "Std"):
            external.add(module)
            return
        root = roots.get(module.split(".")[0])
        path = repo / root / (module.replace(".", "/") + ".lean") if root else None
        if path is None or not path.is_file():
            unresolved.add(module)
            return
        if module in active:
            raise ValueError(f"Import cycle at {module}")
        data = path.read_bytes()
        text = data.decode()
        direct = imports(text)
        active.add(module)
        for child in direct:
            visit(child)
        active.remove(module)
        rows[module] = {
            "module": module, "path": str(path.relative_to(repo)),
            "sha256": hashlib.sha256(data).hexdigest(),
            "bytes": len(data), "lines": len(text.splitlines()),
            "imports": direct,
        }

    visit(TARGET)
    selected = set(rows)

    def closure(roots_: list[str]) -> set[str]:
        seen, todo = set(), list(roots_)
        while todo:
            m = todo.pop()
            if m in seen or m not in rows:
                continue
            seen.add(m)
            todo.extend(rows[m]["imports"])
        return seen

    # A disjoint, explicitly ordered decomposition, not independently additive
    # measurements of all transitive root closures.
    groups = [
        ("logical_calibration", ["BusyBeaver.ZFC.KSeedDirect222", "BusyBeaver.ZFC.KLowerQHyp", "BusyBeaver.ZFC.KUpper222"]),
        ("additional_enumerator_and_source", ["BusyBeaver.ZFC.SeedPerm", "BusyBeaver.ZFC.KSource215"]),
        ("additional_generic_runtime", ["BusyBeaver.ZFC.KSim", "BusyBeaver.ZFC.KDenseBridge", "BusyBeaver.ZFC.KTape"]),
        ("remaining_machine_inputs_and_endpoints", [TARGET]),
    ]
    assigned, layers = set(), []
    for name, rootset in groups:
        group = closure(rootset) - assigned
        assigned |= group
        layers.append({"name": name, "roots": rootset, **summarize(rows, group)})
    assert assigned == selected

    hist_path = repo / PREFIX / "simplification/phase15/lean/execution.tar.gz"
    historical = {}
    if hist_path.is_file():
        with tarfile.open(hist_path, "r:gz") as t:
            member = t.getmember("execution/inventory.json")
            inv = json.load(t.extractfile(member))
        old = {r["module"]: r for r in inv["modules"]}
        oldset, todo = set(), [TARGET]
        while todo:
            m = todo.pop()
            if m in oldset or m not in old:
                continue
            oldset.add(m)
            todo.extend(old[m]["imports"])
        changed = [{"module": m, "phase15_sha256": old[m]["source_sha256"],
                    "current_sha256": rows[m]["sha256"]}
                   for m in sorted(oldset & selected)
                   if old[m]["source_sha256"] != rows[m]["sha256"]]
        historical = {
            "source": str(hist_path.relative_to(repo)),
            "member": "execution/inventory.json",
            "historical_module_count": len(oldset),
            "historical_source_bytes_reported_by_phase15_readme": 2052142,
            "removed_from_endpoint_closure": sorted(oldset - selected),
            "added_to_endpoint_closure": sorted(selected - oldset),
            "changed_common_sources": changed,
            "unchanged_common_source_count": len(oldset & selected) - len(changed),
            "note": "Historical byte total is the phase15 README's reported total; current source bytes are freshly measured. No endpoint compilation or archive receipt validation is performed.",
        }

    sites_path = repo / "Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json"
    sites = json.loads(sites_path.read_text())
    kinds = Counter(s[1] for s in sites)
    batches = []
    for m in sorted(selected):
        if re.fullmatch(r"BusyBeaver\.ZFC\.KSites215Batch\d+", m):
            p = repo / rows[m]["path"]
            txt = p.read_text()
            header = re.search(r"blocks (\d+) to (\d+) \((\d+) leaves\)", txt)
            batches.append({"module": m,
                            "kernel_blocks": len(re.findall(r"(?m)^theorem block_\d+\s*:", txt)),
                            "declared_leaf_count": int(header.group(3)) if header else None,
                            "bytes": rows[m]["bytes"], "lines": rows[m]["lines"]})
    assert sum(b["declared_leaf_count"] for b in batches) == len(sites)
    return {
        "status": "COMPLETE_SOURCE_CENSUS" if not unresolved else "INCOMPLETE_SOURCE_CENSUS",
        "evidence_kind": "static_source_analysis_not_kernel_verification",
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip(),
        "target": TARGET,
        "method": "Transitive public/import statements after stripping nested comments and string literals; Lake roots from lakefile.toml. Each local module counted once; source bytes include comments and whitespace. Init/Lean/Std toolchain modules excluded.",
        "totals": summarize(rows, selected),
        "unresolved_imports": sorted(unresolved),
        "external_toolchain_imports": sorted(external),
        "ordered_disjoint_layers": layers,
        "largest_sources": sorted(rows.values(), key=lambda x: (-x["bytes"], x["module"]))[:25],
        "phase15_comparison": historical,
        "site_coverage": {
            "source": str(sites_path.relative_to(repo)),
            "sha256": hashlib.sha256(sites_path.read_bytes()).hexdigest(),
            "leaf_count": len(sites), "instruction_kind_counts": dict(sorted(kinds.items())),
            "branch_outcome_count": len(sites) + kinds["CD"],
            "explanation": "Each decrement CD has zero and nonzero outcomes; every other leaf has one.",
            "batch_count": len(batches), "kernel_block_count": sum(b["kernel_blocks"] for b in batches),
            "batches": batches,
        },
        "sources": list(rows.values()),
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    report = census(args.repo.resolve())
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "commit", "unresolved_imports")}, indent=2))
    print(json.dumps({k:v for k,v in report["totals"].items() if k != "modules"}, indent=2))
    print("Saved", args.output)


if __name__ == "__main__":
    main()
