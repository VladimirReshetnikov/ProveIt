#!/usr/bin/env python3
"""Prepare a reviewable K215 semantic import cut without editing the repository.

The transformation moves one theorem body verbatim and redirects two imports.
It retains all old public names and the original ZFNative import facade.
No proof compiler is run: closure counts are source-graph measurements only.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess

LEAN_ROOTS = (
    "Computability/BusyBeaver/Lean", "Logic/FirstOrder/Lean",
    "SetTheory/ZF/Lean", "SetTheory/BoundedConsistency/Lean",
)
PREFIX = "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/"
BASE_COMMIT = "2ca3a5c16f0876d2cab842056353c03a1ed2f5f0"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def imports(text):
    # Lean has nested block comments; retain newlines for the import parser.
    out, depth, i = [], 0, 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif pair == "--":
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
                    i += 1
        else:
            out.append(text[i])
            i += 1
    assert depth == 0
    return [m for line in re.findall(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)", "".join(out))
            for m in line.split()]


def collect(repo, overlay):
    rows = {}

    def visit(module):
        if module in rows or module == "Init" or module.startswith("Init."):
            return
        paths = [root + "/" + module.replace(".", "/") + ".lean" for root in LEAN_ROOTS]
        found = [p for p in paths if p in overlay or (repo / p).is_file()]
        if len(found) != 1:
            raise ValueError(("Missing or ambiguous source", module, found))
        relative = found[0]
        data = overlay.get(relative)
        if data is None:
            data = (repo / relative).read_text()
        parents = imports(data)
        rows[module] = {"module": module, "path": relative, "imports": parents,
                        "sha256": digest(data.encode()), "bytes": len(data.encode()),
                        "lines": len(data.splitlines())}
        for parent in parents:
            visit(parent)

    visit("BusyBeaver.ZFC.KEndpoint215")
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    original = (repo / (PREFIX + "ZFNative.lean")).read_text()
    marker = "/-- The semantic content of a model of `ZFax_s`. -/"
    next_marker = "/-- **Every model of ZF is a model of the native theory.** -/"
    start, end = original.index(marker), original.index(next_marker)
    moved = original[start:end]
    assert moved.count("theorem ") == 1 and "theorem models_ZF " in moved
    new_module = (
        "import BusyBeaver.ZFC.InternalOrd\n\n"
        "/-! The semantic fields of a ZF model, independent of every enumerator\n"
        "and register program. The original `ZFNative.models_ZF` name is retained.\n"
        "The theorem body is moved verbatim from ZFNative.lean. -/\n\n"
        "namespace SetTheory.BusyBeaver.ZFC.ZFNative\n\n"
        "open InternalOrd\n\n"
        "universe u\n"
        "variable {V : Type u}\n\n" + moved +
        "end SetTheory.BusyBeaver.ZFC.ZFNative\n"
    )
    old_import = "import BusyBeaver.ZFC.NativeTheory254\n"
    assert original.count(old_import) == 1
    facade = (original[:start] + original[end:]).replace(
        old_import, old_import + "import BusyBeaver.ZFC.ZFModelSemantics\n")
    overlay = {PREFIX + "ZFModelSemantics.lean": new_module,
               PREFIX + "ZFNative.lean": facade}
    for filename, old, new in (
        ("ConstructibleChoice.lean", "ZFNative", "ZFModelSemantics"),
        ("KQ1ZF.lean", "WFTheory", "WFModel"),
    ):
        relative = PREFIX + filename
        text = (repo / relative).read_text()
        line = "import BusyBeaver.ZFC." + old + "\n"
        assert text.count(line) == 1
        overlay[relative] = text.replace(line, "import BusyBeaver.ZFC." + new + "\n")
    patches = []
    sources = []
    for relative, text in overlay.items():
        previous = (repo / relative).read_text() if (repo / relative).is_file() else ""
        target = out / "overlay" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        patches.append("".join(difflib.unified_diff(
            previous.splitlines(keepends=True), text.splitlines(keepends=True),
            fromfile="a/" + relative if previous else "/dev/null",
            tofile="b/" + relative)))
        sources.append({"path": relative, "baseline_sha256": digest(previous.encode()) if previous else None,
                        "proposed_sha256": digest(text.encode())})
    (out / "semantic_import_cut.patch").write_text("".join(patches))
    before, after = collect(repo, {}), collect(repo, overlay)
    removed, added = sorted(before.keys() - after.keys()), sorted(after.keys() - before.keys())
    metrics = {
        "status": "STATIC_SOURCE_ANALYSIS_ONLY",
        "baseline_commit": subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip(),
        "designed_against": BASE_COMMIT,
        "endpoint": "BusyBeaver.ZFC.KEndpoint215",
        "modules_before": len(before), "modules_after": len(after),
        "removed_modules": [before[m] for m in removed],
        "added_modules": [after[m] for m in added],
        "source_bytes_before": sum(r["bytes"] for r in before.values()),
        "source_bytes_after": sum(r["bytes"] for r in after.values()),
        "source_lines_before": sum(r["lines"] for r in before.values()),
        "source_lines_after": sum(r["lines"] for r in after.values()),
        "removed_bytes": sum(before[m]["bytes"] for m in removed),
        "removed_lines": sum(before[m]["lines"] for m in removed),
        "added_bytes": sum(after[m]["bytes"] for m in added),
        "added_lines": sum(after[m]["lines"] for m in added),
        "moved_models_ZF_sha256": digest(moved.encode()),
        "moved_models_ZF_body_verbatim": moved in new_module,
        "sources": sources,
        "limits": ["Import closure, not theorem proof-term dependency closure.",
                   "Old modules and all their public declarations remain in the repository.",
                   "No compiler run or timing improvement is claimed by this script."],
    }
    (out / "import_cut_metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    (out / "closures.json").write_text(json.dumps({"before": before, "after": after}, indent=2) + "\n")
    print(json.dumps({k: v for k, v in metrics.items() if k not in {"sources", "removed_modules", "added_modules"}}, indent=2))


if __name__ == "__main__":
    main()
