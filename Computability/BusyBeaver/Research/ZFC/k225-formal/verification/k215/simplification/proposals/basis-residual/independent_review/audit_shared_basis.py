#!/usr/bin/env python3
"""Independently measure and inspect a shared-basis overlay, without compiling it."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import tarfile
from pathlib import Path


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def imports(source: str) -> list[str]:
    return [word for line in source.splitlines() if line.startswith("import ")
            for word in line.split("--", 1)[0].split()[1:]]


def signature(source: str, theorem: str) -> str:
    match = re.search(r"^theorem " + re.escape(theorem) + r"\b([\s\S]*?):=", source, re.M)
    if match is None:
        raise ValueError(theorem)
    return " ".join(match.group(0).rsplit(":=", 1)[0].split())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--overlay", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    overlay = args.overlay.resolve()
    base = repo / "Computability/BusyBeaver/Lean"
    archive = repo / "Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase12/lean/execution.tar.gz"
    with tarfile.open(archive) as saved:
        inventory = json.load(saved.extractfile("execution/inventory.json"))
    source = {}
    for row in inventory["modules"]:
        name = row["source"]
        relative = next(name.split(marker, 1)[1] for marker in ("/Proofs/", "/candidate/") if marker in name)
        source[row["module"]] = (repo / relative).read_bytes()
    original = dict(source)
    replacements = {}
    for path in sorted(overlay.rglob("*.lean")):
        module = str(path.relative_to(overlay))[:-5].replace("/", ".")
        replacements[module] = path.read_bytes()
    source.update(replacements)

    def closure(sources: dict[str, bytes]) -> set[str]:
        active: set[str] = set()
        complete: set[str] = set()
        def visit(module: str) -> None:
            if module not in sources or module in complete:
                return
            if module in active:
                raise ValueError("Import cycle: " + module)
            active.add(module)
            for child in imports(sources[module].decode()):
                visit(child)
            active.remove(module)
            complete.add(module)
        visit("BusyBeaver.ZFC.KEndpoint215")
        return complete

    old_closure = closure(original)
    new_closure = closure(source)
    old_core = original["BusyBeaver.ZFC.DominatedImplication"].decode()
    new_core = source["BusyBeaver.ZFC.DominatedImplication"].decode()
    old_luk = original["BusyBeaver.ZFC.Lukasiewicz"].decode()
    new_luk = source["BusyBeaver.ZFC.Lukasiewicz"].decode()
    pure = source["BusyBeaver.ZFC.ImplicationalBasis"].decode()
    old_prefix = old_core.split("\nend\n#print", 1)[0].rstrip()
    new_prefix = new_core.split("/-- K is already present", 1)[0].rstrip()
    marker = "namespace SetTheory.BusyBeaver.ZFC.Tarski\n"
    old_tarski = old_luk[old_luk.index(marker):]
    new_tarski = new_luk[new_luk.index(marker):]
    names = ["k", "peirce", "composition", "s"]
    api_comparison = {name: signature(old_luk, name) == signature(pure, name) for name in names}
    relevant = ["BusyBeaver.ZFC.DominatedImplication", "BusyBeaver.ZFC.Lukasiewicz", "BusyBeaver.ZFC.ImplicationalBasis"]
    old_bytes = sum(len(original[x]) for x in relevant if x in original)
    new_bytes = sum(len(source[x]) for x in relevant)
    old_lines = sum(len(original[x].decode().splitlines()) for x in relevant if x in original)
    new_lines = sum(len(source[x].decode().splitlines()) for x in relevant)
    old_dag = old_core.count("h.mp") - 1  # lift_right is an inference adapter.
    old_luk_dag = len(re.findall(r"^private theorem cd_\d+", old_luk, re.M)) - 1
    new_dag = new_core.count("h.mp") - 1
    record = {
        "scope": "Independent source and dependency-graph check only; no Lean compilation or endpoint axiom inference.",
        "preserved_current_core_before_extension": old_prefix == new_prefix,
        "preserved_tarski_block_byte_for_byte": old_tarski == new_tarski,
        "public_type_text_equal_up_to_whitespace": api_comparison,
        "old_sources_bytes": old_bytes, "new_sources_bytes": new_bytes,
        "source_byte_reduction": old_bytes - new_bytes,
        "old_sources_lines": old_lines, "new_sources_lines": new_lines,
        "source_line_reduction": old_lines - new_lines,
        "old_endpoint_module_count": len(old_closure),
        "new_endpoint_module_count": len(new_closure),
        "old_endpoint_source_bytes": sum(len(original[x]) for x in old_closure),
        "new_endpoint_source_bytes": sum(len(source[x]) for x in new_closure),
        "added_endpoint_modules": sorted(new_closure - old_closure),
        "removed_endpoint_modules": sorted(old_closure - new_closure),
        "old_schematic_MP_nodes_excluding_lift_right": old_dag + old_luk_dag,
        "new_schematic_MP_nodes_excluding_lift_right": new_dag,
        "old_schematic_MP_nodes_including_lift_right": old_dag + old_luk_dag + 1,
        "new_schematic_MP_nodes_including_lift_right": new_dag + 1,
        "schematic_MP_count_scope": "Maintained dominated proof plus old independent cd_0..cd_106 implication DAG versus extended shared core; excludes the unchanged Tarski bridge. No proof-term-size or shortest-proof claim.",
        "files": {name: {"bytes": len(data), "lines": len(data.decode().splitlines()), "sha256": sha(data)} for name, data in replacements.items()},
    }
    assert record["preserved_current_core_before_extension"]
    assert record["preserved_tarski_block_byte_for_byte"]
    assert all(api_comparison.values())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
