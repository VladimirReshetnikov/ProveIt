#!/usr/bin/env python3
"""Read-only comparison of two pinned ProveIt arithmetic-DAG suffixes.

This reports source-data equality, not Lean kernel verification.
Usage: python3 inspect_shared_tail.py /absolute/path/to/ProveIt
"""

from pathlib import Path
import importlib.util
import json
import subprocess
import sys
from collections import Counter

sys.dont_write_bytecode = True

BASE = "60e9c5d620c6c387d932876cfa2d9376f64ea56c"


def main() -> None:
    repo = Path(sys.argv[1]).resolve()
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True
    ).strip()
    if commit != BASE:
        raise SystemExit(f"Expected commit {BASE}, found {commit}")
    tools = repo / "Computability/DiophantineConsistency/tools"

    def load(name):
        spec = importlib.util.spec_from_file_location(name, tools / (name + ".py"))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module

    split_generator = load("generate_split_recipe_steps59")
    gap_generator = load("generate_gap_recipe_steps66")
    lean_dir = repo / "Computability/DiophantineConsistency/Lean/DiophantineConsistency"
    generated_sources = {
        "SplitCircuit59.lean": split_generator.g.render(),
        "GapCircuit66.lean": gap_generator.g.render(),
        "SplitCircuitSteps59.lean": split_generator.render(),
        "GapCircuitSteps66.lean": gap_generator.render(),
    }
    source_matches = {
        name: (lean_dir / name).read_text() == source
        for name, source in generated_sources.items()
    }
    if not all(source_matches.values()):
        raise SystemExit(f"Generated sources differ: {source_matches}")
    split = split_generator.nodes[416:]
    gap = gap_generator.nodes[385:]
    remap = {i: i for i in range(18)} | {21: 87, 409: 378, 414: 383, 415: 384}
    normalized = []
    external = set()
    for node in split:
        item = dict(node)
        for key in ("left", "right"):
            if key in item:
                index = item[key]
                if index < 416:
                    external.add(index)
                item[key] = index - 31 if index >= 416 else remap[index]
        normalized.append(item)
    equal = normalized == gap
    result = {
        "base_commit": commit,
        "split_suffix_start": 416,
        "gap_suffix_start": 385,
        "split_suffix_nodes": len(split),
        "gap_suffix_nodes": len(gap),
        "exact_suffix_equality_after_remap": equal,
        "generated_sources_match": source_matches,
        "suffix_node_kinds": dict(Counter(n["kind"] for n in split)),
        "source_json_sha256": {
            "split_natural": split_generator.g.PINS["natural"],
            "gap_natural": gap_generator.g.PINS["natural"],
        },
        "boundary_map": {str(i): remap[i] for i in sorted(external)},
        "local_map": "j -> j - 31 for j >= 416",
        "verification": "Python source-data equality; not a Lean theorem",
    }
    print(json.dumps(result, indent=2))
    if not equal:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
