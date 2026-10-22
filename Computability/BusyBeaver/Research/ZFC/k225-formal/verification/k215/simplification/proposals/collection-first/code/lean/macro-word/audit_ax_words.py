#!/usr/bin/env python3
"""Reproduce the literal AX-word census; this is finite evidence, not a proof."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, required=True)
    args = ap.parse_args()
    repo = args.repo.resolve()
    base = "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95"
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if actual != base:
        raise SystemExit(f"Expected {base}, got {actual}")
    root = repo / "Computability/BusyBeaver/Lean/BusyBeaver/ZFC"
    result, words, texts = {"base_commit": actual, "files": {}}, [], []
    for name in ("L2AxiomsPerm", "L2AxiomsDom"):
        path = root / (name + ".lean")
        data = path.read_bytes()
        text = data.decode("utf-8")
        word_text = text.split("def axWord :", 1)[1].split("theorem axWord_checked", 1)[0]
        word = [(a, int(n)) for a, n in re.findall(r"\(\.(\w+), (\d+)\)", word_text)]
        words.append(word)
        texts.append(text)
        result["files"][name + ".lean"] = {
            "bytes": len(data), "lines": len(text.splitlines()),
            "sha256": hashlib.sha256(data).hexdigest(), "atoms": len(word)}
    perm, dom = words
    assert len(perm) == len(dom) == 156
    sem_perm, sem_dom = ([a for a, _ in word] for word in words)
    assert sem_perm[:6] == sem_dom[:6]
    assert sem_perm[6:8] == ["cons", "readp1"]
    assert sem_dom[6:8] == ["readp1", "cons"]
    assert sem_perm[8:] == sem_dom[8:]
    normalized = texts[1]
    for a, b in (("L2Dom", "L2Perm"), ("DagDom", "DagPerm"),
                 ("dagDom", "dagPerm"), ("EnumDom", "EnumPerm")):
        normalized = normalized.replace(a, b)
    line_diffs = [i + 1 for i, (a, b) in enumerate(zip(texts[0].splitlines(), normalized.splitlines())) if a != b]
    assert line_diffs == [114, 115]
    result.update({"common_semantic_prefix_atoms": 6, "common_semantic_suffix_atoms": 148,
        "semantic_difference_positions_zero_based": [6, 7],
        "node_label_difference_positions_zero_based": [i for i, (a, b) in enumerate(zip(perm, dom)) if a[1] != b[1]],
        "namespace_normalized_differing_source_lines": line_diffs})
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
