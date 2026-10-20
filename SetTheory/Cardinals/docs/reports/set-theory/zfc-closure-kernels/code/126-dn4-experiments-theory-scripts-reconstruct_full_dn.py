#!/usr/bin/env python3
"""Reconstruct a full-DN source from the pinned K225 source and a recipe.

Keep verify_full_dn_semantics.py alongside this file.  No workspace paths,
network access, or third-party Python packages are used.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

import verify_full_dn_semantics as v


def reconstruct(baseline: Path, recipe_path: Path, builder_path: Path):
    raw = baseline.read_bytes()
    v.require(hashlib.sha256(raw).hexdigest() == v.BASELINE_SHA256, "Wrong baseline225 source")
    v.require(hashlib.sha256(builder_path.read_bytes()).hexdigest() == v.BUILDER_SHA256, "Wrong source-graph builder")
    spec = importlib.util.spec_from_file_location("source_builder", builder_path)
    builder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder)
    old = builder.tree(json.loads(raw))
    recipe = json.loads(recipe_path.read_text())
    v.require(recipe["and_ex_paths"] == v.XPATHS and recipe["and_and_acdup_paths"] == [v.BPATH], "Wrong replacement paths")
    v.require(v.flatten_shape(recipe["shape_x"]) == list(range(4)), "Wrong existential/conjunction macro order")
    v.require(v.flatten_shape(recipe["shape_b"]) == list(range(5)), "Wrong bundle-ending macro order")
    macros = {name: v.at(old, path) for name, (_, path) in v.MACROS.items()}
    for path in v.XPATHS:
        v.require(v.at(old, path) == (macros["and"], macros["ex"]), "Wrong old and/ex subtree")
    v.require(v.at(old, v.BPATH) == (macros["and"], (macros["and"], macros["ac_s1s2"])), "Wrong old bundle subtree")
    xnew = v.build(recipe["shape_x"], [macros[n] for n in ("neg", "im", "all", "neg")])
    bnew = v.build(recipe["shape_b"], [macros[n] for n in ("neg", "im", "im", "neg", "ac_s1s2")])
    new = v.replace_paths(old, {**{path: xnew for path in v.XPATHS}, v.BPATH: bnew})
    sites = builder.sites(new)
    builder.graph(sites)
    return builder.json_bytes(sites, compact=True), builder.metrics(new)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("baseline", "recipe", "builder", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    data, metrics = reconstruct(args.baseline, args.recipe, args.builder)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(data)
    print(json.dumps({"source_sha256": hashlib.sha256(data).hexdigest(), "source_metrics": metrics}, indent=2))


if __name__ == "__main__":
    main()
