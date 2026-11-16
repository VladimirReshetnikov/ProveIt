#!/usr/bin/env python3
"""Generate a Lean proof-schedule skeleton from a topologically ordered JSON DAG.

The generated theorem uses ``ProofBuild.step`` from ``lean/KernelCompiler.lean``.
It intentionally leaves the domain-specific local derivations as theorem
arguments; the generic composition itself is exact and kernel-facing.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


def ident(name: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not cleaned or cleaned[0].isdigit():
        cleaned = "n_" + cleaned
    return cleaned


def generate(data: dict[str, Any]) -> str:
    nodes = data.get("nodes")
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("JSON must contain a nonempty 'nodes' list")

    names: list[str] = []
    for raw in nodes:
        name = str(raw["name"])
        if name in names:
            raise ValueError(f"duplicate node name: {name}")
        parents = [str(p) for p in raw.get("parents", [])]
        missing = [p for p in parents if p not in names]
        if missing:
            raise ValueError(f"node {name} has forward parents: {missing}")
        names.append(name)

    formulas = [f"A{i}" for i in range(len(nodes))]
    lines: list[str] = [
        "import KernelCompiler",
        "",
        "/-! Generated proof-carrying topological schedule.",
        "Domain-specific local derivations are explicit theorem arguments. -/",
        "",
        "namespace LeanProofs.ConciseIPRA.KernelFiniteUse.Generated",
        "",
        "open Syn",
        "open scoped Fm",
        "open LeanProofs.ConciseIPRA.KernelFiniteUse",
        "",
        "theorem compile_generated",
        "    {n : Nat} {Γ : List (Fm PTm n)}",
        "    {" + " ".join(formulas) + " : Fm PTm n}",
    ]

    done: list[str] = []
    for i, raw in enumerate(nodes):
        context = "[" + ", ".join(reversed(done)) + "]"
        if not done:
            context = "([] : List (Fm PTm n))"
        comma = "" if i == len(nodes) - 1 else ""
        lines.append(
            f"    (h{i} : {context} ++ Γ ⊢[PRAAx] {formulas[i]})"
        )
        done.append(formulas[i])
    lines[-1] += " :"
    lines.append(f"    Γ ⊢[PRAAx] {formulas[-1]} := by")
    lines.append("  let s0 : ProofBuild Γ [] := ProofBuild.nil")
    built: list[str] = []
    for i, formula in enumerate(formulas):
        new_context = "[" + ", ".join(reversed(built)) + "]"
        if not built:
            new_context = "[]"
        next_list = "[" + ", ".join(reversed(built + [formula])) + "]"
        lines.append(
            f"  let s{i + 1} : ProofBuild Γ {next_list} := ProofBuild.step s{i} h{i}"
        )
        built.append(formula)
    lines.append(f"  exact s{len(nodes)}.get (by simp)")
    lines.extend(
        [
            "",
            "end LeanProofs.ConciseIPRA.KernelFiniteUse.Generated",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text(encoding="utf-8"))
    args.output.write_text(generate(data), encoding="utf-8")


if __name__ == "__main__":
    main()
