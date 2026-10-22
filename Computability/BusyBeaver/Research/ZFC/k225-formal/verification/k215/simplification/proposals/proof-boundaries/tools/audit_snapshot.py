#!/usr/bin/env python3
"""Read-only source census for the K215 proof-boundary proposal.

This checks source identities and literal word structure. It is not a proof
checker and does not replace Lean, Rocq, or the endpoint verification drivers.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

PIN = "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95"
ROOTS = ["Computability/BusyBeaver/Lean", "Logic/FirstOrder/Lean",
         "SetTheory/ZF/Lean", "SetTheory/BoundedConsistency/Lean"]
ZFC = "Computability/BusyBeaver/Research/ZFC"
LEAN = "Computability/BusyBeaver/Lean/BusyBeaver/ZFC"
FOCUS = [
    f"{LEAN}/{n}.lean" for n in [
        "KEndpoint215", "KEndpoint", "EnumPerm", "EnumDom", "SeedPerm",
        "L2AxiomsPerm", "L2AxiomsDom", "L2Axioms222", "L2RootPerm", "L2RootDom",
        "KQ1Model", "QuotientModel", "KLowerTag", "KLowerQHyp", "InductiveAttempts",
        "KDenseBridge", "KSource215Data", "KSource215Program", "KSites215"]
] + [
    f"{ZFC}/k225-formal/rocq/rocq-extension/coq/215/{n}.v"
    for n in ["EnumPerm", "L1_CompPerm", "SeedPerm", "Source215", "CorrectDense215"]
] + [f"{ZFC}/candidate-k215/k215.tm"]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def imports(path: Path) -> list[str]:
    out = []
    for line in path.read_text().splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+([^/]+)", line)
        if match:
            out.extend(match.group(1).split())
    return out


def audit(repo: Path) -> dict:
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    module_files = {}
    for relative in ROOTS:
        base = repo / relative
        if not base.is_dir():
            raise RuntimeError(f"Missing source root: {relative}")
        for path in base.rglob("*.lean"):
            if ".lake" not in path.parts:
                module_files[str(path.relative_to(base))[:-5].replace("/", ".")] = path
    seen, external = set(), set()
    pending = ["BusyBeaver.ZFC.KEndpoint215"]
    while pending:
        name = pending.pop()
        if name in seen or name in external:
            continue
        path = module_files.get(name)
        if path is None:
            external.add(name)
        else:
            seen.add(name)
            pending.extend(imports(path))
    unresolved = sorted(n for n in external if n.split(".")[0] not in {"Init", "Lean", "Std"})
    if unresolved:
        raise RuntimeError("Unresolved project imports: " + ", ".join(unresolved))
    rows = []
    for name in sorted(seen):
        path = module_files[name]
        data = path.read_bytes()
        rows.append(dict(module=name, path=str(path.relative_to(repo)), bytes=len(data),
                         lines=len(data.splitlines()), sha256=digest(data), imports=imports(path)))
    files = []
    for relative in FOCUS:
        path = repo / relative
        if not path.is_file():
            files.append(dict(path=relative, missing=True))
            continue
        data = path.read_bytes()
        original = subprocess.check_output(["git", "show", f"{PIN}:{relative}"], cwd=repo)
        files.append(dict(path=relative, bytes=len(data), lines=len(data.splitlines()),
                          sha256=digest(data), equal_to_pin=(data == original)))
    words = []
    for variant in ["Dom", "Perm"]:
        source = (repo / LEAN / f"L2Axioms{variant}.lean").read_text()
        word = source[source.index("def axWord :"):source.index("theorem axWord_checked")]
        words.append([(op, int(n)) for op, n in re.findall(r"\(\.([A-Za-z0-9]+),\s*(\d+)\)", word)])
    dom, perm = words
    assert len(dom) == len(perm) == 156
    differences = [dict(index=i, dom=a, perm=b) for i, (a, b) in enumerate(zip(dom, perm)) if a != b]
    operations_dom = [a for a, _ in dom]
    operations_perm = [a for a, _ in perm]
    swapped = operations_dom.copy()
    swapped[6], swapped[7] = swapped[7], swapped[6]
    assert swapped == operations_perm
    # The exact source tables are still separately checked by Lean's kernel.
    return dict(
        pin=PIN, checkout_head=head, pin_matches_head=(head == PIN),
        endpoint_closure=dict(project_modules=len(rows), bytes=sum(r["bytes"] for r in rows),
                              lines=sum(r["lines"] for r in rows), external_imports=sorted(external),
                              modules=rows),
        focused_sources=files,
        ax_words=dict(length=156, tuple_differences=differences,
                      operation_swap_indices=[6, 7],
                      operations_equal_after_swap=True,
                      semantic_equivalence="See the separately kernel-checked AXWord.lean theorem."),
        interpretation="Static source census; no endpoint compiler invocation is performed by this script.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit(args.repo.resolve())
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
