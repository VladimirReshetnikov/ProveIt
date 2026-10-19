#!/usr/bin/env python3
"""Check deletion of identity-effect source sites on the product invariant.

Kept leaves are paired in their original order with target leaves.  Deleted
nonempty-invariant leaves must be unconditional controls or known-zero
decrements.  Their normalization must terminate.  Every feasible retained
edge is then checked through normalization against the target edge.
This is a source-language theorem only, not a binary runtime certificate.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from audit_guard_transport import parse_source, cases, check_product, image, represented, require, file_hash
from leaf_cfg import Program

DEFAULT_DELETED = (6316, 6317, 6318, 6434, 6435, 6436)


def check_collapse(source, target, certificate, deleted):
    source_cases = cases(source)
    product = check_product(certificate, source_cases)
    old_addresses = [pc for pc, op, arg in source.sites]
    new_addresses = [pc for pc, op, arg in target.sites]
    require(new_addresses == sorted(new_addresses), "Target leaves must be in lexicographic order")
    old_index = {pc: i for i, pc in enumerate(old_addresses)}
    new_index = {pc: i for i, pc in enumerate(new_addresses)}
    deleted = set(deleted)
    require(deleted <= set(range(len(old_addresses))), "Invalid deleted leaf index")
    kept = [i for i in range(len(old_addresses)) if i not in deleted]
    require(len(kept) == len(new_addresses), "Target leaf count does not match deletion")
    mapping = {old: new for new, old in enumerate(kept)}
    masks = certificate["masks"]
    normalized, normalization_paths = {}, {}

    def normalize(start):
        i, path = start, []
        while i in deleted:
            require(i not in path, "Cycle inside deleted feasible sites")
            require(masks[i] is not None, "Normalization enters empty invariant")
            path.append(i)
            pc, op, arg = source.sites[i]
            successors = source.successors(pc)
            if op in {"CB", "CC"}:
                nextpc = successors["always"]
            elif op == "CD" and masks[i][arg] == 1:
                nextpc = successors["zero"]
            else:
                raise ValueError(f"Deleted leaf {i} has a feasible nonidentity effect or halt")
            i = old_index[nextpc]
        normalized[start], normalization_paths[start] = i, path
        return i

    # Check even nonempty deleted masks outside the actual reachable set.
    for i in deleted:
        if masks[i] is not None:
            normalize(i)
    initial = normalize(old_index[source.initial])
    require(mapping[initial] == new_index[target.initial], "Initial normalized leaf differs")
    for old, new in mapping.items():
        require(source.signature(old_addresses[old]) == target.signature(new_addresses[new]),
                f"Kept effect or halt tag changed at old leaf {old}")
    feasible = 0
    for old, pc, op, arg, zero, following in source_cases:
        if old in deleted or masks[old] is None:
            continue
        if op in {"CI", "CD"} and not image(represented(masks[old][arg]), op, zero):
            continue
        feasible += 1
        if following is None:
            continue
        final = normalize(following)
        guard = "zero" if zero is True else "positive" if zero is False else "always"
        target_pc = new_addresses[mapping[old]]
        actual = new_index[target.successors(target_pc)[guard]]
        require(actual == mapping[final], f"Normalized successor differs at old leaf {old}, guard {guard}")
    return {
        "status": "PASS", "scope": "Source halting equivalence on T=W=H=0 and arbitrary six numerical registers",
        "source_leaves": len(old_addresses), "target_leaves": len(new_addresses),
        "deleted_old_leaf_indices": sorted(deleted),
        "checked_feasible_retained_cases": feasible,
        "maximum_identity_steps_after_one_retained_step": max(map(len, normalization_paths.values()), default=0),
        "initial_old_leaf": old_index[source.initial], "initial_normalized_old_leaf": initial,
        "initial_target_leaf": new_index[target.initial],
        "nonempty_deleted_paths": {str(i): normalization_paths[i] for i in sorted(deleted) if masks[i] is not None},
        "source_product": product,
        "proof_obligations_remaining": "Changed binary instruction segments, macro support, and complete blank initializer",
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("candidate", type=Path, help="JSON object with sites, or a direct site list")
    ap.add_argument("--package", type=Path, default=Path(__file__).resolve().parents[2])
    ap.add_argument("--deleted", type=int, nargs="+", default=DEFAULT_DELETED)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    source_path = args.package / "reference/context246/sources/Prog254.v"
    certificate_path = args.package / "reference/guard-invariant/product-invariant.json"
    source = parse_source(source_path)
    data = json.loads(args.candidate.read_text())
    target = Program(data["sites"] if isinstance(data, dict) else data)
    certificate = json.loads(certificate_path.read_text())
    result = check_collapse(source, target, certificate, args.deleted)
    result.update(source_sha256=file_hash(source_path), target_sha256=file_hash(args.candidate),
                  certificate_sha256=file_hash(certificate_path))
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
