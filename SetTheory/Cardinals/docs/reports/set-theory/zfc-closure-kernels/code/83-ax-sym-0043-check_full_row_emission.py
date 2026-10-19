#!/usr/bin/env python3
"""Check every complete row order with the existing recovered AX emitter.

Usage: python3 -B check_full_row_emission.py
Optional: --repo /path/to/ProveIt uses byte-identical pinned repository sources.
This validates formula-emission syntax and read placement, not binary execution.
"""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import time

from vendor_loader import load_theory


def leaves(form):
    if not isinstance(form, tuple):
        return [form]
    return leaves(form[1]) + leaves(form[2])


def rename(form, role_map):
    if not isinstance(form, tuple):
        return role_map.get(form, form)
    return form[0], rename(form[1], role_map), rename(form[2], role_map)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--preflight-only", action="store_true",
                        help="Check identity, the original order, and all twelve rho8 maps")
    args = parser.parse_args()
    theory, provenance = load_theory(args.repo)
    spec, digest = theory.published_spec()
    rows = spec["ax_rows"]("a", "h", "b", "c", "u")
    bundle = spec["bundle"]("a", "b", "c")
    fragments = [theory.emit(row) for row in rows[1:]]
    if sum(p.count(158) for p in fragments) != 1:
        raise AssertionError("The entire logical family must read u once")
    if sum(p.count(176) for p in fragments) != 0:
        raise AssertionError("A static row unexpectedly reads a new b")
    started = time.monotonic()
    checked = 0
    orders = [tuple(range(8))] if args.preflight_only else itertools.permutations(range(8))
    for order in orders:
        word = ([166, 121, 180, 176]
                + [x for k in order for x in fragments[k]]
                + theory.emit(bundle) + theory.TAIL)
        actual, _ = theory.symbolic(word)
        expected = ["old_top", rows[0], *[rows[k+1] for k in order], bundle]
        if actual != expected:
            raise AssertionError(("Formula output changed", order))
        if word.count(158) != 1 or word.count(176) != 1:
            raise AssertionError(("Read count changed", order))
        if word[:4] != [166, 121, 180, 176] or word[-5:] != theory.TAIL:
            raise AssertionError(("Prefix/tail changed", order))
        checked += 1
    rho8 = rows[1]
    counts = Counter(leaves(rho8))
    if counts != Counter(a=2, b=1, c=3, u=1):
        raise AssertionError("The rho8 role-occurrence counts changed")
    role_records = []
    for values in itertools.permutations(("a", "b", "c", "u")):
        role_map = dict(zip(("a", "b", "c", "u"), values))
        form = rename(rho8, role_map)
        if Counter(leaves(form))["u"] != 1:
            continue
        calls = theory.emit(form)
        actual, _ = theory.symbolic([166, 121, 180, 176] + calls)
        if actual != ["old_top", rows[0], form]:
            raise AssertionError(("Rho8 role-map output changed", role_map))
        if calls.count(158) != 1 or calls.count(208) != 1 or 176 in calls:
            raise AssertionError(("Rho8 role-map read effects changed", role_map))
        inverse = {value: key for key, value in role_map.items()}
        if rename(form, inverse) != rho8:
            raise AssertionError(("Rho8 role map is not invertible", role_map))
        role_records.append(dict(role_map=role_map, macro_calls=len(calls),
                                 read_u_count=calls.count(158)))
    if len(role_records) != 12:
        raise AssertionError("Expected precisely twelve single-read rho8 maps")
    result = dict(
        all_checks_passed=True,
        complete_logical_row_orders=checked,
        one_old_cache_GEN_then_read_b=True,
        one_consumed_u_per_AXIOM=True,
        original_both_gates_and_cleanup_fixed_last=True,
        source_spec_sha256=digest,
        rho8_occurrence_counts=dict(counts),
        permitted_rho8_maps=len(role_records),
        nominal_full_configurations=40320 * 12 * 6**7,
        rho8_role_maps=role_records,
        execution_mode="portable_preflight" if args.preflight_only else "exhaustive",
        source_loading=provenance,
        seconds=round(time.monotonic()-started, 3),
        scope="Repository emitter and symbolic row evaluator; no numeric helper or TM proof",
    )
    filename = "portable_preflight.json" if args.preflight_only else "full_row_emission_checks.json"
    output = args.output or Path(__file__).with_name(filename)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
