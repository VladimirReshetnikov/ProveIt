#!/usr/bin/env python3
"""Certify the global South-label obstruction to marker1004 offset19."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "research/low-padding-independent/certify.py"
PARENT_SHA = "86dae914161f5f030cd1c575e6448e029542a18718cadf732c2d5a673adc3cc7"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    require(sha(PARENT.read_bytes()) == PARENT_SHA, "Exact frozen complete source verifier")
    module_spec = importlib.util.spec_from_file_location("frozen_marker_source", PARENT)
    require(module_spec is not None and module_spec.loader is not None, "Parent import specification")
    parent = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(parent)
    _, seed, actions, tiles, coefficients, support = parent.model()
    require(len(tiles) == 942 and list(tiles[941]) == [4, 437, 2, 437]
            and 511 - tiles[941][3] == 74 and 511 - tiles[0][3] == 510,
            "Complete calibrated exceptional tile and forced Start South label")
    # At field offset19, all nine North-copy preimages lie in the same B-cell.
    targets = list(range(960, 969))
    preimages = [e - 19 for e in targets]
    require(preimages == [941] + list(range(942, 950)),
            "Exact selector941 followed by the first eight South bits")
    bit_cases = []
    for south in range(512):
        for epsilon in ((0, 1) if south == 74 else (0,)):
            copied_bits = [epsilon] + [(south >> j) & 1 for j in range(8)]
            current = sum(bit << j for j, bit in enumerate(copied_bits))
            require(current == (2 * south + epsilon) % 512,
                    "Whole9-bit shifted-copy identity")
            bit_cases.append((south, epsilon, current))
    require(len(bit_cases) == 513, "All possible calibrated9-bit transition cases")

    # This graph deliberately includes every9-bit label, not just used colors.
    graph = {south: {2 * south % 512} for south in range(512)}
    graph[74].add(149)
    ranks, active = {0: 0}, set()

    def rank(south):
        if south in ranks:
            return ranks[south]
        require(south not in active, "No directed cycle outside zero")
        active.add(south)
        value = 1 + max(rank(target) for target in graph[south])
        active.remove(south)
        ranks[south] = value
        return value

    for south in range(512):
        rank(south)
    require(graph[0] == {0} and len(ranks) == 512 and max(ranks.values()) == 11,
            "Full512-state bounded ranking with only zero-cycle")
    require(all(ranks[target] < ranks[south] for south in range(1, 512) for target in graph[south]),
            "Every nonzero transition strictly decreases the recorded ranking")
    transitions = [{"tile_index": None, "south": 0, "epsilon": 0, "current_south": 0}]
    for j, tile in enumerate(tiles):
        south, epsilon = 511 - tile[3], int(j == 941)
        current = (2 * south + epsilon) % 512
        require(current in graph[south] and (epsilon == 0 or south == 74),
                "Every one of942 decoded tile transitions belongs to the certified graph")
        transitions.append({"tile_index": j, "south": south, "epsilon": epsilon,
                            "current_south": current})
    require(len(transitions) == 943, "Entire admissible language plus the empty state")
    special_path = [74, 149]
    while special_path[-1] != 0:
        special_path.append(2 * special_path[-1] % 512)
    require(special_path == [74, 149, 298, 84, 168, 336, 160, 320, 128, 256, 0],
            "Entire exceptional branch terminates without returning to74")
    require(511 - tiles[3][3] == 511 and (2 * 511) % 512 == 510,
            "Previously compatible local marker1004 pattern remains present")
    require((2 * 511 + 1) % 512 == 511 and 511 != 74,
            "Dropping the exact exceptional-tile calibration would permit a nonzero cycle")
    rows = [{"south": south, "successors": sorted(graph[south]), "rank": ranks[south]}
            for south in range(512)]
    data = {
        "schema": "marker1004_offset19_global_graph_v1",
        "script_sha256": sha(Path(__file__).read_bytes()), "parent_verifier_sha256": PARENT_SHA,
        "parent_proof_sha256": parent.PROOF_SHA,
        "seed_sha256": sha(seed.encode()), "actions_sha256": sha(encoded(actions)),
        "tiles_sha256": sha(encoded(tiles)), "full_coefficients_sha256": sha(encoded(coefficients)),
        "copy_targets": targets, "offset19_preimages": preimages,
        "transition_formula": "S_current=(2*S_temporal+I(tile_temporal=941)) mod512",
        "all513_bit_cases_sha256": sha(encoded(bit_cases)),
        "all943_native_state_transitions": transitions,
        "graph": rows, "largest_rank": 11,
        "largest_rank_vertices": sorted(south for south, value in ranks.items() if value == 11),
        "exceptional_path": special_path, "only_directed_cycle": [0], "forced_Start_south": 510,
        "local_negative_control": {"temporal_tile": 3, "temporal_south": 511, "current_south": 510,
                                   "scope": "A valid local edge; it cannot lie on any nonzero finite temporal cycle."},
        "calibration_deletion_negative": {"false_exception_south": 511, "false_self_loop": 511},
        "consequence": "On any finite temporal cell permutation every South label lies on a closed graph walk. The ranking forces every label to0, contradicting the forced Start label510.",
        "scope": "Complete finite global phase sublemma from all942 tiles. This is not a complete new marker1004 tuple certificate, scalar/controller proof or page promotion."
    }
    raw = encoded(data)
    path = HERE / "CERTIFICATE.json"
    if args.write:
        path.write_bytes(raw)
    else:
        require(path.read_bytes() == raw, "Deterministic complete graph certificate")
    print(json.dumps({"status": "PASS", "states": len(graph), "native_state_transitions": len(transitions),
                      "largest_rank": max(ranks.values()), "script_sha256": data["script_sha256"],
                      "certificate_sha256": sha(raw)}, sort_keys=True))


if __name__ == "__main__":
    main()
