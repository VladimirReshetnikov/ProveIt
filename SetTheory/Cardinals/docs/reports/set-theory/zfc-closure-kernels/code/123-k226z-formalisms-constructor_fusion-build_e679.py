#!/usr/bin/env python3
"""Fuse native constructors and closure witnesses in the complete E688 packet.

The mathematical upper-model proof is in constructor_fusion.tex.  This program
checks the literal finite packet transformation, including a structural inverse
that is valid in the fixed equation contexts.  It does not test consistency or
compile a Turing machine.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

from codec_inherited import (decode, encode, expected_decoding, pretty,
                            size, validate)


FUSION = {"Target": "Q", "Next": "P", "Mem": "A"}
PIN_BITS = "9518c474861557da085c76ef77dd4141eecfa0befaec66d90acc81ac39264d97"


def require(value, message):
    if not value:
        raise ValueError(message)


def replace_symbols(term):
    if isinstance(term, str):
        return term
    return [FUSION.get(term[0], term[0]),
            *(replace_symbols(c) for c in term[1:])]


def symbols(term):
    if isinstance(term, str):
        return Counter()
    result = Counter({term[0]: 1})
    for child in term[1:]:
        result.update(symbols(child))
    return result


def same_tree(before, after, path=()):
    """Check every corresponding node and return all renamed operation sites."""
    if isinstance(before, str):
        require(before == after, f"variable changed at {path}")
        return []
    require(isinstance(after, list) and len(before) == len(after),
            f"tree shape changed at {path}")
    require(after[0] == FUSION.get(before[0], before[0]),
            f"unexpected operation change at {path}")
    changed = []
    if before[0] != after[0]:
        changed.append({"path": list(path), "old": before[0], "new": after[0]})
    for i, (a, b) in enumerate(zip(before[1:], after[1:])):
        changed += same_tree(a, b, path + (i,))
    return changed


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=here / "E688_reference.json")
    parser.add_argument("--bits", type=Path, default=here / "E688_reference.bits")
    parser.add_argument("--out", type=Path, default=here / "generated")
    args = parser.parse_args()

    original = json.loads(args.input.read_text())
    original_bits, original_metrics = encode(original)
    require(sha256(original_bits.encode()).hexdigest() == PIN_BITS,
            "E688 source bits differ from pinned baseline")
    require(args.bits.read_text() == original_bits + "\n", "E688 bit file differs")
    require(original_metrics["complete_packet_bits"] == 688, "incorrect baseline")
    require(all(original["signature"][a] == original["signature"][b]
                for a, b in FUSION.items()), "fusion changes arity")

    reduced = deepcopy(original)
    reduced.pop("metrics", None)
    reduced["name"] = "E679"
    reduced["signature"] = {k: v for k, v in original["signature"].items()
                            if k not in FUSION}
    reduced["equations"] = [[replace_symbols(a), replace_symbols(b)]
                            for a, b in original["equations"]]
    reduced["start"] = replace_symbols(original["start"])
    reduced["target"] = replace_symbols(original["target"])
    reduced["status"] = (
        "Complete equational packet; ordinary ZFC calibration inherited from E688 "
        "through an explicit constructor/Skolem fusion upper model; no TM count "
        "or proof-assistant endpoint is claimed.")
    reduced["fusion"] = FUSION
    validate(reduced)

    changed = []
    for row, (old, new) in enumerate(zip(original["equations"], reduced["equations"])):
        for side in (0, 1):
            for item in same_tree(old[side], new[side]):
                changed.append({"equation": row, "side": side, **item})
    require(original["equations"][:6] == reduced["equations"][:6],
            "a native or Boolean equation changed")
    require(original["start"] == reduced["start"] and
            original["target"] == reduced["target"], "endpoints changed")
    counts = Counter(item["old"] for item in changed)
    require(counts == {"Target": 4, "Next": 3, "Mem": 2},
            "unexpected closure witness multiplicities")
    bits, metrics = encode(reduced)
    require(metrics["complete_packet_bits"] == 679, "incorrect packet count")
    require(metrics["both_side_tree_nodes"] == 153, "equation tree count changed")
    require(metrics["equation_node_counts"] == [14, 6, 10, 12, 12, 17, 82],
            "equation shape counts changed")
    require(metrics["signature_symbols"] == 9 and metrics["opcode_width"] == 4,
            "unexpected signature or opcode width")
    require(decode(bits) == expected_decoding(reduced, 4), "round trip failed")

    rejected = 0
    for end in range(len(bits)):
        try:
            decode(bits[:end])
        except ValueError:
            rejected += 1
        else:
            raise ValueError(f"accepted strict truncation at {end}")
    malformed_controls = [bits + "0", bits + "1", bits[:-1] + "x"]
    for bad in malformed_controls:
        try:
            decode(bad)
        except ValueError:
            pass
        else:
            raise ValueError("accepted malformed control")

    reduced["metrics"] = metrics
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "E679.json").write_text(json.dumps(reduced, indent=2) + "\n")
    (args.out / "E679.bits").write_text(bits + "\n")
    (args.out / "E679.equations").write_text(
        "\n".join(pretty(a) + " = " + pretty(b) for a, b in reduced["equations"])
        + "\n\nQuery: " + pretty(reduced["start"]) + " = "
        + pretty(reduced["target"]) + "\n")
    receipt = {
        "baseline_bits_sha256": PIN_BITS,
        "baseline_metrics": original_metrics,
        "fusion": FUSION,
        "changed_operation_sites": changed,
        "changed_operation_counts": dict(counts),
        "first_six_equations_unchanged": True,
        "endpoints_unchanged": True,
        "all_tree_shapes_and_variables_unchanged": True,
        "round_trip": True,
        "strict_truncations_rejected": rejected,
        "malformed_controls_rejected": len(malformed_controls),
        "metrics": metrics,
        "saving_bits": original_metrics["complete_packet_bits"]
                       - metrics["complete_packet_bits"],
        "saving_source": "three removed 3-bit signature arities; term width unchanged",
        "mathematical_proof": "constructor_fusion.tex",
        "proof_status": "ordinary mathematical proof; codec checks only are executable",
        "turing_machine_state_bound": None,
    }
    (args.out / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"packet_bits": len(bits), "sha256": metrics["bits_sha256"],
                      "fusion_counts": dict(counts),
                      "strict_truncations_rejected": rejected}, indent=2))


if __name__ == "__main__":
    main()
