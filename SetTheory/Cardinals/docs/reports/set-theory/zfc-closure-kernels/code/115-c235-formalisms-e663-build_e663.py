#!/usr/bin/env python3
"""E663 changes only E667's ground query to Q(d)=d; E667 stays unchanged."""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import build_e667 as e


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--out", type=Path, default=Path(__file__).resolve().parent / "generated")
    a = p.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    old = e.presentation()
    oldbits, oldmetrics = e.encode(old)
    assert oldmetrics["packet_bits"] == 667
    assert oldmetrics["bit_character_sha256"] == "1075854399e1c3428e1c178b51bac47e428b8ef010b59e0312a3c06d409e55b8"
    new = {**old, "start": e.t("Q", e.D)}
    metrics = e.write_packet(a.out, "E663", new)
    assert metrics["packet_bits"] == 663
    assert metrics["equation_nodes"] == 150 and metrics["endpoint_bits"] == 12
    newbits, _ = e.encode(new)
    assert oldbits[:-16] == newbits[:-12]
    constants = [name for name, arity in new["signature"] if arity == 0]
    assert constants == ["d"]
    assert e.size(new["start"]) + e.size(new["target"]) == 3
    receipt = {"status": "COMPLETE_CALIBRATED_QUERY_PACKET", "E663": metrics,
               "E667_header_and_equations_literal_unchanged": True,
               "old_ground_query": "N(d,d)=d", "new_ground_query": "Q(d)=d",
               "query_term_nodes_old": 4, "query_term_nodes_new": 3,
               "exact_saving_bits": 4,
               "endpoint_optimality_scope": "12 bits is minimal for syntactically distinct ground endpoints in this unchanged signature/codec",
               "unique_constant": constants[0],
               "relative_theorem": "Both queries collapse every E667 model to a singleton; equal equational derivability status",
               "proof_scope": "Ordinary equational-model argument formalizable in ZFC, inherited EPSC calibration, no TM compilation"}
    (a.out / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
