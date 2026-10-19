#!/usr/bin/env python3
"""Conservative fresh-constant reduction of the inherited E663 packet to E662.

The input is an exact AST snapshot from ZFC235_Construction_2026-10-19.zip.
This script reimplements its unchanged prefix codec, verifies the inherited
bit digest, appends a new constant e unused by the axioms, and changes the
ground query to e=d. It provides no new Turing-machine state bound.
See ATTRIBUTION.baseline.txt and proof.tex for scope and attribution.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path

BASELINE_SHA256 = "6c3b72c39c81aa5bbf028e654c8056e7e86376cdeecdd56943e5c3e23de1a215"


def variables(term):
    if isinstance(term, str):
        return {term}
    return set().union(*(variables(t) for t in term[1:]))


def nodes(term):
    return 1 if isinstance(term, str) else 1 + sum(nodes(t) for t in term[1:])


def canonical(equation):
    names = sorted(variables(equation[0]) | variables(equation[1]))
    mapping = {s: f"v{i}" for i, s in enumerate(names)}
    def walk(t):
        return mapping[t] if isinstance(t, str) else [t[0], *(walk(x) for x in t[1:])]
    return [walk(equation[0]), walk(equation[1])]


def encode(packet):
    signature = packet["signature"]
    arity = dict(signature)
    equations = [canonical(eq) for eq in packet["equations"]]
    capacity = max(len(variables(a) | variables(b)) for a, b in equations)
    width = max(1, (len(signature) + capacity - 1).bit_length())
    opcodes = {symbol: i + capacity for i, (symbol, _) in enumerate(signature)}

    def encode_term(term):
        if isinstance(term, str):
            index = int(term[1:])
            if not 0 <= index < capacity:
                raise ValueError("variable outside header capacity")
            return f"{index:0{width}b}"
        if len(term) != 1 + arity[term[0]]:
            raise ValueError("arity mismatch")
        return f"{opcodes[term[0]]:0{width}b}" + "".join(map(encode_term, term[1:]))

    header = f"{len(signature):08b}" + "".join(f"{a:03b}" for _, a in signature) + f"{capacity:08b}"
    body = "".join("1" + encode_term(a) + encode_term(b) for a, b in equations) + "0"
    endpoints = encode_term(packet["start"]) + encode_term(packet["target"])
    bits = header + body + endpoints
    counts = [nodes(a) + nodes(b) for a, b in equations]
    return bits, {
        "operation_symbols": len(signature), "equations": len(equations),
        "variable_capacity": capacity, "opcode_bits": width,
        "equation_node_counts": counts, "equation_nodes": sum(counts),
        "header_bits": len(header), "equation_bits": len(body),
        "endpoint_bits": len(endpoints), "packet_bits": len(bits),
        "bit_character_sha256": hashlib.sha256(bits.encode("ascii")).hexdigest(),
    }


def decode(bits):
    """Independent positional parser using only encoded arities and opcodes."""
    position = 0
    def read(count):
        nonlocal position
        block = bits[position:position+count]
        if len(block) != count or any(c not in "01" for c in block):
            raise ValueError("truncated or invalid bit field")
        position += count
        return int(block, 2)

    operation_count = read(8)
    arities = [read(3) for _ in range(operation_count)]
    capacity = read(8)
    width = max(1, (operation_count + capacity - 1).bit_length())

    def term():
        opcode = read(width)
        if opcode < capacity:
            return opcode
        index = opcode - capacity
        if not 0 <= index < operation_count:
            raise ValueError("unused operation code")
        return [index, *(term() for _ in range(arities[index]))]

    equations = []
    while read(1):
        equations.append([term(), term()])
    start, target = term(), term()
    def ground(t):
        return isinstance(t, list) and all(ground(x) for x in t[1:])
    if position != len(bits) or not ground(start) or not ground(target):
        raise ValueError("trailing bits or nonground query")
    return {"arities": arities, "capacity": capacity, "equations": equations,
            "start": start, "target": target}


def expected_numeric(packet):
    symbols = [s for s, _ in packet["signature"]]
    def numeric(t):
        return int(t[1:]) if isinstance(t, str) else [symbols.index(t[0]), *(numeric(x) for x in t[1:])]
    return {"arities": [a for _, a in packet["signature"]], "capacity": 4,
            "equations": [[numeric(a), numeric(b)] for a, b in map(canonical, packet["equations"])],
            "start": numeric(packet["start"]), "target": numeric(packet["target"])}


def pretty(t):
    if isinstance(t, str):
        return t
    return t[0] + ("(" + ",".join(map(pretty, t[1:])) + ")" if len(t) > 1 else "")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=Path, default=Path(__file__).with_name("baseline_E663.json"))
    parser.add_argument("--out", type=Path, default=Path(__file__).with_name("generated"))
    args = parser.parse_args()
    source = json.loads(args.baseline.read_text())
    old_bits, old_metrics = encode(source)
    assert old_metrics["packet_bits"] == 663
    assert old_metrics["bit_character_sha256"] == BASELINE_SHA256
    assert decode(old_bits) == expected_numeric(source)

    packet = {key: copy.deepcopy(source[key]) for key in ("signature", "equations", "start", "target")}
    assert all(symbol != "e" for symbol, _ in packet["signature"])
    packet["signature"].append(["e", 0])
    packet["start"], packet["target"] = ["e"], ["d"]
    assert packet["equations"] == source["equations"]
    new_bits, new_metrics = encode(packet)
    assert new_metrics["packet_bits"] == 662
    assert new_metrics["equation_node_counts"] == [14, 6, 9, 12, 12, 17, 80]
    assert decode(new_bits) == expected_numeric(packet)
    # Appending e leaves every existing operation index unchanged, as well
    # as all seven equation bit strings (the header has moved by three bits).
    old_body = old_bits[old_metrics["header_bits"]:-old_metrics["endpoint_bits"]]
    new_body = new_bits[new_metrics["header_bits"]:-new_metrics["endpoint_bits"]]
    assert old_body == new_body
    malformed = [new_bits[:n] for n in range(len(new_bits))]
    malformed += [new_bits + "0", new_bits[:-1] + "x", new_bits[:-4] + "0000"]
    for bad in malformed:
        try:
            decode(bad)
        except (ValueError, RecursionError):
            continue
        raise AssertionError("malformed packet accepted")

    args.out.mkdir(parents=True, exist_ok=True)
    padding = (-len(new_bits)) % 8
    binary = int(new_bits + "0" * padding, 2).to_bytes((len(new_bits) + padding)//8, "big")
    assert "".join(f"{b:08b}" for b in binary)[:len(new_bits)] == new_bits
    data = {"name": "E662", **packet, "metrics": new_metrics,
            "transport_padding_bits": padding,
            "status": "complete equational packet; conservative signature extension; no machine-state claim"}
    receipt = {
        "E663": old_metrics, "E662": new_metrics,
        "old_bit_digest_verified": True, "equation_ASTs_unchanged": True,
        "equation_bits_unchanged": True, "fresh_constant_unused_by_axioms": True,
        "independent_roundtrip": True, "strict_truncations_rejected": len(new_bits),
        "other_malformed_controls_rejected": 3,
        "exact_saving_bits": old_metrics["packet_bits"] - new_metrics["packet_bits"],
        "query_equivalence": "E proves Q(d)=d iff E in the signature expanded by fresh e proves e=d",
        "scope": "ordinary equational proof transformation plus inherited raw-EPSC/ZFC calibration",
    }
    (args.out / "E662.bits").write_text(new_bits + "\n")
    (args.out / "E662.bitlength").write_text(str(len(new_bits)) + "\n")
    (args.out / "E662.bin").write_bytes(binary)
    (args.out / "E662.json").write_text(json.dumps(data, indent=2) + "\n")
    equations_text = "\n".join(f"{i}: {pretty(a)} = {pretty(b)}" for i, (a,b) in enumerate(packet["equations"], 1))
    (args.out / "E662.equations").write_text(equations_text + "\nQUERY: e = d\n")
    (args.out / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
