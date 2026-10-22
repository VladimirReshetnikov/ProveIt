#!/usr/bin/env python3
"""Replay a source-only path representation census for the K215 certificate.

No Lean proof, compiler invocation, or concrete replacement decoder is produced.
The estimated radix layout is precisely an ASCII list of (parent, tail-code)
pairs plus decimal IDs in the existing certificate entries. It excludes the
definition header, decoder, balanced lookup representation, and any proofs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

ap = argparse.ArgumentParser()
ap.add_argument("--repo", type=Path, required=True)
ap.add_argument("--output", type=Path)
args = ap.parse_args()
relative = Path("Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean")
source = args.repo / relative
raw = source.read_bytes()
text = raw.decode("utf-8")
chunks = text[text.index("def fwd0"):text.index("def fwdCert")]
entries = [tuple(map(int, match)) for match in re.findall(
    r"\.leaf \((\d+), (\d+), (\d+), (\d+)\)", chunks)]
if not entries:
    raise SystemExit("No certificate entries found")
codes = [n for entry in entries for n in entry[:2]]
if any(n < 1 or n.bit_length() - 1 > 512 for n in codes):
    raise SystemExit("The source pointers do not satisfy the measured 512-fuel representation")

# RMBisim.decodeAux removes the leading binary sentinel 1. Current codes all
# fit the 512-step bound, so this decodes exactly the stored finite paths.
paths = [bin(n)[3:] for n in codes]
unique = set(paths)
prefixes = {p[:i] for p in unique for i in range(len(p) + 1)}
suffixes = {p[i:] for p in unique for i in range(len(p) + 1)}
branches = {p for p in prefixes if p + "0" in prefixes and p + "1" in prefixes}

# Keep every terminal and every binary branch. Suppress all other unary trie
# vertices. Row zero is implicit and denotes the empty path.
vertices = sorted(unique | branches | {""}, key=lambda p: (len(p), p))
index = {p: i for i, p in enumerate(vertices)}
rows = []
reconstructed = [""]
for vertex in vertices[1:]:
    parent = vertex[:-1]
    while parent not in index:
        parent = parent[:-1]
    tail = vertex[len(parent):]
    parent_id = index[parent]
    tail_code = int("1" + tail, 2)
    if parent_id >= len(reconstructed):
        raise SystemExit("Parent ID is not earlier than its child")
    reconstructed.append(reconstructed[parent_id] + bin(tail_code)[3:])
    rows.append((parent_id, tail_code))

if reconstructed != vertices:
    raise SystemExit("Compressed-prefix reconstruction failed")
if [reconstructed[index[p]] for p in paths] != paths:
    raise SystemExit("Replacement IDs do not preserve the stored paths")

# Exact syntax used solely for the size estimate. This is not a full Lean
# module and does not include the implementation cost of lookup or decoding.
payload = "[" + ", ".join(f"({parent}, {tail})" for parent, tail in rows) + "]"
old_fields = sum(len(str(n)) for n in codes)
id_fields = sum(len(str(index[p])) for p in paths)
payload_bytes = len(payload.encode("ascii"))
plain_ids = {p: i for i, p in enumerate(sorted(unique, key=lambda p: (len(p), p)))}
pin = subprocess.check_output(
    ["git", "-C", str(args.repo), "rev-parse", "HEAD"], text=True).strip()
result = {
    "status": "Source census and estimated data-layout comparison only; no replacement decoder or kernel check",
    "repository_commit": pin,
    "source_path": str(relative),
    "source_sha256": hashlib.sha256(raw).hexdigest(),
    "source_bytes": len(raw),
    "certificate_entries": len(entries),
    "path_occurrences": len(paths),
    "unique_paths": len(unique),
    "maximum_path_bits": max(map(len, paths)),
    "total_occurrence_bits": sum(map(len, paths)),
    "unique_path_bits": sum(map(len, unique)),
    "unique_prefixes": len(prefixes),
    "unique_suffixes": len(suffixes),
    "certificate_chunk_bytes": len(chunks.encode("utf-8")),
    "current_decimal_path_field_bytes": old_fields,
    "whole_path_dictionary_id_field_bytes_only": sum(len(str(plain_ids[p])) for p in paths),
    "compressed_prefix_vertices_including_empty": len(vertices),
    "compressed_prefix_rows_excluding_empty": len(rows),
    "compressed_prefix_edge_bits": sum(t.bit_length() - 1 for _, t in rows),
    "estimated_ascii_pair_payload_bytes": payload_bytes,
    "compressed_prefix_id_field_bytes": id_fields,
    "estimated_pair_payload_plus_id_bytes": payload_bytes + id_fields,
    "estimated_bytes_saved_before_decoder_and_index_overhead": old_fields - payload_bytes - id_fields,
    "reconstruction_checks_passed": True,
    "measurement_definitions": {
        "certificate_chunk_bytes": "UTF-8 byte count from first 'def fwd0' up to, excluding, first 'def fwdCert'",
        "current_decimal_path_field_bytes": "sum(len(str(n))) for the first two integer fields of every parsed leaf entry",
        "vertices": "unique stored paths union all branching prefixes union empty path, sorted by (length, lexicographic bits)",
        "parent": "longest proper prefix that is also a vertex",
        "tail_code": "int('1' + bits_after_parent, 2)",
        "pair_payload": "'[' + ', '.join(f'({parent_id}, {tail_code})' for nonempty vertices) + ']'",
        "id_field_bytes": "sum(len(str(vertex_id))) for each of the 2 * entry_count path occurrences",
        "estimated_saving": "current_decimal_path_field_bytes - pair_payload_bytes - id_field_bytes"
    },
    "excluded_costs": [
        "Lean definition headers and types",
        "Balanced indexing tree or other non-list lookup representation",
        "Decoder implementation and any associated proofs",
        "Compile time, kernel reductions, memory use, and compiled object size"
    ],
    "interpretation": "Whole-path repetition is sparse; the estimated radix saving is modest and may be erased by decoder/index overhead. This is not a measured production source reduction or speedup."
}
rendered = json.dumps(result, indent=2) + "\n"
if args.output:
    args.output.write_text(rendered)
print(rendered, end="")
