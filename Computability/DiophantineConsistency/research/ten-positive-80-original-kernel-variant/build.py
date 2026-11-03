#!/usr/bin/env python3
"""Build a distinct 80-row graph specialization, not an equivalence proof."""
import gzip
import hashlib
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError("optimized Python is not supported")

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "research/ten-positive-unshift-t-finite/data/equation_qcube_V2.json"
PAYLOADS = ROOT / "candidates/free-j-polarized-positive/source/positive/coefficients/payloads"
INPUT_HASH = "fcc5e40f5d22320541ec2af5857725ceafaa69d0df36708ec60d6b9a40a71f01"
PINS = {
    "beta": ("beta.bin.gz", "466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c", "0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d"),
    "K0": ("K.bin.gz", "b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a", "c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e"),
    "MC": ("MC.bin.gz", "271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e", "6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4"),
    "MF": ("MF_source.bin.gz", "935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c6e3b", "48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737"),
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


source_bytes = SOURCE.read_bytes()
if digest(source_bytes) != INPUT_HASH:
    raise ValueError("80-row source changed")
source = json.loads(source_bytes)
rows = source["source"]
if len(rows) != 80 or source["operations"] != 80 or source["exact_degree"] != 750:
    raise ValueError("unexpected source metrics")
known = set(source["witnesses"]) | set(PINS)
counts = {"+": 0, "-": 0, "*": 0}
for row in rows:
    if not isinstance(row, list) or len(row) != 4:
        raise ValueError("malformed row")
    name, operation, left, right = row
    if not isinstance(name, str) or name in known or operation not in counts:
        raise ValueError("bad row name or operator")
    for operand in (left, right):
        if not (type(operand) is int or isinstance(operand, str) and operand in known):
            raise ValueError("undefined or malformed operand")
    known.add(name)
    counts[operation] += 1
if counts != source["operation_breakdown"] or source["output"] not in known:
    raise ValueError("graph census changed")

ports = {}
for name, (filename, compressed_hash, raw_hash) in PINS.items():
    compressed = (PAYLOADS / filename).read_bytes()
    raw = gzip.decompress(compressed)
    if digest(compressed) != compressed_hash or digest(raw) != raw_hash or not raw or raw[-1] == 0:
        raise ValueError("payload mismatch: " + name)
    (HERE / "coefficients" / filename).write_bytes(compressed)
    ports[name] = {"file": filename, "gzip_sha256": compressed_hash,
                   "raw_sha256": raw_hash, "bits": int.from_bytes(raw, "little").bit_length()}

candidate = {
    "name": "80-row-qcube-original-kernel-variant",
    "domain": source["domain"],
    "witnesses": source["witnesses"],
    "fixed_numerals": source["fixed_numerals"],
    "source": rows,
    "output": source["output"],
    "operations": len(rows),
    "operation_breakdown": counts,
    "inherited_exact_degree": source["exact_degree"],
    "parent_source_sha256": INPUT_HASH,
    "coefficient_binding": {"path": "coefficients/", "encoding": "minimal unsigned little-endian", "ports": ports},
    "proof_status": "Candidate only: the original-kernel specialization, its file/Lean binding, machine equivalence and iPRA endpoint are not proved by this artifact.",
}
output = (json.dumps(candidate, indent=2, sort_keys=True) + "\n").encode()
(HERE / "equation.json").write_bytes(output)
if SOURCE.read_bytes() != source_bytes:
    raise ValueError("source changed during build")
for name, (filename, compressed_hash, _) in PINS.items():
    if digest((PAYLOADS / filename).read_bytes()) != compressed_hash:
        raise ValueError("payload changed during build: " + name)
print(json.dumps({"status": "CANDIDATE_BUILT", "equation_sha256": digest(output),
                  "rows": len(rows), "counts": counts,
                  "scope": "external byte and graph construction only"}, sort_keys=True))
