"""Independent checker for weighted representative-family certificates.

Uses incidence minors rather than the producer's rooted-transversal formula.
Imports neither disc_basis nor its helpers. This authenticates reduction of a
supplied table, not whether the table describes embedded surfaces of a knot.
"""
from __future__ import annotations
from hashlib import sha256
from itertools import combinations
from math import comb
import json


def _valid_partition(p, r):
    if not isinstance(p, list) or len(p) != r:
        return False
    hi = -1
    for x in p:
        if type(x) is not int or x < 0 or x > hi+1:
            return False
        hi = max(hi, x)
    return True


def _minor_row(p):
    groups = {}
    for v, label in enumerate(p):
        groups.setdefault(label, []).append(v)
    columns = [(group[0], v) for group in groups.values() for v in group[1:]]
    d = len(columns)
    result = 0
    for chosen in combinations(range(1, len(p)), d):
        a = [[int(v == x or v == y) for x, y in columns] for v in chosen]
        rank = 0
        for col in range(d):
            pivot = next((i for i in range(rank, d) if a[i][col]), None)
            if pivot is None:
                continue
            a[rank], a[pivot] = a[pivot], a[rank]
            for i in range(rank+1, d):
                if a[i][col]:
                    a[i] = [x ^ y for x, y in zip(a[i], a[rank])]
            rank += 1
        if rank == d:
            result |= 1 << sum(1 << (v-1) for v in chosen)
    return result


def verify(records, cert, *, max_ports=12, max_rows=100000):
    """Return bool; malformed input, mismatched source, or cap overflow rejects."""
    try:
        if not isinstance(cert, dict) or set(cert) != {"version", "r", "source_sha256", "kept", "dropped"}:
            return False
        if type(cert["version"]) is not int or cert["version"] != 1:
            return False
        r = cert["r"]
        if type(r) is not int or not 1 <= r <= max_ports or not isinstance(records, list) or len(records) > max_rows:
            return False
        by_id, costs, groups = {}, {}, {}
        for c in records:
            if not isinstance(c, dict) or set(c) != {"id", "partition", "cost_hex", "control"}:
                return False
            ident = c["id"]
            if not isinstance(ident, str) or not ident or ident in by_id or not isinstance(c["control"], str) or not _valid_partition(c["partition"], r):
                return False
            if not isinstance(c["cost_hex"], str):
                return False
            cost = int(c["cost_hex"], 16)
            if hex(cost) != c["cost_hex"]:
                return False
            by_id[ident] = c
            costs[ident] = cost
            groups[ident] = (c["control"], r-max(c["partition"])-1)
        obj = {"r": r, "candidates": sorted(records, key=lambda x: x["id"])}
        digest = sha256(json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()).hexdigest()
        if cert["source_sha256"] != digest:
            return False
        kept, dropped = cert["kept"], cert["dropped"]
        if not isinstance(kept, list) or any(not isinstance(x, str) or x not in by_id for x in kept) or len(set(kept)) != len(kept) or not isinstance(dropped, list):
            return False
        counts = {}
        for ident in kept:
            key = groups[ident]
            counts[key] = counts.get(key, 0)+1
            if counts[key] > comb(r-1, key[1]):
                return False
        row_cache = {}
        def row(ident):
            if ident not in row_cache:
                row_cache[ident] = _minor_row(by_id[ident]["partition"])
            return row_cache[ident]
        covered = set(kept)
        for proof in dropped:
            if not isinstance(proof, dict) or set(proof) != {"id", "xor_hex"}:
                return False
            ident = proof["id"]
            if not isinstance(ident, str) or ident not in by_id or ident in covered or not isinstance(proof["xor_hex"], str):
                return False
            mask = int(proof["xor_hex"], 16)
            if mask <= 0 or mask.bit_length() > len(kept) or hex(mask) != proof["xor_hex"]:
                return False
            total = 0
            while mask:
                bit = mask & -mask
                k = kept[bit.bit_length()-1]
                if groups[k] != groups[ident] or costs[k] > costs[ident]:
                    return False
                total ^= row(k)
                mask ^= bit
            if total != row(ident):
                return False
            covered.add(ident)
        return covered == set(by_id)
    except (ValueError, TypeError, KeyError, IndexError, OverflowError):
        return False


if __name__ == "__main__":
    import argparse
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    source = json.loads(args.input.read_text())
    certificate = json.loads(args.certificate.read_text())
    ok = type(source.get("r")) is int and source["r"] == certificate.get("r") and verify(source["candidates"], certificate)
    print("VALID representative reduction" if ok else "REJECTED")
    raise SystemExit(0 if ok else 1)
