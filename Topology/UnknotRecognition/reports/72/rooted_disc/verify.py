"""Independent small reference certificate replay.

Reconstructs rows by the mathematical saturation/transversal definition,
not by importing the producer's feature, reducer, or pairing functions.
"""
from __future__ import annotations
from itertools import product
from functools import lru_cache
import hashlib
import json
from .kernel import State, Candidate, ResourceLimit


@lru_cache(maxsize=4096)
def reference_feature(s: State, max_dimension: int = 2_000_000) -> int:
    dimension = s.q * 3 ** (s.r - 1)
    if dimension > max_dimension:
        raise ResourceLimit("reference feature is above the dimension limit")
    out = 0
    for digits in product(range(3), repeat=s.r - 1):
        membership = [True] + [x != 0 for x in digits]
        transversal = [True] + [x == 2 for x in digits]
        charge, valid = 0, True
        for block in range(len(s.good)):
            points = [i for i, b in enumerate(s.partition) if b == block]
            included = sum(membership[i] for i in points)
            if included == 0:
                continue
            if included != len(points) or not s.good[block] or sum(transversal[i] for i in points) != 1:
                valid = False
                break
            charge ^= s.charges[block]
        if valid:
            code = sum(x * 3 ** i for i, x in enumerate(digits))
            out ^= 1 << (code * s.q + charge)
    return out


def verify_reduction(candidates: list[Candidate], cert: dict, *, geometry_key: str,
                     max_dimension: int = 2_000_000) -> bool:
    """False for malformed algebraic evidence. Resource exhaustion propagates.

A geometry-key string binds a caller's contract; this checker does not certify it.
"""
    try:
        if set(cert) != {"format", "geometry_key", "source_sha256", "kept", "expressions_hex"}:
            return False
        if cert["format"] != "rooted-disc-basis-v1" or cert["geometry_key"] != geometry_key:
            return False
        payload = {"geometry_key": geometry_key, "candidates": [c.as_dict() for c in candidates]}
        digest = hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        if cert["source_sha256"] != digest:
            return False
        if candidates and any((c.state.r, c.state.q) != (candidates[0].state.r, candidates[0].state.q) for c in candidates):
            return False
        kept = cert["kept"]
        if not isinstance(kept, list) or any(type(i) is not int or not 0 <= i < len(candidates) for i in kept):
            return False
        if len(set(kept)) != len(kept) or len(cert["expressions_hex"]) != len(candidates):
            return False
        dimension = candidates[0].state.q * 3 ** (candidates[0].state.r - 1) if candidates else 0
        if len(kept) > dimension:
            return False
        rows = [reference_feature(candidates[i].state, max_dimension) for i in kept]
        # Independence certifies the stated size argument, not just representativity.
        echelon = {}
        for original in rows:
            x = original
            while x:
                leading = x.bit_length() - 1
                if leading not in echelon:
                    echelon[leading] = x
                    break
                x ^= echelon[leading]
            else:
                return False
        for i, text in enumerate(cert["expressions_hex"]):
            if not isinstance(text, str) or not text.startswith("0x"):
                return False
            mask = int(text, 16)
            if mask < 0 or mask.bit_length() > len(kept):
                return False
            reconstructed = 0
            for j, row in enumerate(rows):
                if mask >> j & 1:
                    if candidates[kept[j]].cost > candidates[i].cost:
                        return False
                    reconstructed ^= row
            if reconstructed != reference_feature(candidates[i].state, max_dimension):
                return False
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError):
        return False
