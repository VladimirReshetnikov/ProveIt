"""Independent version-2 verifier: source times inverse(target) must be identity.

Imports only the independent local replay checker, not search or normalization.
"""
from __future__ import annotations
from hashlib import sha256
import json
from .verify import _require, _integer, _replay


def verify_radius(b, word, certificate, *, max_moves=None, check=None):
    if check:
        check()
    _require(_integer(b) and b >= 1, "invalid strand count")
    _require(max_moves is None or (_integer(max_moves) and max_moves >= 0), "invalid move allowance")
    word = tuple(word)
    _require(all(_integer(a) and 0 < abs(a) < b for a in word), "invalid source word")
    fields = {"schema", "strands", "input_digest", "mode", "rotation", "output", "replacements", "target_radius"}
    _require(isinstance(certificate, dict) and set(certificate) == fields, "invalid certificate fields")
    _require(certificate["schema"] == "cyclic-garside-kernel-v2", "unknown certificate schema")
    _require(_integer(certificate["strands"]) and certificate["strands"] == b, "wrong braid group")
    raw = json.dumps([b, list(word)], separators=(",", ":")).encode("ascii")
    _require(certificate["input_digest"] == sha256(raw).hexdigest(), "input digest mismatch")
    radius = certificate["target_radius"]
    _require(_integer(radius) and radius >= 1, "invalid target radius")
    n, cut = len(word), certificate["rotation"]
    _require(_integer(cut) and (0 <= cut < n if n else cut == 0), "invalid cyclic cut")
    _require(certificate["mode"] in ("linear", "cyclic") and
             (certificate["mode"] != "linear" or cut == 0), "illegal linear rotation")
    output = certificate["output"]
    _require(isinstance(output, list) and all(_integer(a) and 0 < abs(a) < b for a in output), "invalid output")
    records = certificate["replacements"]
    _require(isinstance(records, list), "replacement list required")
    rotated = word[cut:]+word[:cut]
    answer, end, allowance = [], 0, [max_moves]
    for record in records:
        if check:
            check()
        _require(isinstance(record, dict) and set(record) == {"start", "end", "target", "proof"}, "invalid replacement")
        i, j, target = record["start"], record["end"], record["target"]
        _require(_integer(i) and _integer(j) and end <= i < j <= n, "invalid or overlapping interval")
        _require(isinstance(target, list) and len(target) <= radius and
                 all(_integer(a) and 0 < abs(a) < b for a in target), "invalid target word")
        _require(j-i > len(target), "replacement does not strictly shorten")
        residual = rotated[i:j] + tuple(-a for a in reversed(target))
        _replay(b, residual, 0, record["proof"], allowance, check)
        answer.extend(rotated[end:i])
        answer.extend(target)
        end = j
    answer.extend(rotated[end:])
    _require(answer == output, "claimed output differs from replay")
    if check:
        check()
    return tuple(answer)
