"""Independent replay of kernel certificates.

This module deliberately imports neither the optimizer nor the normalizer.
It checks local simple-braid equalities. It does NOT certify optimality,
normal-form uniqueness, a knot verdict, or an arbitrary Markov move.
"""
from __future__ import annotations
from hashlib import sha256
import json

class CertificateError(ValueError):
    pass

class VerificationLimit(RuntimeError):
    pass


def _require(condition, message):
    if not condition:
        raise CertificateError(message)


def _integer(x):
    return type(x) is int


def _target_state(b, target):
    if not target:
        return 0, []
    e = list(range(b))
    d = e[::-1]
    i = abs(target) - 1
    if target > 0:
        e[i], e[i + 1] = e[i + 1], e[i]
        return (1, []) if e == d else (0, [e])
    pos, nxt = d.index(i), d.index(i + 1)
    d[pos], d[nxt] = d[nxt], d[pos]
    return (-1, []) if d == e else (-1, [d])


def _replay(b, source, target, proof, allowance):
    _require(isinstance(proof, list) and len(proof) == len(source),
             "proof length does not equal source length")
    unit = list(range(b))
    half = unit[::-1]
    power, factors = 0, []
    for letter, step in zip(source, proof):
        _require(isinstance(step, dict) and set(step) == {"moves", "delta"},
                 "invalid normalization step")
        k = abs(letter) - 1
        if letter > 0:
            atom = unit.copy()
            atom[k], atom[k + 1] = atom[k + 1], atom[k]
            factors.append(atom)
        else:
            power -= 1
            factors = [[b - 1 - p[b - 1 - i] for i in range(b)] for p in factors]
            comp = half.copy()
            a, c = comp.index(k), comp.index(k + 1)
            comp[a], comp[c] = comp[c], comp[a]
            if comp != unit:
                factors.append(comp)
        moves = step["moves"]
        _require(isinstance(moves, list), "moves must be a list")
        for move in moves:
            if allowance[0] is not None:
                allowance[0] -= 1
                if allowance[0] < 0:
                    raise VerificationLimit("certificate move allowance exhausted")
            _require(isinstance(move, list) and len(move) == 2
                     and all(_integer(x) for x in move), "invalid atom-transfer record")
            at, generator = move
            _require(0 <= at < len(factors) - 1 and 1 <= generator < b,
                     "atom-transfer index outside live factors")
            i = generator - 1
            left, right = factors[at], factors[at + 1]
            a, c = left.index(i), left.index(i + 1)
            _require(a < c and right[i] > right[i + 1], "illegal simple-braid transfer")
            left[a], left[c] = left[c], left[a]
            right[i], right[i + 1] = right[i + 1], right[i]
            if right == unit:
                del factors[at + 1]
        d = step["delta"]
        _require(_integer(d) and 0 <= d <= len(factors), "invalid half-twist extraction")
        for _ in range(d):
            _require(factors[0] == half, "extracted factor is not a half-twist")
            del factors[0]
            power += 1
    _require((power, factors) == _target_state(b, target),
             "replayed braid does not equal the claimed target")


def verify(b: int, word, certificate: dict, *, max_moves: int | None = None) -> tuple[int, ...]:
    """Return the reconstructed output on success; raise on invalid/limited input."""
    _require(_integer(b) and b >= 1, "invalid strand count")
    _require(max_moves is None or (_integer(max_moves) and max_moves >= 0), "invalid move allowance")
    word = tuple(word)
    _require(all(_integer(a) and 0 < abs(a) < b for a in word), "invalid source word")
    _require(isinstance(certificate, dict), "certificate must be an object")
    required = {"schema", "strands", "input_digest", "mode", "rotation", "output", "replacements"}
    _require(set(certificate) == required, "invalid certificate fields")
    _require(certificate["schema"] == "cyclic-garside-kernel-v1", "unknown certificate schema")
    _require(_integer(certificate["strands"]) and certificate["strands"] == b,
             "certificate belongs to a different braid group")
    raw = json.dumps([b, list(word)], separators=(",", ":")).encode("ascii")
    _require(certificate["input_digest"] == sha256(raw).hexdigest(), "input digest mismatch")
    n, cut = len(word), certificate["rotation"]
    _require(_integer(cut) and (0 <= cut < n if n else cut == 0), "invalid cyclic cut")
    mode = certificate["mode"]
    _require(mode in ("linear", "cyclic") and (mode != "linear" or cut == 0),
             "a linear certificate may not rotate")
    output = certificate["output"]
    _require(isinstance(output, list) and all(_integer(a) and 0 < abs(a) < b for a in output),
             "invalid output word")
    rotated = word[cut:] + word[:cut]
    records = certificate["replacements"]
    _require(isinstance(records, list), "replacement list required")
    reconstructed, end = [], 0
    allowance = [max_moves]
    for record in records:
        _require(isinstance(record, dict) and set(record) == {"start", "end", "target", "proof"},
                 "invalid replacement fields")
        i, j, target = record["start"], record["end"], record["target"]
        _require(all(_integer(x) for x in (i, j, target)), "replacement indices must be integers")
        _require(end <= i < j <= n, "overlapping or invalid source interval")
        _require(target == 0 or 0 < abs(target) < b, "target is not a signed generator")
        _require(j - i > int(target != 0), "replacement is not strictly shorter")
        _replay(b, rotated[i:j], target, record["proof"], allowance)
        reconstructed.extend(rotated[end:i])
        if target:
            reconstructed.append(target)
        end = j
    reconstructed.extend(rotated[end:])
    _require(reconstructed == output, "output does not match the replayed intervals")
    return tuple(reconstructed)
