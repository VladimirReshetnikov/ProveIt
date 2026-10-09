"""Independent source-bound arithmetic replay.

Does not import the producer, its planner, its state class, or its profile code.
A valid replay proves the specified free-factor quotients, not source topology.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import gcd
import re
from .grammar import Source, ResourceLimit


class BadCertificate(ValueError):
    pass


@dataclass(frozen=True)
class ReplayResult:
    rank_one_zero: bool
    needs_torsion_freeness: bool
    images: dict[int, tuple[int, int]]
    alive: frozenset[int]
    dead: frozenset[int]
    contractions: int


def _int(x: object) -> int:
    if type(x) is not int:
        raise BadCertificate("integer identifier required")
    return x


def _hex(x: object, max_bits: int) -> int:
    if (type(x) is not str or len(x) > (max_bits + 3) // 4 + 4 or
            re.fullmatch(r'-?0x[0-9a-f]+', x) is None):
        raise BadCertificate("bad or overlong scalar encoding")
    n = int(x, 16)
    if abs(n).bit_length() > max_bits or hex(n) != x:
        raise BadCertificate("noncanonical or oversized scalar")
    return n


def replay(source: Source, proof: dict, max_work: int | None = None) -> ReplayResult:
    if (type(proof) is not dict or set(proof) != {'format', 'source_sha256', 'steps', 'endpoint'} or
            proof['format'] != 'source-anchored-projection-v1' or proof['source_sha256'] != source.digest):
        raise BadCertificate("source binding or top-level schema")
    if type(proof['steps']) is not list or len(proof['steps']) >= len(source.generators):
        raise BadCertificate("invalid round count")
    r = len(source.generators)
    # Conservative global cofactor bound, also used BEFORE parsing large scalars.
    bound = 4 * (r + 1) * (source.max_length.bit_length() + r.bit_length() + 2)
    images = {g: (g, 1) for g in source.generators}
    live, dead = set(source.generators), set()
    work = 0
    requires_torsion_free = False
    contractions = 0

    def tick():
        nonlocal work
        work += 1
        if max_work is not None and work > max_work:
            raise ResourceLimit("replay work limit")

    for batch in proof['steps']:
        if type(batch) is not list or not batch or len(batch) > len(live) // 2:
            raise BadCertificate("invalid batch")
        selected = []
        used, slots = set(), set()
        for item in batch:
            tick()
            if type(item) is not dict or set(item) != {'slot', 'pair', 'vector', 'exponent', 'width'}:
                raise BadCertificate("witness schema")
            slot = _int(item['slot'])
            if not 0 <= slot < len(source.roots) or slot in dead or slot in slots:
                raise BadCertificate("invalid or reused source slot")
            if type(item['pair']) is not list or len(item['pair']) != 2:
                raise BadCertificate("pair schema")
            a, b = map(_int, item['pair'])
            if a >= b or a not in live or b not in live or a in used or b in used:
                raise BadCertificate("pair is not live and disjoint")
            if type(item['vector']) is not list or len(item['vector']) != 2:
                raise BadCertificate("vector schema")
            u, v = (_hex(x, bound) for x in item['vector'])
            exponent, width = _hex(item['exponent'], bound), _hex(item['width'], bound)
            if not u or not v or exponent < 1 or gcd(abs(u), abs(v)) != 1:
                raise BadCertificate("nonprimitive coordinate vector")
            # Check only nodes actually reachable from the supplied donor root.
            # This traversal differs from the producer's full source scans.
            root = source.roots[slot]
            done = {0: (0, 0, 0, 0, 0, 0, 0, False)}
            pending = [(root, False)]
            while pending:
                tick()
                node, ready = pending.pop()
                if node in done:
                    continue
                rule = source.rules[node]
                if rule[0] == 't':
                    symbol = rule[1]
                    target, k = images[abs(symbol)]
                    sign = (1 if symbol > 0 else -1) * (1 if k > 0 else -1)
                    amount = abs(k)
                    counts = [0, 0, 0, 0]
                    foreign = target not in (a, b)
                    if not foreign:
                        counts[(0 if target == a else 2) + (0 if sign > 0 else 1)] = amount
                    delta = amount * (abs(v) if target == a else -abs(u) if target == b else 0)
                    done[node] = (*counts, delta, min(0, delta), max(0, delta), foreign)
                elif not ready:
                    pending.extend(((node, True), (rule[2], False), (rule[1], False)))
                else:
                    left, right = done[rule[1]], done[rule[2]]
                    counts = [left[i] + right[i] for i in range(4)]
                    done[node] = (*counts, left[4] + right[4],
                                  min(left[5], left[4] + right[5]),
                                  max(left[6], left[4] + right[6]), left[7] or right[7])
            ap, an, bp, bn, delta, low, high, foreign = done[root]
            if (foreign or ap and an or bp and bn or ap - an != exponent * u or
                    bp - bn != exponent * v or delta or high - low != width or
                    width != abs(u) + abs(v) - 1):
                raise BadCertificate("donor content does not verify")
            selected.append((slot, a, b, u, v, exponent))
            used.update((a, b)); slots.add(slot)
        # All content checks precede any mutation. Build a fresh table directly.
        new_images = {}
        for original, (target, power) in images.items():
            tick()
            new_target, new_power = target, power
            for slot, a, b, u, v, exponent in selected:
                if target == a:
                    new_target, new_power = a, power * abs(v)
                    break
                if target == b:
                    new_target, new_power = a, power * (-u if v > 0 else u)
                    break
            new_images[original] = new_target, new_power
        images = new_images
        for slot, a, b, u, v, exponent in selected:
            dead.add(slot); live.remove(b)
            requires_torsion_free |= exponent > 1
            contractions += 1
    one_zero = False
    if len(live) == 1:
        exps = [0]
        for rule in source.rules[1:]:
            tick()
            if rule[0] == 't':
                symbol = rule[1]
                exps.append(images[abs(symbol)][1] * (1 if symbol > 0 else -1))
            else:
                exps.append(exps[rule[1]] + exps[rule[2]])
        one_zero = all(i in dead or exps[v] == 0 for i, v in enumerate(source.roots))
    actual = 'rank_one_zero' if one_zero else 'rank_one_nonzero' if len(live) == 1 else 'stalled'
    if proof['endpoint'] != actual:
        raise BadCertificate("incorrect endpoint")
    return ReplayResult(one_zero, requires_torsion_free, images, frozenset(live), frozenset(dead), contractions)
