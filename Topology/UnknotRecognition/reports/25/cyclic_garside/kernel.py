"""Optimal disjoint radius-one replacements over all supports and cyclic cuts.

Group operations are shared over one doubled word. Canonical state lookup uses
sorting and binary search, not probabilistic fingerprints or hash-table bounds.
"""
from __future__ import annotations
from bisect import bisect_left
from dataclasses import asdict
from hashlib import sha256
import json
from .normalform import (IDENTITY, Budget, Counters, append, normal_form, validate)


def input_digest(b: int, word: tuple[int, ...]) -> str:
    raw = json.dumps([b, list(word)], separators=(",", ":")).encode("ascii")
    return sha256(raw).hexdigest()


def length_lower_bound(b: int, word: tuple[int, ...]) -> int:
    """Conjugacy-invariant lower bound: max(|exponent|, b - permutation cycles)."""
    order = list(range(b))
    for a in word:
        i = abs(a) - 1
        order[i], order[i + 1] = order[i + 1], order[i]
    seen = [False] * b
    cycles = 0
    for i in range(b):
        if seen[i]:
            continue
        cycles += 1
        j = i
        while not seen[j]:
            seen[j] = True
            j = order[j]
    exponent = sum(1 if a > 0 else -1 for a in word)
    return max(abs(exponent), b - cycles)


def _prepare(b, word, cyclic, counters, budget):
    source = word + word if cyclic else word
    states = [IDENTITY]
    for a in source:
        state, _ = append(states[-1], a, b, counters=counters, budget=budget)
        states.append(state)
    counters.prefix_height = max(counters.prefix_height,
                                 max(len(s[1]) for s in states))
    # Exact, deterministic canonical-state interning. No set/dict is needed.
    unique = []
    for state in sorted(states):
        if not unique or state != unique[-1]:
            unique.append(state)
    ids = [bisect_left(unique, s) for s in states]
    targets = (0,) + tuple(a for i in range(1, b) for a in (i, -i))
    queries = [None] * len(states)
    for j, state in enumerate(states):
        if j == 0:
            continue
        row = [ids[j]]
        for target in targets[1:]:
            q, _ = append(state, -target, b, counters=counters, budget=budget)
            pos = bisect_left(unique, q)
            row.append(pos if pos < len(unique) and unique[pos] == q else -1)
        queries[j] = row
    return ids, queries, targets, len(unique)


def _solve_cut(n, cut, ids, queries, targets, count, budget):
    negative = -10 * (n + 1)
    best_scores = [negative] * count
    starts = [-1] * count
    best_scores[ids[cut]] = 0
    starts[ids[cut]] = 0
    score = [0] * (n + 1)
    previous = [(0, None)] * (n + 1)
    checks = 0
    for j in range(1, n + 1):
        if budget:
            budget.check()
        value, choice = score[j - 1], (j - 1, None)
        for target, key in zip(targets, queries[cut + j]):
            checks += 1
            if key < 0 or starts[key] < 0:
                continue
            candidate = j - int(target != 0) + best_scores[key]
            if candidate > value:
                value = candidate
                choice = (starts[key], target)
        score[j], previous[j] = value, choice
        key = ids[cut + j]
        candidate = value - j
        if candidate > best_scores[key]:
            best_scores[key], starts[key] = candidate, j
    replacements = []
    j = n
    while j:
        i, target = previous[j]
        if target is not None:
            replacements.append((i, j, target))
        j = i
    replacements.reverse()
    return n - score[n], replacements, checks


def compress(b: int, word, *, cyclic: bool = True,
             stop_at_lower_bound: bool = True,
             budget: Budget | None = None) -> dict:
    """Return a shortest one-pass radius-one kernel and a replay certificate.

    cyclic=False preserves the braid element itself. cyclic=True preserves the
    oriented closure (via one recorded cyclic rotation). Neither mode is a
    standalone unknot recognizer. A LimitExceeded exception supplies no verdict.
    The lower-bound shortcut, when enabled, is exact, not heuristic.
    """
    word = validate(b, word)
    n = len(word)
    stats = Counters()
    lower = length_lower_bound(b, word)
    best_cut, best_length, best_plan, checks, rotations = 0, n, [], 0, 0
    unique_count = 0
    if n and not (stop_at_lower_bound and lower == n):
        ids, queries, targets, unique_count = _prepare(b, word, cyclic, stats, budget)
        for cut in range(n if cyclic else 1):
            value, plan, scanned = _solve_cut(n, cut, ids, queries, targets,
                                            unique_count, budget)
            rotations += 1
            checks += scanned
            if value < best_length:
                best_length, best_cut, best_plan = value, cut, plan
            if stop_at_lower_bound and best_length == lower:
                break
    algebra_appends = stats.appends
    rotated = word[best_cut:] + word[:best_cut]
    records, output = [], []
    endpoint = 0
    for i, j, target in best_plan:
        output.extend(rotated[endpoint:i])
        if target:
            output.append(target)
        _, proof = normal_form(b, rotated[i:j], trace=True, counters=stats,
                               budget=budget)
        records.append({"start": i, "end": j, "target": target, "proof": proof})
        endpoint = j
    output.extend(rotated[endpoint:])
    assert len(output) == best_length
    certificate = {
        "schema": "cyclic-garside-kernel-v1", "strands": b,
        "input_digest": input_digest(b, word), "mode": "cyclic" if cyclic else "linear",
        "rotation": best_cut, "output": output, "replacements": records,
    }
    details = asdict(stats)
    details.update({"input_length": n, "output_length": best_length,
                    "lower_bound": lower, "rotations_evaluated": rotations,
                    "dp_target_checks": checks, "unique_prefix_states": unique_count,
                    "lower_bound_attained": best_length == lower,
                    "algebra_appends_before_proof": algebra_appends})
    return {"word": output, "certificate": certificate, "stats": details}
