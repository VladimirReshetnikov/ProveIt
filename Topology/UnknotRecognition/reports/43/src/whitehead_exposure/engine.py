"""Bounded rank-first positive-certificate search and independent literal replay."""
from __future__ import annotations
from collections import Counter, deque
from .algebra import (Budget, ResourceLimit, validate_words, apply_whitehead, eliminate,
                      word_graph, add_graphs, degrees)
from .selector import find_exposure
from .flow import minimum_pinned_cut


def strict_whitehead(words, alive, budget: Budget):
    """Reference all-signed-terminal min-cut policy; returns only strict gain."""
    V = tuple(sorted([-g for g in alive]+list(alive)))
    graph = add_graphs(word_graph(w) for w in words)
    degree = degrees(graph, V)
    best = (0, None, None)
    for a in V:
        proof = minimum_pinned_cut(graph, V, {a}, {-a}, budget)
        change = proof["capacity"]-degree[a]
        if change < best[0]:
            best = (change, a, set(proof["shore"]))
    return best


def search_presentation(words, alive, *, max_letters: int = 200_000,
                        max_work: int = 10_000_000, mode: str = "rank-first",
                        check=lambda: None) -> dict:
    """Return a positive algebraic trace, or INCONCLUSIVE. No negative verdict.

    'rank-first' performs <= r-1 rank drops. 'strict' is a comparison policy
    without relator-overlap moves and does not have that round bound.
    """
    if type(max_letters) is not int or max_letters < 0:
        raise ValueError("max_letters must be a nonnegative integer")
    if mode not in ("rank-first", "strict"):
        raise ValueError("invalid search mode")
    W, G = validate_words(words, alive)
    original = [list(w) for w in W]
    budget = Budget(max_work, check)
    active = set(G)
    moves = []
    trace = []
    peak = sum(map(len, W))
    try:
        if peak > max_letters:
            raise ResourceLimit("initial letter allowance exhausted")
        while len(active) > 1:
            L = sum(map(len, W))
            budget.tick(L+1)
            counts = Counter(abs(x) for w in W for x in w)
            direct = []
            for j, w in enumerate(W):
                for g, count in Counter(map(abs, w)).items():
                    if count == 1:
                        U = L-len(w)+(counts[g]-1)*(len(w)-2)
                        direct.append((U, len(w), j, g))
            if direct:
                U, _, j, g = min(direct)
                if U > max_letters:
                    raise ResourceLimit("defining-relation allocation bound exceeds cap")
                W = eliminate(W, j, g, budget, max_letters)
                moves.append({"kind": "eliminate", "relation": j, "generator": g})
                active.remove(g)
                trace.append({"kind": "direct", "before": L, "allocation_bound": U,
                              "after": sum(map(len, W))})
            elif mode == "strict":
                delta, a, S = strict_whitehead(W, sorted(active), budget)
                if delta >= 0:
                    return _result("INCONCLUSIVE", "strict Whitehead local minimum", original, G, moves, trace, peak, budget)
                Z = apply_whitehead(W, a, S, budget, 3*max_letters)
                if sum(map(len, Z)) > max_letters:
                    raise ResourceLimit("stored-letter allowance exhausted")
                W = Z
                moves.append({"kind": "whitehead", "multiplier": a, "subset": sorted(S)})
                trace.append({"kind": "strict", "before": L, "after": sum(map(len, W))})
            else:
                selection_stats = {}
                witness = find_exposure(W, sorted(active), max_after=max_letters,
                                        budget=budget, stats=selection_stats)
                if witness is None:
                    return _result("INCONCLUSIVE", "no affordable one-step exposure", original, G, moves, trace, peak, budget)
                j, a, S = witness["relation"], witness["multiplier"], set(witness["subset"])
                Z = apply_whitehead(W, a, S, budget, 3*max_letters)
                if sum(map(len, Z))-L != witness["length_change"]:
                    raise ArithmeticError("cut formula disagrees with substitution")
                peak = max(peak, sum(map(len, Z)))
                W = eliminate(Z, j, abs(a), budget, max_letters)
                if sum(map(len, W)) > witness["allocation_bound"]:
                    raise ArithmeticError("elimination bound violated")
                moves.extend([{"kind": "whitehead", "multiplier": a, "subset": sorted(S)},
                              {"kind": "eliminate", "relation": j, "generator": abs(a)}])
                active.remove(abs(a))
                trace.append({"kind": "exposure", "before": L,
                              "whitehead_after": sum(map(len, Z)), "after": sum(map(len, W)),
                              "witness": witness, "selector_stats": selection_stats})
            peak = max(peak, sum(map(len, W)))
        status = "FREE_RANK_ONE" if not any(W) else "INCONCLUSIVE"
        result = _result(status, "all relations empty" if not any(W) else "rank-one residual relations",
                         original, G, moves, trace, peak, budget)
        result["remaining_generator"] = next(iter(active))
        if status == "FREE_RANK_ONE" and not verify_presentation_trace(result, max_letters=3*max_letters):
            raise ArithmeticError("independent presentation replay rejected certificate")
        return result
    except ResourceLimit as exc:
        check()
        return _result("INCONCLUSIVE", str(exc), original, G, moves, trace, peak, budget)


def _result(status, reason, words, G, moves, trace, peak, budget):
    return {"status": status, "reason": reason, "initial_words": words, "initial_alive": list(G),
            "moves": moves, "trace": trace, "peak_stored_letters": peak, "work": budget.used}


def verify_presentation_trace(certificate: dict, *, max_letters: int = 600_000) -> bool:
    """Independent deque-based algebraic replay, no graph or flow calculations."""
    try:
        if type(certificate) is not dict or certificate.get("status") != "FREE_RANK_ONE":
            return False
        W, G = validate_words(certificate["initial_words"], certificate["initial_alive"])
        active = set(G)
        if type(certificate["moves"]) is not list:
            return False
        def normalize(stream):
            d = deque()
            for x in stream:
                if d and d[-1]+x == 0:
                    d.pop()
                else:
                    d.append(x)
                    if len(d) > max_letters:
                        raise ResourceLimit("replay stack limit")
            while len(d) > 1 and d[0]+d[-1] == 0:
                d.popleft(); d.pop()
            return tuple(d)
        for move in certificate["moves"]:
            if type(move) is not dict:
                return False
            kind = move.get("kind")
            if kind == "whitehead":
                if set(move) != {"kind", "multiplier", "subset"}:
                    return False
                a, S = move["multiplier"], move["subset"]
                if (type(a) is not int or abs(a) not in active or type(S) is not list
                        or any(type(x) is not int or abs(x) not in active for x in S)
                        or len(set(S)) != len(S) or a not in S or -a in S):
                    return False
                images = {}
                for g in active:
                    w = [g]
                    if g != abs(a):
                        if -g in S: w.insert(0, -a)
                        if g in S: w.append(a)
                    images[g] = tuple(w)
                    images[-g] = tuple(-x for x in reversed(w))
            elif kind == "eliminate":
                if set(move) != {"kind", "relation", "generator"}:
                    return False
                j, g = move["relation"], move["generator"]
                if type(j) is not int or not 0 <= j < len(W) or type(g) is not int or g not in active:
                    return False
                positions = [p for p, x in enumerate(W[j]) if x == g or x == -g]
                if len(positions) != 1:
                    return False
                p = positions[0]
                prefix, suffix = W[j][:p], W[j][p+1:]
                w = (tuple(-x for x in reversed(prefix))+tuple(-x for x in reversed(suffix))
                     if W[j][p] == g else suffix+prefix)
                images = {g: w, -g: tuple(-x for x in reversed(w))}
                W[j] = ()
                active.remove(g)
            else:
                return False
            raw = sum(sum(len(images.get(x, (x,))) for x in w) for w in W)
            if raw > max_letters:
                raise ResourceLimit("replay allocation limit")
            W = [normalize(y for x in w for y in images.get(x, (x,))) for w in W]
        return (type(certificate.get("remaining_generator")) is int
                and active == {certificate["remaining_generator"]} and not any(W))
    except (KeyError, TypeError, ValueError, IndexError):
        return False
