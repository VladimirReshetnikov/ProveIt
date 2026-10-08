"""Native classical braid-closure positive certificates for reproducible checks.

This small frontend is independent of fastunknot. It is not a complete
recognizer; a stalled positive search returns INCONCLUSIVE, never KNOTTED.
"""
from __future__ import annotations
from .algebra import cyclic_reduce
from .engine import search_presentation, verify_presentation_trace


def validate_braid(strands, word):
    if type(strands) is not int or strands < 1:
        raise ValueError("strands must be a positive integer")
    if type(word) not in (list, tuple) or any(type(x) is not int or not 1 <= abs(x) < strands for x in word):
        raise ValueError("invalid signed braid generator")
    return tuple(word)


def closure_components(strands: int, word) -> int:
    word = validate_braid(strands, word)
    permutation = list(range(strands))
    for letter in word:
        i = abs(letter)-1
        permutation[i], permutation[i+1] = permutation[i+1], permutation[i]
    seen = set()
    count = 0
    for v in range(strands):
        if v not in seen:
            count += 1
            while v not in seen:
                seen.add(v)
                v = permutation[v]
    return count


def braid_presentation(strands: int, word):
    """Full Wirtinger presentation; overpasses are continuous generators.

    All crossing relations are retained. Only the closure identifications
    are collapsed, including crossingless closed components.
    """
    word = validate_braid(strands, word)
    current = list(range(1, strands+1))
    relations = []
    for k, letter in enumerate(word):
        i, new = abs(letter)-1, strands+k+1
        left, right = current[i:i+2]
        if letter > 0:
            relations.append((left, right, -left, -new))
            current[i:i+2] = [new, left]
        else:
            relations.append((-right, left, right, -new))
            current[i:i+2] = [right, new]
    parent = list(range(strands+len(word)+1))
    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for initial, final in enumerate(current, 1):
        x, y = root(initial), root(final)
        if x != y:
            parent[max(x, y)] = min(x, y)
    classes = sorted({root(g) for g in range(1, len(parent))})
    names = {x: i+1 for i, x in enumerate(classes)}
    mapping = {g: names[root(g)] for g in range(1, len(parent))}
    words = [cyclic_reduce(mapping[abs(x)]*(1 if x > 0 else -1) for x in rel) for rel in relations]
    return words, tuple(range(1, len(classes)+1))


def _reconstruct_for_replay(strands, word):
    """Separate closure graph traversal rather than DSU; same documented convention."""
    word = validate_braid(strands, word)
    frontier = {i: i+1 for i in range(strands)}
    crossings = []
    for k, crossing in enumerate(word):
        p = abs(crossing)-1
        out = strands+k+1
        if crossing > 0:
            over, under = frontier[p], frontier[p+1]
            crossings.append([over, under, -over, -out])
            frontier[p], frontier[p+1] = out, over
        else:
            over, under = frontier[p+1], frontier[p]
            crossings.append([-over, under, over, -out])
            frontier[p], frontier[p+1] = over, out
    graph = {g: set() for g in range(1, strands+len(word)+1)}
    for p in range(strands):
        a, b = p+1, frontier[p]
        graph[a].add(b)
        graph[b].add(a)
    owner, count = {}, 0
    for g in sorted(graph):
        if g in owner:
            continue
        count += 1
        stack = [g]
        owner[g] = count
        while stack:
            for h in graph[stack.pop()]:
                if h not in owner:
                    owner[h] = count
                    stack.append(h)
    from collections import deque
    words = []
    for relation in crossings:
        reduced = deque()
        for x in relation:
            y = owner[abs(x)]*(1 if x > 0 else -1)
            if reduced and reduced[-1] == -y:
                reduced.pop()
            else:
                reduced.append(y)
        while len(reduced) > 1 and reduced[0] == -reduced[-1]:
            reduced.popleft(); reduced.pop()
        words.append(list(reduced))
    return words, list(range(1, count+1))


def verify_braid_certificate(certificate: dict, *, max_letters=600_000) -> bool:
    try:
        if type(certificate) is not dict or set(certificate) != {"method", "status", "strands", "braid", "algebra"}:
            return False
        if certificate["method"] != "braid-wirtinger-exposure-v1" or certificate["status"] != "UNKNOT":
            return False
        s, w = certificate["strands"], certificate["braid"]
        if closure_components(s, w) != 1:
            return False
        words, alive = _reconstruct_for_replay(s, w)
        algebra = certificate["algebra"]
        if type(algebra) is not dict or algebra.get("initial_words") != words or algebra.get("initial_alive") != alive:
            return False
        return verify_presentation_trace(algebra, max_letters=max_letters)
    except (ValueError, TypeError, KeyError, IndexError):
        return False


def recognize_braid(strands, word, **kwargs):
    word = validate_braid(strands, word)
    if closure_components(strands, word) != 1:
        return {"status": "INCONCLUSIVE", "reason": "closure is not one-component"}
    W, alive = braid_presentation(strands, word)
    result = search_presentation(W, alive, **kwargs)
    if result["status"] != "FREE_RANK_ONE":
        return {"status": "INCONCLUSIVE", "reason": result["reason"], "algebra": result}
    certificate = {"method": "braid-wirtinger-exposure-v1", "status": "UNKNOT", "strands": strands,
                   "braid": list(word), "algebra": result}
    if not verify_braid_certificate(certificate, max_letters=3*kwargs.get("max_letters", 200_000)):
        raise ArithmeticError("native braid certificate failed independent replay")
    return certificate
