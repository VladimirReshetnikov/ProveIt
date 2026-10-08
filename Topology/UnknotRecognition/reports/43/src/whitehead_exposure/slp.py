"""Binary straight-line grammars with exact adjacency summaries.

No compressed free-reduction algorithm is claimed: summary roots are required
already to expand to freely and cyclically reduced words. A bounded literal
homomorphic-image evaluator is provided separately, for replay experiments.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import Counter
from .algebra import Budget, ResourceLimit, free_reduce, cyclic_reduce, inverse

@dataclass
class Summary:
    length: int
    first: int | None
    last: int | None
    letters: Counter
    pairs: Counter
    reduced: bool


def summarize(grammar: dict, budget: Budget | None = None) -> list[Summary]:
    budget = budget or Budget()
    if type(grammar) is not dict or set(grammar) != {"alive", "nodes", "roots"}:
        raise ValueError("invalid grammar fields")
    alive, nodes, roots = grammar["alive"], grammar["nodes"], grammar["roots"]
    if (type(alive) is not list or not alive or any(type(g) is not int or g <= 0 for g in alive)
            or len(set(alive)) != len(alive) or type(nodes) is not list or type(roots) is not list):
        raise ValueError("invalid grammar header")
    allowed = set(alive)
    result = []
    for i, rule in enumerate(nodes):
        budget.tick()
        if type(rule) is not list or not rule:
            raise ValueError("invalid production")
        if rule == ["empty"]:
            result.append(Summary(0, None, None, Counter(), Counter(), True))
        elif rule[0] == "letter" and len(rule) == 2:
            x = rule[1]
            if type(x) is not int or abs(x) not in allowed:
                raise ValueError("invalid terminal")
            result.append(Summary(1, x, x, Counter({x: 1}), Counter(), True))
        elif rule[0] == "concat" and len(rule) == 3:
            j, k = rule[1:]
            if any(type(x) is not int or not 0 <= x < i for x in (j, k)):
                raise ValueError("forward or invalid nonterminal reference")
            A, B = result[j], result[k]
            letters, pairs = A.letters.copy(), A.pairs.copy()
            letters.update(B.letters)
            pairs.update(B.pairs)
            if A.length and B.length:
                pairs[A.last, B.first] += 1
            good = A.reduced and B.reduced and (not A.length or not B.length or A.last != -B.first)
            result.append(Summary(A.length+B.length, A.first if A.length else B.first,
                                  B.last if B.length else A.last, letters, pairs, good))
            budget.tick(len(letters)+len(pairs)+1)
        else:
            raise ValueError("unknown production")
    if any(type(x) is not int or not 0 <= x < len(nodes) for x in roots):
        raise ValueError("invalid root")
    for root in roots:
        s = result[root]
        if not s.reduced or (s.length > 1 and s.first == -s.last):
            raise ValueError("root is not freely and cyclically reduced")
    return result


def grammar_graphs(grammar: dict, budget: Budget | None = None):
    summaries = summarize(grammar, budget)
    graphs = []
    for root in grammar["roots"]:
        s = summaries[root]
        graph = Counter()
        for (x, y), c in s.pairs.items():
            graph[tuple(sorted((x, -y)))] += c
        if s.length:
            graph[tuple(sorted((s.last, -s.first)))] += 1
        graphs.append(dict(graph))
    return graphs


def image_values(grammar: dict, images: dict[int, tuple[int, ...]], *, cap: int = 10_000,
                 roots: list[int] | None = None) -> list[tuple[int, ...]]:
    """Bounded exact free reduction at every DAG node; never silently expands.

    This is intentionally not a general polynomial compressed word solver.
    It succeeds on the compressed barrier family because each base relator
    maps to the empty word before its power nodes are evaluated.
    """
    summarize(grammar)
    if type(cap) is not int or cap < 0:
        raise ValueError("cap must be a nonnegative integer")
    needed = set(grammar["roots"] if roots is None else roots)
    pending = list(needed)
    while pending:
        i = pending.pop()
        if type(i) is not int or not 0 <= i < len(grammar["nodes"]):
            raise ValueError("invalid requested root")
        rule = grammar["nodes"][i]
        if rule[0] == "concat":
            for j in rule[1:]:
                if j not in needed:
                    needed.add(j)
                    pending.append(j)
    values = {}
    for i, rule in enumerate(grammar["nodes"]):
        if i not in needed:
            continue
        if rule[0] == "empty":
            values[i] = ()
        elif rule[0] == "letter":
            values[i] = free_reduce(images.get(rule[1], (rule[1],)), cap=cap)
        else:
            from itertools import chain
            values[i] = free_reduce(chain(values[rule[1]], values[rule[2]]), cap=cap)
    return [cyclic_reduce(values[i]) for i in (grammar["roots"] if roots is None else roots)]


def verify_fused_exposure(grammar: dict, move: dict, *, cap: int = 10_000) -> bool:
    """Verify one exposure and Tietze elimination, then test FREE_RANK_ONE.

    The target is evaluated first. The composed quotient map is then evaluated
    on each original relation. This verifies a presentation, not a knot diagram.
    """
    try:
        from .algebra import whitehead_image
        summarize(grammar)
        if type(move) is not dict or set(move) != {"relation", "multiplier", "subset"}:
            return False
        j, a, S = move["relation"], move["multiplier"], move["subset"]
        alive = set(grammar["alive"])
        if (type(j) is not int or not 0 <= j < len(grammar["roots"]) or type(a) is not int
                or abs(a) not in alive or type(S) is not list
                or any(type(x) is not int or abs(x) not in alive for x in S)
                or len(set(S)) != len(S) or a not in S or -a in S):
            return False
        shore = set(S)
        images = {x: whitehead_image(x, a, shore) for g in alive for x in (g, -g)}
        pivot = image_values(grammar, images, cap=cap, roots=[grammar["roots"][j]])[0]
        positions = [i for i, x in enumerate(pivot) if abs(x) == abs(a)]
        if len(positions) != 1:
            return False
        p = positions[0]
        rest = pivot[p+1:]+pivot[:p]
        replacement = inverse(rest) if pivot[p] > 0 else rest
        quotient = {abs(a): replacement, -abs(a): inverse(replacement)}
        composed = {x: free_reduce(y for z in w for y in quotient.get(z, (z,))) for x, w in images.items()}
        # The defining relation is checked too; no relation is silently dropped.
        outputs = image_values(grammar, composed, cap=cap)
        return len(alive-{abs(a)}) == 1 and not any(outputs)
    except (ValueError, KeyError, TypeError, IndexError):
        return False


def grammar_from_words(words: list[tuple[int, ...]], alive: list[int]) -> dict:
    nodes = [["empty"]]
    def word_node(word):
        root = 0
        for x in word:
            nodes.append(["letter", x]); leaf = len(nodes)-1
            nodes.append(["concat", root, leaf]); root = len(nodes)-1
        return root
    roots = [word_node(w) for w in words]
    return {"alive": alive, "nodes": nodes, "roots": roots}


def barrier_grammar(exponent_bits: int) -> dict:
    """P_(2^k), with two relation roots and O(k) nodes."""
    if type(exponent_bits) is not int or exponent_bits < 0:
        raise ValueError("exponent_bits must be nonnegative")
    u = (1, 1, 2, 1, 2)
    t = (1, -2)*3
    v = cyclic_reduce(u+t+inverse(u)+inverse(t))
    grammar = grammar_from_words([u, v], [1, 2])
    root = grammar["roots"][1]
    for _ in range(exponent_bits):
        grammar["nodes"].append(["concat", root, root])
        root = len(grammar["nodes"])-1
    grammar["roots"][1] = root
    return grammar
