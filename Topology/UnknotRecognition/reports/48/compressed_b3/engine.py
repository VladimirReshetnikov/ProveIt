"""Compressed C2*C3 reduction and complete three-braid closure recognition."""
from copy import deepcopy
from hashlib import sha256
import json

from .grammar import validate
from .strings import Arena, Limit

# x = aba (order 2 modulo the centre), y = ab (order 3), z = y^2.
IMAGE = {1: (3, 1), -1: (1, 2), 2: (1, 3), -2: (2, 1)}
INV = {1: 1, 2: 3, 3: 2}
VERSION = 'compressed-three-braid-v1'


def same_factor(a, b):
    return (a == 1) == (b == 1)


class Reducer:
    """Uses only the string interface provided by Arena or upstream WordArena."""
    def __init__(self, arena):
        self.a = arena
        self.inverses = {0: 0}
        self.multiplications = 0

    def inverse(self, root):
        pending = [(root, False)]
        while pending:
            self.a.tick()
            node, ready = pending.pop()
            if node in self.inverses:
                continue
            rule = self.a.rules[node]
            if rule[0] == 't':
                result = self.a.letter(INV[rule[1]])
            elif ready:
                result = self.a.concat(self.inverses[rule[2]], self.inverses[rule[1]])
            else:
                pending.extend(((node, True), (rule[1], False), (rule[2], False)))
                continue
            self.inverses[node], self.inverses[result] = result, node
        return self.inverses[root]

    def multiply(self, u, v):
        self.multiplications += 1
        a = self.a
        k = a.lcp(self.inverse(u), v) if u and v else 0
        left = a.slice(u, 0, a.lengths[u] - k)
        right = a.slice(v, k, a.lengths[v])
        if left and right and same_factor(a.last[left], a.first[right]):
            # Maximal inverse cancellation leaves precisely equal y or z.
            token = a.last[left]
            if token == 1 or token != a.first[right]:
                raise RuntimeError('maximal boundary cancellation invariant failed')
            left = a.slice(left, 0, a.lengths[left] - 1)
            right = a.slice(right, 1, a.lengths[right])
            result = a.concat(a.concat(left, a.letter(INV[token])), right)
        else:
            result = a.concat(left, right)
        return result, k

    def cyclic(self, word):
        a = self.a
        size = a.lengths[word]
        t = a.lcp(word, self.inverse(word), size // 2) if size > 1 else 0
        core = a.slice(word, t, size - t)
        conjugator = a.slice(word, 0, t)
        merged = False
        if a.lengths[core] > 1 and same_factor(a.first[core], a.last[core]):
            first = a.first[core]
            if first == 1 or first != a.last[core]:
                raise RuntimeError('cyclic maximality invariant failed')
            conjugator = a.concat(conjugator, a.letter(first))
            core = a.concat(a.slice(core, 1, a.lengths[core] - 1), a.letter(INV[first]))
            merged = True
        return core, conjugator, t, merged


def small_word(a, root, cap=4):
    if a.lengths[root] > cap:
        return None
    # Read at most four tokens. Never calls the debug expansion oracle.
    tokens, pending = [], [root]
    while pending:
        a.tick()
        node = pending.pop()
        if not node:
            continue
        rule = a.rules[node]
        if rule[0] == 't':
            tokens.append(rule[1])
        else:
            pending.extend((rule[2], rule[1]))
    return tokens


def decide_core(exponent, tokens):
    if exponent == 2:
        return tokens == [2]
    if exponent == -2:
        return tokens == [3]
    return (exponent == 0 and tokens is not None and len(tokens) == 4
            and tokens.count(1) == 2 and tokens.count(2) == tokens.count(3) == 1)


def _normal_form(data, arena):
    reducer = Reducer(arena)
    roots, cancellations = [0], ['0x0']
    for rule in data['rules'][1:]:
        if rule[0] == 'g':
            root = arena.from_word(IMAGE[rule[1]])
            k = 0
        else:
            root, k = reducer.multiply(roots[rule[1]], roots[rule[2]])
        roots.append(root)
        cancellations.append(hex(k))
    core, conjugator, t, merged = reducer.cyclic(roots[data['root']])
    return roots, cancellations, core, conjugator, t, merged


def normal_form(data, *, arena_factory=Arena, **arena_options):
    """Research API: always compute the quotient, even for links/high writhe."""
    summary = validate(data)
    arena = arena_factory(**arena_options)
    proof = _normal_form(data, arena)
    return summary, arena, proof


def recognize(data, *, arena_factory=Arena, **arena_options):
    """Return a complete verdict plus certificate, or propagate a resource cap.

    Invalid input raises ValueError. A resource exception must be treated as
    inconclusive; it is never converted to UNKNOT/KNOTTED. The CLI catches it.
    Full knot decisions apply only to exactly three strands.
    """
    summary = validate(data)
    e, n = summary.exponents[summary.root], summary.lengths[summary.root]
    cert = dict(version=VERSION, input=deepcopy(data), input_sha256=sha256(
        json.dumps(data, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
        exponent_hex=hex(e), length_hex=hex(n),
        permutation=list(summary.permutations[summary.root]))
    if not summary.knot:
        cert.update(phase='finite', status='LINK')
        return dict(status='LINK', certificate=cert, stats={})
    if abs(e) > 2:
        cert.update(phase='finite', status='KNOTTED')
        return dict(status='KNOTTED', certificate=cert, stats={})
    arena = arena_factory(**arena_options)
    roots, cancellations, core, conjugator, t, merged = _normal_form(data, arena)
    tokens = small_word(arena, core)
    status = 'UNKNOT' if decide_core(e, tokens) else 'KNOTTED'
    cert.update(phase='quotient', status=status,
                string_rules=[list(r) if r is not None else ['e'] for r in arena.rules],
                reduced_roots=roots, cancellations_hex=cancellations,
                cyclic=dict(core=core, conjugator=conjugator, trim_hex=hex(t), merged=merged),
                core_length_hex=hex(arena.lengths[core]), core_tokens=tokens)
    stats = dict(arena.stats)
    stats.update(input_rules=len(data['rules'])-1, arena_nodes=len(arena.rules)-1,
                 max_height=max(getattr(arena, 'heights', [0])),
                 reduced_length_bits=arena.lengths[roots[data['root']]].bit_length(),
                 core_length_bits=arena.lengths[core].bit_length())
    return dict(status=status, certificate=cert, stats=stats)
