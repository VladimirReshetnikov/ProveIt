"""Independent proof replay. Does not invoke producer reduction or LCP search.

Trusted primitives: deterministic string equality/slicing and finite arithmetic.
It validates every claimed normal form, maximal cancellation, and cyclic step.
The original input grammar is compared structurally, not merely by a hash.
"""
from hashlib import sha256
import json
from .grammar import validate
from ..compressed_words import WordArena as Arena


class InvalidCertificate(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def integer_hex(value):
    require(isinstance(value, str), 'hexadecimal integer expected')
    try:
        result = int(value, 16)
    except (ValueError, TypeError) as exc:
        raise InvalidCertificate('invalid hexadecimal integer') from exc
    require(hex(result) == value, 'noncanonical hexadecimal integer')
    return result


def verify(data, certificate, *, arena_factory=Arena, **arena_options):
    """Return the certified status or raise; limits also raise, never accept."""
    check = arena_options.get('check', lambda: None)
    summary = validate(data, check=check)
    c = certificate
    require(isinstance(c, dict), 'certificate must be an object')
    require(c.get('version') == 'compressed-three-braid-v1', 'unknown certificate version')
    require(json.dumps(c.get('input'), sort_keys=True, separators=(',', ':')) ==
            json.dumps(data, sort_keys=True, separators=(',', ':')),
            'certificate is not bound to this grammar')
    digest = sha256(json.dumps(data, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(c.get('input_sha256') == digest, 'input digest mismatch')
    e, n = summary.exponents[summary.root], summary.lengths[summary.root]
    require(integer_hex(c.get('exponent_hex')) == e, 'wrong exponent')
    require(integer_hex(c.get('length_hex')) == n, 'wrong length')
    permutation = c.get('permutation')
    require(isinstance(permutation, list) and all(type(v) is int for v in permutation)
            and permutation == list(summary.permutations[summary.root]), 'wrong permutation')
    check()
    if c.get('phase') == 'finite':
        expected = 'LINK' if not summary.knot else ('KNOTTED' if abs(e) > 2 else None)
        require(expected is not None and c.get('status') == expected, 'invalid finite verdict')
        return expected
    require(c.get('phase') == 'quotient' and summary.knot and abs(e) <= 2, 'invalid phase')
    a = arena_factory(**arena_options)
    rules = c.get('string_rules')
    require(isinstance(rules, list) and rules and rules[0] == ['e'], 'invalid string grammar')
    require(len(rules) - 1 <= a.max_nodes, 'certificate node cap exceeded')
    # This list maps certificate node numbers to fresh, independently interned nodes.
    remap, reduced = [0], [True]
    for i, rule in enumerate(rules[1:], 1):
        check()
        require(isinstance(rule, list) and bool(rule), 'malformed string rule')
        if rule[0] == 't' and len(rule) == 2:
            require(type(rule[1]) is int and rule[1] in (1, 2, 3), 'invalid quotient syllable')
            remap.append(a.letter(rule[1]))
            reduced.append(True)
        elif rule[0] == 'c' and len(rule) == 3:
            u, v = rule[1:]
            require(all(type(k) is int and 0 <= k < i for k in (u, v)), 'non-acyclic string rule')
            U, V = remap[u], remap[v]
            remap.append(a.concat(U, V))
            reduced.append(reduced[u] and reduced[v] and
                           (not U or not V or ((a.last[U] == 1) != (a.first[V] == 1))))
        else:
            raise InvalidCertificate('unsupported string rule')

    def ref(index):
        require(type(index) is int and 0 <= index < len(remap), 'invalid proof root')
        return remap[index]

    # Separate anti-morphism evaluator; no producer Reducer is imported.
    inverse_cache = {0: 0}
    def inverse(root):
        todo = [(root, False)]
        while todo:
            a.tick()
            current, ready = todo.pop()
            if current in inverse_cache:
                continue
            rule = a.rules[current]
            if rule[0] == 't':
                out = a.letter({1: 1, 2: 3, 3: 2}[rule[1]])
            elif ready:
                out = a.concat(inverse_cache[rule[2]], inverse_cache[rule[1]])
            else:
                todo.extend(((current, True), (rule[1], False), (rule[2], False)))
                continue
            inverse_cache[current] = out
        return inverse_cache[root]

    roots, cancellations = c.get('reduced_roots'), c.get('cancellations_hex')
    require(isinstance(roots, list) and isinstance(cancellations, list), 'missing reduction trace')
    require(len(roots) == len(cancellations) == len(data['rules']), 'trace has wrong size')
    require(type(roots[0]) is int and roots[0] == 0 and cancellations[0] == '0x0',
            'invalid empty rule witness')
    image = {1: [3, 1], -1: [1, 2], 2: [1, 3], -2: [2, 1]}
    for i, rule in enumerate(data['rules'][1:], 1):
        check()
        W = ref(roots[i])
        require(reduced[roots[i]], 'claimed normal word is not reduced')
        k = integer_hex(cancellations[i])
        if rule[0] == 'g':
            require(k == 0 and a.equal(W, a.from_word(image[rule[1]])), 'incorrect generator image')
            continue
        U, V = ref(roots[rule[1]]), ref(roots[rule[2]])
        require(0 <= k <= min(a.lengths[U], a.lengths[V]), 'invalid cancellation length')
        tail = a.slice(U, a.lengths[U] - k, a.lengths[U])
        head = a.slice(V, 0, k)
        require(a.equal(inverse(tail), head), 'cancelled syllables are not inverse strings')
        L, R = a.slice(U, 0, a.lengths[U] - k), a.slice(V, k, a.lengths[V])
        if L and R and ((a.last[L] == 1) == (a.first[R] == 1)):
            require(a.last[L] == a.first[R] and a.last[L] in (2, 3),
                    'cancellation is not maximal')
            merged = a.letter(5 - a.last[L])
            expected = a.concat(a.concat(a.slice(L, 0, a.lengths[L] - 1), merged),
                                a.slice(R, 1, a.lengths[R]))
        else:
            expected = a.concat(L, R)
        require(a.equal(W, expected), 'incorrect reduced product')
    cyclic = c.get('cyclic')
    require(isinstance(cyclic, dict), 'missing cyclic witness')
    W, C, Q = ref(roots[data['root']]), ref(cyclic.get('core')), ref(cyclic.get('conjugator'))
    require(reduced[cyclic['core']] and reduced[cyclic['conjugator']], 'nonreduced cyclic witness')
    t, size = integer_hex(cyclic.get('trim_hex')), a.lengths[W]
    require(0 <= t <= size // 2, 'invalid cyclic trim')
    prefix, suffix = a.slice(W, 0, t), a.slice(W, size - t, size)
    require(a.equal(inverse(prefix), suffix), 'cyclic boundary is not inverse')
    R = a.slice(W, t, size - t)
    merge = a.lengths[R] > 1 and ((a.first[R] == 1) == (a.last[R] == 1))
    require(type(cyclic.get('merged')) is bool and cyclic['merged'] == merge, 'wrong cyclic merge flag')
    if merge:
        require(a.first[R] == a.last[R] and a.first[R] in (2, 3), 'cyclic trim not maximal')
        expected_C = a.concat(a.slice(R, 1, a.lengths[R] - 1), a.letter(5 - a.first[R]))
        expected_Q = a.concat(prefix, a.letter(a.first[R]))
    else:
        expected_C, expected_Q = R, prefix
    require(a.equal(C, expected_C) and a.equal(Q, expected_Q), 'incorrect core/conjugator')
    require(a.lengths[C] <= 1 or ((a.first[C] == 1) != (a.last[C] == 1)), 'not cyclically reduced')
    require(integer_hex(c.get('core_length_hex')) == a.lengths[C], 'wrong core length')
    tokens = None
    if a.lengths[C] <= 4:
        tokens, todo = [], [C]
        while todo:
            node = todo.pop()
            if node:
                rule = a.rules[node]
                if rule[0] == 't':
                    tokens.append(rule[1])
                else:
                    todo.extend((rule[2], rule[1]))
    supplied_tokens = c.get('core_tokens')
    require((supplied_tokens is None or
             (isinstance(supplied_tokens, list) and all(type(v) is int for v in supplied_tokens)))
            and supplied_tokens == tokens, 'wrong small core preview')
    positive = ((e == 2 and tokens == [2]) or (e == -2 and tokens == [3]) or
                (e == 0 and tokens is not None and sorted(tokens) == [1, 1, 2, 3]))
    expected = 'UNKNOT' if positive else 'KNOTTED'
    require(c.get('status') == expected, 'incorrect final verdict')
    check()
    return expected
