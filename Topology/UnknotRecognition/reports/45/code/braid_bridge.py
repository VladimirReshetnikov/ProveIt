"""Capped literal braid-to-presentation demonstration with replayed certificates.

This is an isolated research bridge, NOT the maintained fastunknot recognizer.
Its Artin-word expansion may be exponential. Crossing and letter caps return
INCONCLUSIVE, never a nontrivial-knot verdict. The compressed terminal query
and its independent checker are charged inside each successful demonstration.
"""
from __future__ import annotations
from collections import deque
from christoffel import Arena, scan_aligned, ResourceLimit, PowerCertificate
from checker import verify_power
from oracle import freely_reduce, cyclic_reduce, inverse, whitehead_primitive_power


def validate_braid(strands, word):
    if type(strands) is not int or not 1 <= strands <= 100:
        raise ValueError('strand count must be in [1,100]')
    if not isinstance(word, (list, tuple)) or any(type(x) is not int or not 0 < abs(x) < strands for x in word):
        raise ValueError('invalid braid word')
    permutation = list(range(strands))
    for x in word:
        i = abs(x)-1
        permutation[i], permutation[i+1] = permutation[i+1], permutation[i]
    seen, cycles = set(), 0
    for i in range(strands):
        if i not in seen:
            cycles += 1
            while i not in seen:
                seen.add(i); i = permutation[i]
    if cycles != 1:
        raise ValueError('closure must be a single-component classical knot')


def presentation(strands, word, cap):
    images = [tuple([i+1]) for i in range(strands)]
    for x in word:
        i = abs(x)-1; a, b = images[i:i+2]
        if 2*len(a)+2*len(b) > cap:
            raise ResourceLimit('literal Artin image limit')
        if x > 0:
            images[i:i+2] = [freely_reduce(a+b+inverse(a)), a]
        else:
            images[i:i+2] = [b, freely_reduce(inverse(b)+a+b)]
        if sum(map(len, images)) > cap:
            raise ResourceLimit('literal Artin volume limit')
    return [cyclic_reduce(w+(-(i+1),)) for i, w in enumerate(images)]


def eliminate(words, slot, generator, cap):
    word = words[slot]
    positions = [i for i, x in enumerate(word) if abs(x) == generator]
    if len(positions) != 1:
        raise ValueError('not a defining relation')
    k = positions[0]; P, x, S = word[:k], word[k], word[k+1:]
    replacement = inverse(P)+inverse(S) if x > 0 else S+P
    inverted = inverse(replacement)
    output = []
    for j, r in enumerate(words):
        if j == slot:
            output.append(()); continue
        estimated = sum(len(replacement) if abs(y) == generator else 1 for y in r)
        if estimated > cap:
            raise ResourceLimit('literal substitution limit')
        output.append(cyclic_reduce(z for y in r for z in
                      (replacement if y == generator else inverted if y == -generator else (y,))))
    if sum(map(len, output)) > cap:
        raise ResourceLimit('literal relation volume limit')
    return output


def _terminal(words, alive, engine):
    if len(alive) == 1:
        return {'kind': 'one_generator'} if not any(words) else None
    if len(alive) != 2: return None
    a, b = sorted(alive)
    trans = {a: 1, -a: -1, b: 2, -b: -2}
    renamed = [tuple(trans[x] for x in w) for w in words]
    if engine == 'whitehead':
        for slot, w in enumerate(renamed):
            if w and whitehead_primitive_power(w)[0]:
                return {'kind': 'primitive_power', 'slot': slot}
        return None
    arena = Arena()
    roots = [arena.from_word(w) for w in renamed]
    report = scan_aligned(arena.rules, roots)
    certs = report.get('certificates', [])
    if certs:
        slot, cert = certs[0]
        if not verify_power(arena.rules, cert):
            raise ArithmeticError('independent terminal replay failed')
        return {'kind': 'primitive_power', 'slot': slot}
    return None


def produce(strands, word, *, cap=100_000, engine='width', max_crossings=200):
    validate_braid(strands, word)
    if engine not in ('width', 'whitehead'): raise ValueError('unknown terminal engine')
    if type(cap) is not int or cap < 1: raise ValueError('positive cap required')
    if len(word) > max_crossings:
        return {'status': 'INCONCLUSIVE', 'reason': 'crossing limit'}
    try:
        words = presentation(strands, word, cap)
        alive = set(range(1, strands+1)); trace = []
        while True:
            terminal = _terminal(words, alive, engine)
            if terminal is not None:
                cert = dict(version=1, strands=strands, braid=list(word),
                            moves=trace, terminal=terminal)
                if not verify_braid_certificate(strands, word, cert, cap=cap):
                    raise ArithmeticError('independent braid replay failed')
                return {'status': 'UNKNOT', 'certificate': cert,
                        'terminal_relator_length': max(map(len, words), default=0)}
            candidates = [(len(r), j, g) for j, r in enumerate(words)
                          for g in sorted(alive) if sum(abs(x) == g for x in r) == 1]
            if not candidates: return {'status': 'INCONCLUSIVE', 'reason': 'search stalled'}
            _, j, g = min(candidates)
            words = eliminate(words, j, g, cap)
            alive.remove(g); trace.append({'relation': j, 'generator': g})
    except ResourceLimit as exc:
        return {'status': 'INCONCLUSIVE', 'reason': str(exc)}


def verify_braid_certificate(strands, word, certificate, *, cap=100_000):
    """Separate Artin construction, cancellation and elimination replay.

    Shares only the input-contract validator and the standalone *independent*
    algebraic certificate checker. Does not call producer helpers.
    """
    validate_braid(strands, word)
    if (type(certificate) is not dict or set(certificate) !=
        {'version', 'strands', 'braid', 'moves', 'terminal'}): return False
    if (type(certificate['version']) is not int or certificate['version'] != 1 or
        certificate['strands'] != strands or certificate['braid'] != list(word)): return False
    if not isinstance(certificate['moves'], list): return False
    def inv(w): return [-x for x in w[::-1]]
    def red(w, cyclic=False):
        stack = deque()
        count = 0
        for x in w:
            count += 1
            if count > cap: raise ResourceLimit('checker literal cap')
            if stack and stack[-1] == -x: stack.pop()
            else: stack.append(x)
        if cyclic:
            while len(stack) > 1 and stack[0] == -stack[-1]:
                stack.popleft(); stack.pop()
        return list(stack)
    images = [[i+1] for i in range(strands)]
    for x in word:
        i = abs(x)-1
        U, V = images[i], images[i+1]
        if 2*len(U)+2*len(V) > cap: raise ResourceLimit('checker Artin cap')
        images[i], images[i+1] = ((red(U+V+inv(U)), U) if x > 0 else (V, red(inv(V)+U+V)))
    relations = [red(w+[-i-1], True) for i, w in enumerate(images)]
    alive = set(range(1, strands+1))
    for move in certificate['moves']:
        if type(move) is not dict or set(move) != {'relation', 'generator'}: return False
        j, g = move['relation'], move['generator']
        if type(j) is not int or type(g) is not int or g not in alive or not 0 <= j < len(relations): return False
        r = relations[j]
        hits = [i for i, x in enumerate(r) if abs(x) == g]
        if len(hits) != 1: return False
        pos = hits[0]
        rotated_rest = r[pos+1:]+r[:pos]
        replacement = inv(rotated_rest) if r[pos] > 0 else rotated_rest
        new = []
        for slot, w in enumerate(relations):
            if slot == j: new.append([]); continue
            new.append(red((z for x in w for z in
                       (replacement if x == g else inv(replacement) if x == -g else [x])), True))
        if sum(map(len, new)) > cap: raise ResourceLimit('checker volume cap')
        relations = new; alive.remove(g)
    t = certificate['terminal']
    if t == {'kind': 'one_generator'}:
        return len(alive) == 1 and not any(relations)
    if type(t) is not dict or set(t) != {'kind', 'slot'} or t['kind'] != 'primitive_power': return False
    j = t['slot']
    if len(alive) != 2 or type(j) is not int or not 0 <= j < len(relations): return False
    names = sorted(alive)
    w = [names.index(abs(x))+1 if x > 0 else -(names.index(abs(x))+1) for x in relations[j]]
    if not w: return False
    # The checker builds a *different*, left-associated grammar from the producer.
    # It derives the candidate from letter counts and lets verify_power establish width.
    from math import gcd
    u = w.count(1)-w.count(-1); v = w.count(2)-w.count(-2)
    d = gcd(abs(u), abs(v))
    if not d: return False
    rules, root = [None], 0
    for x in w:
        leaf = len(rules); rules.append(('t', x))
        if root:
            rules.append(('c', root, leaf)); root = len(rules)-1
        else: root = leaf
    u //= d; v //= d
    return verify_power(rules, PowerCertificate(root, u, v, d, abs(u)+abs(v)-1))
