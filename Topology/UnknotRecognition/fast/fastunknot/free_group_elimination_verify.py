"""Independent literal replay of nonincreasing Tietze freeness certificates.

The checker imports neither the search policy nor its reduction routines.
It accepts any legal complete trace satisfying the advertised length bound.
"""

from hashlib import sha256
import json


def _reduced(values, check):
    stack = []
    for value in values:
        check()
        if stack and value + stack[-1] == 0:
            stack.pop()
        else:
            stack.append(value)
    first, last = 0, len(stack)
    while first < last and stack[first] + stack[last - 1] == 0:
        first += 1
        last -= 1
    return stack[first:last]


def replay_free_group(generators, relators, certificate, *, check=lambda: None):
    """Return verified rank/labels/statistics, or None for a malformed proof."""
    check()
    keys = {'schema', 'presentation_sha256', 'policy', 'moves', 'free_generators',
            'free_rank', 'trivial_relators', 'initial_reduced_length'}
    if (type(certificate) is not dict or set(certificate) != keys
            or certificate['schema'] != 'free-presentation-elimination-v1'
            or certificate['policy'] != 'nonincreasing'):
        return None
    if (type(generators) is not list or type(relators) is not list
            or any(type(g) is not int or g <= 0 for g in generators)
            or len(set(generators)) != len(generators)):
        return None
    live = set(generators)
    original, rows, dropped = [], {}, []
    for record in relators:
        if type(record) is not dict:
            return None
        r, word = record.get('id'), record.get('word')
        if (type(r) is not int or r < 0 or r in rows
                or type(word) is not list
                or any(type(x) is not int or abs(x) not in live for x in word)):
            return None
        rows[r] = word[:]
        original.append(dict(id=r, word=word))
    canonical = dict(generators=sorted(generators), relators=sorted(original, key=lambda r: r['id']))
    digest = sha256(json.dumps(canonical, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    if certificate['presentation_sha256'] != digest:
        return None
    for r in sorted(rows):
        rows[r] = _reduced(rows[r], check)
        if not rows[r]:
            dropped.append(r)
    for r in dropped:
        del rows[r]
    length = sum(len(word) for word in rows.values())
    initial = certificate['initial_reduced_length']
    moves = certificate['moves']
    if (type(initial) is not int or initial != length or type(moves) is not list
            or len(moves) > min(len(generators), len(relators))):
        return None
    lengths = [length]
    for move in moves:
        check()
        if type(move) is not list or len(move) != 2 or any(type(x) is not int for x in move):
            return None
        r, g = move
        if r not in rows or g not in live:
            return None
        donor = rows[r]
        where = [i for i, letter in enumerate(donor) if abs(letter) == g]
        if len(where) != 1:
            return None
        i = where[0]
        # p g^eps q = 1.  Cyclic conjugation gives g^eps q p = 1.
        tail = donor[i + 1:] + donor[:i]
        image = [-x for x in reversed(tail)] if donor[i] == g else tail
        inverse = [-x for x in reversed(image)]
        del rows[r]
        current_dropped = []
        for other in sorted(rows):
            word = rows[other]

            def expanded():
                for x in word:
                    if x == g:
                        yield from image
                    elif x == -g:
                        yield from inverse
                    else:
                        yield x

            value = _reduced(expanded(), check)
            rows[other] = value
            if not value:
                current_dropped.append(other)
        for other in current_dropped:
            del rows[other]
        dropped.extend(current_dropped)
        current_length = sum(len(word) for word in rows.values())
        if current_length > length:
            return None
        lengths.append(current_length)
        length = current_length
        live.remove(g)
    if rows:
        return None
    labels, rank, trivial = (certificate['free_generators'], certificate['free_rank'],
                             certificate['trivial_relators'])
    if (type(rank) is not int or rank != len(live) or type(labels) is not list
            or any(type(g) is not int for g in labels) or labels != sorted(live)
            or type(trivial) is not list or any(type(r) is not int for r in trivial)
            or trivial != sorted(dropped)):
        return None
    return dict(free_rank=rank, free_generators=labels, pivots=len(moves),
                trivial_relators=len(trivial), accepted_lengths=lengths)
