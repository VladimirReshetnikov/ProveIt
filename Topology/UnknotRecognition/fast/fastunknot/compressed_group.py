"""Compressed replay of group-certificate moves after independent PD recovery.

This module never calls the producer's algebra or search helpers. It preserves
exact SLP words across moves and uses deterministic compressed free reduction.
Search itself remains explicit; this is a separately selectable verifier.
"""
from .compressed_words import WordArena, CompressedLimit


def verify_moves(words, alive, certificate, budget, max_nodes, stats):
    arena = WordArena(max_nodes=max_nodes, max_work=budget.left, check=budget.check)
    roots = [arena.reduce(arena.from_word(word)) for word in words]
    try:
        for move in certificate['moves']:
            arena.tick()
            if type(move) is not dict:
                return False
            kind = move.get('kind')
            if kind == 'eliminate':
                if set(move) != {'kind', 'relation', 'generator'}:
                    return False
                index, g = move['relation'], move['generator']
                if (type(index) is not int or not 0 <= index < len(roots)
                        or type(g) is not int or g not in alive):
                    return False
                count, position, signed = arena.occurrence(roots[index], g)
                if count != 1:
                    return False
                root = roots[index]
                suffix = arena.slice(root, position+1, arena.lengths[root])
                prefix = arena.slice(root, 0, position)
                value = arena.concat(suffix, prefix)
                if signed > 0:
                    value = arena.inverse(value)
                value = arena.reduce(value)
                images = {g: value, -g: arena.inverse(value)}
                roots[index] = 0
                alive.remove(g)
                roots = [arena.cyclic_reduce(x) for x in arena.substitute(roots, images)]
            elif kind == 'whitehead':
                if set(move) != {'kind', 'multiplier', 'subset'}:
                    return False
                a, subset = move['multiplier'], move['subset']
                if type(subset) is list:
                    arena.tick(len(subset))
                if (type(a) is not int or abs(a) not in alive or type(subset) is not list
                        or any(type(x) is not int or abs(x) not in alive for x in subset)
                        or len(set(subset)) != len(subset) or a not in subset or -a in subset):
                    return False
                subset, images = set(subset), {}
                for g in alive:
                    letters = [g]
                    if g != abs(a):
                        if -g in subset:
                            letters = [-a]+letters
                        if g in subset:
                            letters += [a]
                    images[g] = arena.from_word(letters)
                    images[-g] = arena.inverse(images[g])
                roots = [arena.cyclic_reduce(x) for x in arena.substitute(roots, images)]
            elif kind == 'relator':
                if certificate['version'] != 2 or set(move) != {
                        'kind', 'target', 'donor', 'target_rotation', 'donor_rotation', 'inverse', 'overlap'}:
                    return False
                target, donor = move['target'], move['donor']
                if (type(target) is not int or type(donor) is not int or target == donor
                        or not 0 <= target < len(roots) or not 0 <= donor < len(roots)
                        or not roots[target] or not roots[donor] or type(move['inverse']) is not bool):
                    return False
                offset, start, overlap = move['target_rotation'], move['donor_rotation'], move['overlap']
                left, right = roots[target], roots[donor]
                ll, rr = arena.lengths[left], arena.lengths[right]
                if (type(offset) is not int or not 0 <= offset < ll
                        or type(start) is not int or not 0 <= start < rr
                        or type(overlap) is not int or not 0 < overlap <= min(ll, rr)):
                    return False
                left = arena.concat(arena.slice(left, offset, ll), arena.slice(left, 0, offset))
                if move['inverse']:
                    right = arena.inverse(right)
                right = arena.concat(arena.slice(right, start, rr), arena.slice(right, 0, start))
                if not arena.equal(arena.slice(left, 0, overlap), arena.slice(right, 0, overlap)):
                    return False
                roots[target] = arena.cyclic_reduce(arena.concat(
                    arena.inverse(arena.slice(right, overlap, rr)), arena.slice(left, overlap, ll)))
            else:
                return False
        arena.tick()
        return alive == {certificate['remaining_generator']} and not any(roots)
    finally:
        if stats is not None:
            stats.update(arena.stats, nodes=len(arena.rules)-1,
                         largest_word_bits=max(arena.lengths).bit_length())
