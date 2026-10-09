"""Compressed replay of group-certificate moves after independent PD recovery.

This module never calls the producer's algebra or search helpers. It preserves
exact SLP words across moves and uses deterministic compressed free reduction.
This is separate from both the explicit and compressed search implementations.
"""
from .compressed_words import WordArena, CompressedLimit


def verify_moves(words, alive, certificate, budget, max_nodes, stats):
    arena = WordArena(max_nodes=max_nodes, max_work=budget.left, check=budget.check)
    roots = [arena.reduce(arena.from_word(word)) for word in words]
    normalization_cache = {}
    try:
        skip_until = 0
        for index, move in enumerate(certificate['moves']):
            if index < skip_until:
                continue
            arena.tick()
            if type(move) is not dict:
                return False
            kind = move.get('kind')
            if kind == 'power_component_delete':
                if certificate['version'] < 10:
                    return False
                from .power_component_verify import replay_compressed_power_components
                if not replay_compressed_power_components(arena,roots,alive,move):
                    return False
                continue
            if kind == 'power_pair_delete':
                if certificate['version'] < 9:
                    return False
                from .power_pair_verify import replay_compressed_power_pairs
                if not replay_compressed_power_pairs(arena,roots,alive,move):
                    return False
                continue
            if kind == 'elimination_batch':
                if certificate['version'] < 8:
                    return False
                end = index+1
                while end < len(certificate['moves']):
                    arena.tick()
                    following = certificate['moves'][end]
                    if type(following) is not dict or following.get('kind') != kind:
                        break
                    end += 1
                if end-index >= 2:
                    from .persistent_elimination_verify import replay_compressed_block
                    if not replay_compressed_block(arena, roots, alive, certificate['moves'][index:end]):
                        return False
                    skip_until = end
                    continue
                from .elimination_batch_verify import replay_compressed_batch
                if not replay_compressed_batch(arena, roots, alive, move):
                    return False
                continue
            if kind in ('primitive_projection', 'primitive_forest'):
                required = {'primitive_projection':6, 'primitive_forest':7}
                if certificate['version'] < required[kind]:
                    return False
                end = index+1
                while end < len(certificate['moves']):
                    arena.tick()
                    following = certificate['moves'][end]
                    if (type(following) is not dict
                            or following.get('kind') not in ('primitive_projection', 'primitive_forest')):
                        break
                    if certificate['version'] < required[following['kind']]:
                        return False
                    end += 1
                if end-index >= 2:
                    from .anchored_projection_verify import replay_compressed_monomial_block
                    if not replay_compressed_monomial_block(arena,roots,alive,certificate['moves'][index:end]):
                        return False
                    skip_until = end
                    continue
                if kind == 'primitive_forest':
                    from .primitive_forest_verify import replay_compressed_forest as replay
                else:
                    from .primitive_projection_verify import replay_compressed_projection as replay
                if not replay(arena, roots, alive, move):
                    return False
                continue
            if kind == 'normalize_relators':
                if certificate['version'] < 6 or set(move) != {'kind'}:
                    return False
                from .syllable_normalize_verify import replay_cyclic_roots
                normalized = replay_cyclic_roots(arena, roots, cache=normalization_cache)
                roots = normalized if normalized is not None else [arena.cyclic_reduce(x) for x in roots]
                continue
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
            elif kind in ('whitehead', 'whitehead_power'):
                fields, exponent = {'kind', 'multiplier', 'subset'}, 1
                if kind == 'whitehead_power':
                    fields.add('exponent')
                    if (certificate['version'] < 3 or type(move.get('exponent')) is not int
                            or move['exponent'] < 2):
                        return False
                    exponent = move['exponent']
                if set(move) != fields:
                    return False
                a, subset = move['multiplier'], move['subset']
                if type(subset) is list:
                    arena.tick(len(subset))
                if (type(a) is not int or abs(a) not in alive or type(subset) is not list
                        or any(type(x) is not int or abs(x) not in alive for x in subset)
                        or len(set(subset)) != len(subset) or a not in subset or -a in subset):
                    return False
                subset, images = set(subset), {}
                power = arena.power(arena.letter(a), exponent)
                for g in alive:
                    value = arena.letter(g)
                    if g != abs(a):
                        if -g in subset:
                            value = arena.concat(arena.inverse(power), value)
                        if g in subset:
                            value = arena.concat(value, power)
                    images[g] = value
                    images[-g] = arena.inverse(images[g])
                roots = [arena.cyclic_reduce(x) for x in arena.substitute(roots, images)]
            elif kind in ('relator', 'relator_power'):
                fields = {'kind', 'target', 'donor', 'target_rotation', 'donor_rotation', 'inverse', 'overlap'}
                if kind == 'relator_power':
                    fields.add('copies')
                    if (certificate['version'] < 4 or type(move.get('copies')) is not int
                            or move['copies'] < 2):
                        return False
                if certificate['version'] < 2 or set(move) != fields:
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
                if kind == 'relator_power':
                    copies = move['copies']
                    if overlap != rr or copies > ll//rr:
                        return False
                    removed = copies*rr
                    if not arena.equal(arena.slice(left, 0, removed), arena.power(right, copies)):
                        return False
                    roots[target] = arena.cyclic_reduce(arena.slice(left, removed, ll))
                    continue
                if not arena.equal(arena.slice(left, 0, overlap), arena.slice(right, 0, overlap)):
                    return False
                roots[target] = arena.cyclic_reduce(arena.concat(
                    arena.inverse(arena.slice(right, overlap, rr)), arena.slice(left, overlap, ll)))
            else:
                return False
        arena.tick()
        if certificate['version'] in (6, 7, 8, 9, 10) and certificate['terminal'].get('kind') == 'rank_one_exponent_zero':
            from .primitive_projection_verify import verify_compressed_rank_one
            return verify_compressed_rank_one(arena, roots, alive, certificate['terminal'])
        if certificate['version'] in (5, 6, 7, 8, 9, 10):
            from .primitive_power_verify import verify_compressed_terminal
            return verify_compressed_terminal(arena, roots, alive, certificate['terminal'])
        return alive == {certificate['remaining_generator']} and not any(roots)
    finally:
        if stats is not None:
            stats.update(arena.stats, nodes=len(arena.rules)-1,
                         largest_word_bits=max(arena.lengths).bit_length())
