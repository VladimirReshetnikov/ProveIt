"""Independent replay of cyclic basis evidence using suffix image layers.

No producer, Euclidean selector, block decomposition, or source-curve compiler
is imported.  The shared trusted word kernel is the existing deterministic
WordArena.  The checker builds suffix automorphism images by a different
recursive-layer traversal, and verifies the final conjugacy classes directly.
"""

from .compressed_words import CompressedLimit, WordArena


def verify_cyclic_basis(arena, roots, generators, certificate):
    """Replay a supplied common automorphism; no rank-two restriction needed."""
    original_check, callback_failed = arena.check, False
    def callback():
        nonlocal callback_failed
        try:
            original_check()
        except BaseException:
            callback_failed = True
            raise
    arena.check = callback
    try:
        if (type(certificate) is not dict or set(certificate) !=
                {'schema', 'generators', 'moves', 'targets'} or
                certificate['schema'] != 'cyclic-basis-nielsen-v1' or
                type(certificate['generators']) is not list or
                any(type(g) is not int for g in certificate['generators']) or
                certificate['generators'] != generators or
                type(generators) is not list or
                any(type(g) is not int or g <= 0 for g in generators) or
                generators != sorted(set(generators))):
            return False
        moves, targets = certificate['moves'], certificate['targets']
        if (type(moves) is not list or type(targets) is not list or
                len(targets) != len(roots) or
                any(type(g) is not int or g not in generators for g in targets) or
                len(set(targets)) != len(targets)):
            return False
        # Each layer means the suffix automorphism after the named step.
        # Keeping all generator images at every layer costs O(rank * moves)
        # references, while new word productions depend only on changed images.
        layers = [{g: arena.letter(g) for g in generators}]
        alphabet = set(generators)
        for position in range(len(moves) - 1, -1, -1):
            arena.tick()
            step, previous = moves[position], layers[-1]
            if type(step) is not dict:
                return False
            current = dict(previous)
            operation = step.get('kind')
            if operation == 'invert':
                if set(step) != {'kind', 'generator'}:
                    return False
                x = step['generator']
                if type(x) is not int or x not in alphabet:
                    return False
                current[x] = arena.inverse(previous[x])
            elif operation == 'swap':
                if set(step) != {'kind', 'first', 'second'}:
                    return False
                x, y = step['first'], step['second']
                if (type(x) is not int or type(y) is not int or x == y or
                        x not in alphabet or y not in alphabet):
                    return False
                current[x], current[y] = previous[y], previous[x]
            elif operation == 'multiply':
                if set(step) != {'kind', 'target', 'donor', 'exponent', 'side'}:
                    return False
                x, y, exponent = step['target'], step['donor'], step['exponent']
                if (type(x) is not int or type(y) is not int or x == y or
                        x not in alphabet or y not in alphabet or
                        type(exponent) is not int or exponent == 0 or
                        step['side'] not in ('left', 'right')):
                    return False
                # Independent binary powering by a left-to-right bit scan.
                atom = previous[y] if exponent > 0 else arena.inverse(previous[y])
                power = 0
                for bit in bin(abs(exponent))[2:]:
                    power = arena.concat(power, power)
                    if bit == '1':
                        power = arena.concat(power, atom)
                current[x] = (arena.concat(power, previous[x]) if step['side'] == 'left'
                              else arena.concat(previous[x], power))
            else:
                return False
            layers.append(current)
        final = layers[-1]
        # Evaluate source grammar without calling the producer's map routine.
        memo = {0: 0}
        stack = [(root, False) for root in roots]
        while stack:
            arena.tick()
            node, ready = stack.pop()
            if node in memo:
                continue
            rule = arena.rules[node]
            if rule[0] == 't':
                letter = rule[1]
                if abs(letter) not in alphabet:
                    return False
                value = final[abs(letter)]
                memo[node] = value if letter > 0 else arena.inverse(value)
            elif ready:
                memo[node] = arena.concat(memo[rule[1]], memo[rule[2]])
            else:
                stack.extend(((node, True), (rule[2], False), (rule[1], False)))
        for root, target in zip(roots, targets):
            answer = arena.cyclic_reduce(memo[root])
            if arena.lengths[answer] != 1 or arena.first[answer] != target:
                return False
        return True
    except (KeyError, TypeError, ValueError, IndexError, CompressedLimit):
        if callback_failed:
            raise
        return False
    finally:
        arena.check = original_check


def verify_literal_cyclic_basis(words, generators, certificate, *,
                                max_nodes=1000000, max_work=10000000):
    arena = WordArena(max_nodes=max_nodes, max_work=max_work)
    try:
        roots = [arena.from_word(word) for word in words]
        return verify_cyclic_basis(arena, roots, generators, certificate)
    except (ValueError, TypeError, CompressedLimit):
        return False
