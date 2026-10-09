"""Integration seam for the pinned fastunknot Arena protocol.

No certificate is authorized by this adapter. Call the existing independent
source/primitive verifiers before accepting any changed monomial image table.
Full fastunknot pipeline integration was not run for this research delivery.
"""
from .grammar import Source


def snapshot_native(arena, roots, alive) -> Source:
    return Source.from_arena(arena, roots, alive)


def export_native(source: Source, images, dead, target_arena):
    """Rebuild into the caller's arena without word reduction or equality calls."""
    mapped = [0]
    powers = {}
    for rule in source.rules[1:]:
        target_arena.tick()
        if rule[0] == 't':
            letter = rule[1]
            target, exponent = images[abs(letter)]
            exponent *= 1 if letter > 0 else -1
            key = target, exponent
            if key not in powers:
                symbol = target if exponent > 0 else -target
                powers[key] = target_arena.power(target_arena.letter(symbol), abs(exponent))
            mapped.append(powers[key])
        else:
            mapped.append(target_arena.concat(mapped[rule[1]], mapped[rule[2]]))
    return [0 if i in dead else mapped[root] for i, root in enumerate(source.roots)]
