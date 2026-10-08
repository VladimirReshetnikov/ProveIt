"""A guarded reference hybrid; production users should retain fastunknot's backend."""
from __future__ import annotations
from collections.abc import Iterable
from .common import validate_word, component_count
from .kernel import compress
from .verify import verify
from .cube import CubeLimit, reduced_rank


def is_signed_coxeter(strands: int, word: Iterable[int]) -> bool:
    word = validate_word(strands, word)
    if len(word) != strands - 1:
        return False
    if not word:
        return True
    positive = word[0] > 0
    seen = [False] * strands
    for generator in word:
        index = abs(generator)
        if seen[index] or (generator > 0) != positive:
            return False
        seen[index] = True
    return True


def recognize_reference(strands: int, word: Iterable[int], *,
                        max_passes: int | None = 1, dictionary: str = 'avl',
                        max_crossings: int | None = 12,
                        max_dimension: int | None = 100_000) -> dict:
    word = validate_word(strands, word)
    # A one-component closure needs at least strands-1 input letters.
    if strands > len(word) + 1 or component_count(strands, word) != 1:
        raise ValueError('recognition is for knot closures, not multi-component links')
    result = compress(strands, word, max_passes=max_passes, dictionary=dictionary)
    reduced, replay = verify(strands, word, result['certificate'])
    result['verification'] = replay
    if is_signed_coxeter(strands, reduced):
        result.update(status='UNKNOT', method='verified-ranktwo-and-signed-coxeter')
        return result
    try:
        cube = reduced_rank(strands, reduced, max_crossings=max_crossings,
                            max_dimension=max_dimension)
    except CubeLimit as exc:
        result.update(status='INCONCLUSIVE', method='reference-cube-resource-limit', reason=str(exc))
        return result
    result.update(status='UNKNOT' if cube['homology_rank'] == 1 else 'KNOTTED',
                  method='verified-ranktwo-and-reduced-F2-cube', cube=cube)
    return result
