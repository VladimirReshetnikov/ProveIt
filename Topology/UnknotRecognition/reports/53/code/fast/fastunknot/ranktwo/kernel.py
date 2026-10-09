"""Optimal one-pass shortening in rank-two parabolic braid corridors.

Allowed replacements are the empty word (radius=0), or additionally one Artin
letter (radius=1). Intervals selected in one pass are disjoint in that pass's
input. The optimizer is exact for this finite class of replacements, not for
arbitrary braid isotopy. All output certificates are independently replayable.
"""
from __future__ import annotations
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from .common import validate_word, input_digest
from .orderedmap import AVLBestMap, HashBestMap
from .search_group import QuotientTrie

Check = Callable[[], None]


@dataclass(frozen=True, slots=True)
class Corridor:
    start: int
    stop: int
    indices: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class Replacement:
    start: int
    stop: int
    target: int  # 0 denotes the empty word.


def maximal_corridors(word: tuple[int, ...]) -> list[Corridor]:
    """All maximal two-index corridors, with total length at most 2*len(word).

    Compress maximal runs with the same absolute generator index. Consecutive
    run-edges with the same unordered pair form one corridor. Neighboring
    corridors overlap in one run; non-neighbors are disjoint.
    """
    if not word:
        return []
    runs: list[tuple[int, int, int]] = []
    start = 0
    for i in range(1, len(word) + 1):
        if i == len(word) or abs(word[i]) != abs(word[start]):
            runs.append((start, i, abs(word[start])))
            start = i
    if len(runs) == 1:
        return [Corridor(0, len(word), (runs[0][2],))]
    result: list[Corridor] = []
    first_edge = 0
    pair = tuple(sorted((runs[0][2], runs[1][2])))
    for edge in range(1, len(runs) - 1):
        new_pair = tuple(sorted((runs[edge][2], runs[edge + 1][2])))
        if new_pair != pair:
            result.append(Corridor(runs[first_edge][0], runs[edge][1], pair))
            first_edge, pair = edge, new_pair
    result.append(Corridor(runs[first_edge][0], runs[-1][1], pair))
    return result


class _Context:
    __slots__ = ('corridor', 'trie', 'table', 'node', 'exponent', 'counts',
                 'adjacent', 'targets')

    def __init__(self, corridor: Corridor, trie: QuotientTrie, backend: str,
                 radius: int, prefix_score: int) -> None:
        self.corridor = corridor
        self.trie = trie
        self.table = AVLBestMap() if backend == 'avl' else HashBestMap()
        self.node = self.exponent = 0
        self.counts = [0, 0]
        self.adjacent = (len(corridor.indices) == 2 and
                         corridor.indices[1] == corridor.indices[0] + 1)
        self.targets = (0,) if radius == 0 else (0,) + tuple(
            g for i in corridor.indices for g in (i, -i))
        self.table.put_best((0, 0), (prefix_score - corridor.start, corridor.start))

    def advance(self, generator: int) -> None:
        position = 0 if abs(generator) == self.corridor.indices[0] else 1
        sign = 1 if generator > 0 else -1
        if self.adjacent:
            self.node = self.trie.append_generator(self.node, sign * (position + 1))
            self.exponent += sign
        else:
            self.counts[position] += sign

    def key(self, target: int = 0) -> tuple[int, int]:
        if self.adjacent:
            if not target:
                return self.node, self.exponent
            position = 0 if abs(target) == self.corridor.indices[0] else 1
            sign = 1 if target > 0 else -1
            node = self.trie.append_generator(self.node, -sign * (position + 1))
            return node, self.exponent - sign
        a, b = self.counts
        if target:
            sign = 1 if target > 0 else -1
            if abs(target) == self.corridor.indices[0]:
                a -= sign
            else:
                b -= sign
        return a, b


def optimal_pass(strands: int, word: Iterable[int], *, radius: int = 1,
                 dictionary: str = 'avl', check: Check | None = None
                 ) -> tuple[tuple[int, ...], list[Replacement], dict[str, int | str]]:
    """Minimize output length among disjoint allowed replacements in the input.

    Deterministic O(n log n) word-RAM time with dictionary='avl', O(n) space.
    The optional 'hash' backend has expected O(n) dictionary time, not a
    deterministic adversarial bound. Exactness does not depend on hashing.
    """
    word = validate_word(strands, word)
    if type(radius) is not int or radius not in (0, 1):
        raise ValueError('radius must be 0 or 1')
    if dictionary not in ('avl', 'hash'):
        raise ValueError("dictionary must be 'avl' or 'hash'")
    check = (lambda: None) if check is None else check
    check()
    n = len(word)
    corridors = maximal_corridors(word)
    trie = QuotientTrie()
    best = [0] * (n + 1)
    choice: list[Replacement | None] = [None] * (n + 1)
    active: list[_Context] = []
    next_corridor = 0
    advances = queries = entries = maximum_active = 0
    for j, generator in enumerate(word):
        if j & 255 == 0:
            check()
        while next_corridor < len(corridors) and corridors[next_corridor].start == j:
            active.append(_Context(corridors[next_corridor], trie, dictionary,
                                   radius, best[j]))
            next_corridor += 1
            entries += 1
        maximum_active = max(maximum_active, len(active))
        value = best[j]
        selected: Replacement | None = None
        for context in active:
            context.advance(generator)
            advances += 1
            for target in context.targets:
                queries += 1
                previous = context.table.get(context.key(target))
                if previous is None:
                    continue
                old_score, start = previous
                candidate = j + 1 + old_score - int(target != 0)
                if candidate > value:
                    assert j + 1 - start > int(target != 0)
                    value = candidate
                    selected = Replacement(start, j + 1, target)
        best[j + 1], choice[j + 1] = value, selected
        for context in active:
            before = context.table.size
            context.table.put_best(context.key(), (value - (j + 1), j + 1))
            entries += context.table.size - before
        active = [context for context in active if context.corridor.stop > j + 1]
    plan: list[Replacement] = []
    j = n
    while j:
        selected = choice[j]
        if selected is None:
            j -= 1
        else:
            plan.append(selected)
            j = selected.start
    plan.reverse()
    output: list[int] = []
    cursor = 0
    for item in plan:
        output.extend(word[cursor:item.start])
        if item.target:
            output.append(item.target)
        cursor = item.stop
    output.extend(word[cursor:])
    assert len(output) == n - best[n]
    stats: dict[str, int | str] = {
        'input_letters': n, 'output_letters': len(output), 'saved_letters': best[n],
        'corridors': len(corridors), 'corridor_letter_sum': sum(c.stop-c.start for c in corridors),
        'group_advances': advances, 'state_queries': queries,
        'table_entries_created': entries, 'quotient_nodes': len(trie.parent),
        'quotient_token_steps': trie.token_steps, 'maximum_active_corridors': maximum_active,
        'replacement_count': len(plan), 'radius': radius, 'dictionary': dictionary,
    }
    return tuple(output), plan, stats


def compress(strands: int, word: Iterable[int], *, radius: int = 1,
             max_passes: int | None = None, dictionary: str = 'avl',
             check: Check | None = None) -> dict:
    """Apply optimal passes and return an exact, independently verifiable witness.

    max_passes=None saturates under the selected rules. It does NOT find a
    globally shortest braid or decide whether a closure is the unknot.
    Fresh node IDs are allocated sequentially for inserted target letters.
    """
    original = validate_word(strands, word)
    if max_passes is not None and (type(max_passes) is not int or max_passes < 0):
        raise ValueError('max_passes must be a nonnegative integer or None')
    # Validate options even when no pass is requested.
    if type(radius) is not int or radius not in (0, 1):
        raise ValueError('radius must be 0 or 1')
    if dictionary not in ('avl', 'hash'):
        raise ValueError("dictionary must be 'avl' or 'hash'")
    current = original
    ids = list(range(len(original)))
    next_id = len(original)
    steps: list[dict[str, int]] = []
    passes: list[dict[str, int | str]] = []
    saturated = False
    while max_passes is None or len(passes) < max_passes:
        output, plan, statistics = optimal_pass(strands, current, radius=radius,
                                                dictionary=dictionary, check=check)
        passes.append(statistics)
        if not plan:
            saturated = True
            break
        new_ids: list[int] = []
        cursor = 0
        for item in plan:
            new_ids.extend(ids[cursor:item.start])
            steps.append({'first': ids[item.start], 'last': ids[item.stop - 1],
                          'target': item.target})
            if item.target:
                new_ids.append(next_id)
                next_id += 1
            cursor = item.stop
        new_ids.extend(ids[cursor:])
        ids, current = new_ids, output
    certificate = {
        'kind': 'rank-two-braid-shortening-v1', 'strands': strands,
        'input_length': len(original), 'input_sha256': input_digest(strands, original),
        'radius': radius, 'steps': steps, 'output_word': list(current),
    }
    return {'strands': strands, 'word': list(current), 'certificate': certificate,
            'stats': {'input_letters': len(original), 'output_letters': len(current),
                      'passes': passes, 'saturated': saturated,
                      'certificate_steps': len(steps), 'fresh_nodes': next_id - len(original)}}
