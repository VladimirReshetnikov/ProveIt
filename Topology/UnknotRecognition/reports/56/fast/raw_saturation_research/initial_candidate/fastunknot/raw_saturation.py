"""Complete raw-singleton saturation of an immutable presentation state.

The plan is a producer proposal, not a knot verdict. Its entries use the
existing version-eight ``elimination_batch`` schema, whose independent
replayer remains responsible for source-bound validation.

No word is expanded, normalized, substituted or allocated during discovery.
The arena's immutable occurrence metadata and cooperative-work counters may
be populated. The supplied root list and live generator set are never changed.
"""
from collections import deque
from dataclasses import dataclass


@dataclass(frozen=True)
class SourceIndex:
    """Exact source occurrence incidence, with dense local label positions."""

    roots: tuple
    labels: tuple
    incidence: tuple
    singletons: tuple
    degrees: tuple
    xors: tuple


@dataclass(frozen=True)
class ClosureResult:
    seeds: tuple
    known: tuple
    entries: tuple
    complete: bool

    def certificate_entries(self):
        return [dict(relation=slot, generator=g) for slot, g in self.entries]


def _stat(arena, name, amount=1):
    arena.stats[name] = arena.stats.get(name, 0) + amount


def build_index(arena, roots, alive):
    """Index presence and exact-once incidence using WordArena's raw masks."""
    roots = tuple(roots)
    supplied = tuple(alive)
    arena.tick(len(roots) + len(supplied) + 1)
    if any(type(g) is not int or g <= 0 for g in supplied):
        raise ValueError('live generator labels must be positive integers')
    if len(set(supplied)) != len(supplied):
        raise ValueError('live generator labels must be distinct')
    if any(type(root) is not int or not 0 <= root < len(arena.rules)
           for root in roots):
        raise ValueError('invalid source word node')
    labels = tuple(sorted(supplied))
    position = {g: i for i, g in enumerate(labels)}
    incidence = [[] for _ in labels]
    singletons, degrees, xors = [], [], []

    # This maintained operation is the sole owner of mask computation. It
    # deduplicates shared grammar traversal and counts repeated child edges.
    arena.singletons(roots)
    for slot, root in enumerate(roots):
        arena.tick()
        present, repeated = arena._letter_masks[root]
        unique, degree, xor = set(), 0, 0
        while present:
            arena.tick()
            bit = present & -present
            g = arena._letter_labels[bit.bit_length() - 1]
            if g not in position:
                raise ValueError('source word contains a non-live generator')
            p = position[g]
            incidence[p].append(slot)
            degree += 1
            xor ^= p
            if not repeated & bit:
                unique.add(p)
            present ^= bit
        singletons.append(frozenset(unique))
        degrees.append(degree)
        xors.append(xor)
    _stat(arena, 'raw_saturation_indices')
    _stat(arena, 'raw_saturation_source_incidence', sum(degrees))
    return SourceIndex(roots, labels, tuple(map(tuple, incidence)),
                       tuple(singletons), tuple(degrees), tuple(xors))


def seed_closure(arena, index, seeds):
    """Compute the least source Horn closure of one specified seed set.

Rule R -> x is enabled exactly when x occurs once in the original raw R
and every other generator in R is known. Each donor slot can fire only
once: afterward every generator in that source row is known.
    """
    seeds = tuple(seeds)
    arena.tick(len(index.labels) + 2 * len(index.degrees) + len(seeds) + 1)
    if any(type(g) is not int or g <= 0 for g in seeds):
        raise ValueError('seed labels must be positive integers')
    if len(set(seeds)) != len(seeds):
        raise ValueError('seed labels must be distinct')
    position = {g: i for i, g in enumerate(index.labels)}
    if any(g not in position for g in seeds):
        raise ValueError('seed is not a live source generator')
    known = [False] * len(index.labels)
    missing = list(index.degrees)
    remaining_xor = list(index.xors)
    for seed in seeds:
        arena.tick()
        p = position[seed]
        known[p] = True
        for slot in index.incidence[p]:
            arena.tick()
            missing[slot] -= 1
            remaining_xor[slot] ^= p
    queue = deque()
    for slot, count in enumerate(missing):
        arena.tick()
        if count == 1 and remaining_xor[slot] in index.singletons[slot]:
            queue.append(slot)
    count_known = len(seeds)
    entries = []
    while queue and count_known < len(index.labels):
        arena.tick()
        slot = queue.popleft()
        if missing[slot] != 1:
            continue
        p = remaining_xor[slot]
        if known[p] or p not in index.singletons[slot]:
            raise ArithmeticError('inconsistent raw-saturation index')
        known[p] = True
        count_known += 1
        entries.append((slot, index.labels[p]))
        _stat(arena, 'raw_saturation_rule_firings')
        for follower in index.incidence[p]:
            arena.tick()
            missing[follower] -= 1
            remaining_xor[follower] ^= p
            if (missing[follower] == 1 and
                    remaining_xor[follower] in index.singletons[follower]):
                queue.append(follower)
    result = ClosureResult(tuple(sorted(seeds)),
                           tuple(g for p, g in enumerate(index.labels) if known[p]),
                           tuple(entries), count_known == len(index.labels))
    _stat(arena, 'raw_saturation_closures')
    return result


def find_rank_one_plan(arena, roots, alive, cache=None, *, max_attempts=None):
    """Find the first successful singleton seed, or decline without mutation.

With ``max_attempts=None`` and sufficient arena resources, failure is complete
for reaching rank one by *any* sequence of raw singleton eliminations from
this frozen source, including different donor assignments and batch orders.
It says nothing about moves involving normalization, relator overlap,
Whitehead transformations, proper-power root extraction or knot type.
    """
    if max_attempts is not None and (type(max_attempts) is not int or max_attempts < 0):
        raise ValueError('max_attempts must be a nonnegative integer or None')
    if cache is not None and type(cache) is not dict:
        raise ValueError('cache must be a dictionary or None')
    _stat(arena, 'raw_saturation_queries')
    roots, alive = tuple(roots), tuple(alive)
    arena.tick(len(roots) + len(alive) + 1)
    # Strict validation precedes equality comparisons against cached integer
    # tuples, so Boolean aliases cannot reuse an otherwise valid source key.
    if any(type(g) is not int or g <= 0 for g in alive):
        raise ValueError('live generator labels must be positive integers')
    if len(set(alive)) != len(alive):
        raise ValueError('live generator labels must be distinct')
    if any(type(root) is not int or not 0 <= root < len(arena.rules)
           for root in roots):
        raise ValueError('invalid source word node')
    labels = tuple(sorted(alive))
    index = None if cache is None else cache.get('_raw_saturation_index')
    if (index is None or cache.get('_raw_saturation_arena') is not arena
            or index.roots != roots or index.labels != labels):
        index = build_index(arena, roots, alive)
        if cache is not None:
            cache['_raw_saturation_arena'] = arena
            cache['_raw_saturation_index'] = index
    if not index.labels:
        raise ValueError('raw saturation must retain a live generator')
    # From a singleton seed, the first productive source rule has at most
    # one distinct premise. If no row can supply such a rule, every singleton
    # closure is already fixed. This is an exact negative result for this
    # algebraic query and avoids running rank-many identical failed scans.
    if len(index.labels) > 1:
        first_firing = False
        for slot, degree in enumerate(index.degrees):
            arena.tick()
            if degree <= 2 and index.singletons[slot]:
                first_firing = True
                break
        if not first_firing:
            _stat(arena, 'raw_saturation_first_firing_failures')
            _stat(arena, 'raw_saturation_exhaustive_failures')
            return None
    for attempt, seed in enumerate(index.labels):
        arena.tick()
        if max_attempts is not None and attempt >= max_attempts:
            _stat(arena, 'raw_saturation_attempt_exhaustions')
            return None
        _stat(arena, 'raw_saturation_seed_attempts')
        result = seed_closure(arena, index, (seed,))
        if result.complete:
            _stat(arena, 'raw_saturation_successes')
            arena.stats['raw_saturation_selected_seed'] = seed
            return dict(seed=seed, entries=result.certificate_entries())
    _stat(arena, 'raw_saturation_exhaustive_failures')
    return None


def plan_rank_one(arena, roots, alive, *, max_attempts=None):
    """Return only the version-eight entries for a successful rank-one plan."""
    plan = find_rank_one_plan(arena, roots, alive, max_attempts=max_attempts)
    return None if plan is None else plan['entries']
