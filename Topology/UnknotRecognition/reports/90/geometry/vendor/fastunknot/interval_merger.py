"""Schedule the existing greedy periodic closure with quadratic pair tests.

This module deliberately does not implement periodic mathematics: ``merge``
is the caller's existing exact merger, and returns a replacement or ``None``.
The queue schedules exactly the same successful pairs as a nested left/right
scan that restarts after every success.  Stable original positions preserve
list order when a right operand is deleted.  Version stamps invalidate a
candidate when either operand has changed.

For k input rows there are at most (k - 1)**2 calls of ``merge`` when k >= 1.
This is a per-closure claim.  The heap has O(k**2) entries in the worst case;
there is no claim that the full AHT algorithm has quadratically many tests.
"""

from dataclasses import dataclass
from heapq import heapify, heappop, heappush


@dataclass(frozen=True, slots=True)
class ClosureResult:
    pairings: list
    pair_tests: int
    mergers: int
    peak_queue: int
    stale_pops: int
    queue_switches: int = 0
    queue_runs: int = 0
    overlap_candidates: int = 0
    support_scans: int = 0


def periodic_closure(pairings, *, merge, check=lambda: None, operations=None):
    """Return the ordinary lexicographically greedy periodic closure.

    ``pairings`` is not mutated. ``merge(first, second)`` is invoked only on
    rows whose ``periodic`` property is true.  It must be deterministic and
    side-effect free and produce the same replacement as the former scan.
    ``operations`` may be an existing mutable trace list; canonical current
    list indices are appended for each successful merge.

    A raising ``check`` propagates; no partial result is returned.  It is
    polled during every input/candidate/update/output scan and queue pop.
    Queue initialisation and heap operations are ordinary Python operations,
    not preemptible hard-real-time operations.
    """
    check()
    rows = list(pairings)
    active = {}
    periodic = set()
    for key, row in enumerate(rows):
        check()
        active[key] = row
        if row.periodic:
            periodic.add(key)
    generation = [0] * len(rows)
    queue = []
    pair_tests = mergers = stale_pops = peak_queue = 0

    def candidate(left, right):
        nonlocal pair_tests
        check()
        pair_tests += 1
        replacement = merge(active[left], active[right])
        if replacement is None:
            return None
        return (left, right, generation[left], generation[right], replacement)

    keys = sorted(periodic)
    for offset, left in enumerate(keys):
        check()
        for right in keys[offset + 1:]:
            entry = candidate(left, right)
            if entry is not None:
                queue.append(entry)
    heapify(queue)
    peak_queue = len(queue)

    while queue:
        check()
        left, right, left_version, right_version, replacement = heappop(queue)
        if (left not in active or right not in active
                or generation[left] != left_version
                or generation[right] != right_version):
            stale_pops += 1
            continue
        if operations is not None:
            # There are at most k - 1 mergers, so these rank scans add at
            # most O(k**2) work without a second mutable indexing structure.
            left_index = right_index = 0
            for key in active:
                check()
                left_index += key < left
                right_index += key < right
            operations.append({'op': 'merge', 'left': left_index,
                               'right': right_index})
        active[left] = replacement
        del active[right]
        generation[left] += 1
        periodic.discard(right)
        if replacement.periodic:
            periodic.add(left)
        else:
            periodic.discard(left)
        mergers += 1

        # Every untouched pair retains its old candidate or old failure.
        # Only the replacement can have gained/lost legal incident edges.
        if left in periodic:
            for other in periodic:
                check()
                if other == left:
                    continue
                first, second = sorted((left, other))
                entry = candidate(first, second)
                if entry is not None:
                    heappush(queue, entry)
        peak_queue = max(peak_queue, len(queue))

    result = []
    for row in active.values():
        check()
        result.append(row)
    return ClosureResult(result, pair_tests, mergers, peak_queue, stale_pops,
                         queue_runs=1)


def support_closure(pairings, *, merge, check=lambda: None, operations=None):
    """Greedy closure specialized to periodic interval supports.

    Disjoint supports cannot pass either maintained periodic merger rule.
    After the first candidate fails, a sweep lists only overlapping supports,
    in original lexicographic pair order. Charge every enumerated overlap
    against the original all-pairs allowance, then fall back to the existing
    quadratic queue. Dense/repeated index builds cannot create cubic work.
    The generic hybrid_closure remains available for non-geometric mergers.
    """
    check()
    pairs = list(pairings)
    allowance = len(pairs)*(len(pairs)-1)//2
    spent = tests = mergers = overlaps = scans = 0

    def finish(queued=None):
        if queued is None:
            return ClosureResult(pairs, tests, mergers, 0, 0,
                                 overlap_candidates=overlaps, support_scans=scans)
        return ClosureResult(queued.pairings, tests+queued.pair_tests,
            mergers+queued.mergers, queued.peak_queue, queued.stale_pops,
            1, queued.queue_runs, overlaps, scans)

    def fallback():
        return finish(periodic_closure(pairs, merge=merge, check=check,
                                       operations=operations))

    def combine(left, right, replacement):
        nonlocal mergers
        if operations is not None:
            operations.append({'op': 'merge', 'left': left, 'right': right})
        pairs[left] = replacement
        del pairs[right]
        mergers += 1

    while True:
        eligible = []
        remaining = enumerate(pairs)
        for index, row in remaining:
            check()
            if row.periodic:
                eligible.append(index)
                if len(eligible) == 2:
                    break
        if len(eligible) < 2:
            return finish()
        if spent == allowance:
            return fallback()
        check()
        left, right = eligible
        tests += 1
        spent += 1
        replacement = merge(pairs[left], pairs[right])
        if replacement is not None:
            combine(left, right, replacement)
            continue
        first = left, right
        for index, row in remaining:
            check()
            if row.periodic:
                eligible.append(index)
        scans += 1
        active, ends, candidates = set(), [], []
        for index in sorted(eligible, key=lambda i: (pairs[i].a, i)):
            check()
            row = pairs[index]
            while ends and ends[0][0] < row.a:
                check()
                _, expired = heappop(ends)
                active.remove(expired)
            for other in active:
                check()
                if spent == allowance:
                    return fallback()
                spent += 1
                overlaps += 1
                candidates.append((min(index, other), max(index, other)))
            active.add(index)
            heappush(ends, (row.d, index))
        found = False
        for left, right in sorted(candidates):
            check()
            if (left, right) == first:
                continue
            tests += 1
            replacement = merge(pairs[left], pairs[right])
            if replacement is not None:
                combine(left, right, replacement)
                found = True
                break
        if not found:
            return finish()


def hybrid_closure(pairings, *, merge, check=lambda: None, operations=None):
    """Use restart scans until their original all-pairs allowance is spent.

    With k original rows, at most binom(k, 2) ordinary candidate tests are
    done.  A further candidate triggers queue closure on the residual rows.
    Thus a no-merger scan and an easy run of first-pair mergers execute the
    historical candidate sequence without queue construction.  Every path
    has at most binom(k, 2) + max(k - 1, 0)**2 candidate tests, and uses at
    most O(k**2) queue memory.  The heap is absent when there is no switch.

    The allowance is a scheduling choice, not a mathematical cancellation
    budget.  It cannot produce an incomplete orbit calculation.
    The first two periodic rows are found lazily so an immediate merger
    need not rebuild the rest of the periodic index list before restarting.
    """
    check()
    pairs = list(pairings)
    allowance = len(pairs) * (len(pairs) - 1) // 2
    pair_tests = mergers = 0

    def finish_with_queue():
        queued = periodic_closure(pairs, merge=merge, check=check,
                                   operations=operations)
        return ClosureResult(
            queued.pairings, pair_tests + queued.pair_tests,
            mergers + queued.mergers, queued.peak_queue,
            queued.stale_pops, 1, queued.queue_runs)

    while True:
        eligible = []
        remaining = enumerate(pairs)
        for index, pair in remaining:
            check()
            if pair.periodic:
                eligible.append(index)
                if len(eligible) == 2:
                    break
        if len(eligible) < 2:
            return ClosureResult(pairs, pair_tests, mergers, 0, 0, 0)

        # The first candidate is already known.  Easy first-pair mergers
        # must not pay for rebuilding all later periodic indices each time.
        left, right = eligible
        check()
        if pair_tests == allowance:
            return finish_with_queue()
        pair_tests += 1
        replacement = merge(pairs[left], pairs[right])
        if replacement is not None:
            if operations is not None:
                operations.append({'op': 'merge', 'left': left, 'right': right})
            pairs[left] = replacement
            del pairs[right]
            mergers += 1
            continue

        for index, pair in remaining:
            check()
            if pair.periodic:
                eligible.append(index)
        found = False
        for offset, left in enumerate(eligible):
            check()
            # Resume the identical lexicographic sequence after its already
            # tested first candidate, without testing that failure twice.
            first_right = 2 if offset == 0 else offset + 1
            for right in eligible[first_right:]:
                check()
                if pair_tests == allowance:
                    return finish_with_queue()
                pair_tests += 1
                replacement = merge(pairs[left], pairs[right])
                if replacement is not None:
                    if operations is not None:
                        operations.append({'op': 'merge', 'left': left,
                                           'right': right})
                    pairs[left] = replacement
                    del pairs[right]
                    mergers += 1
                    found = True
                    break
            if found:
                break
        if not found:
            return ClosureResult(pairs, pair_tests, mergers, 0, 0, 0)


def restart_closure(pairings, *, merge, check=lambda: None, operations=None):
    """Literal historical merger scan, retained only as a research oracle."""
    pairs = list(pairings)
    pair_tests = mergers = 0
    while True:
        found = False
        for left in range(len(pairs)):
            check()
            if not pairs[left].periodic:
                continue
            for right in range(left + 1, len(pairs)):
                check()
                if not pairs[right].periodic:
                    continue
                pair_tests += 1
                replacement = merge(pairs[left], pairs[right])
                if replacement is not None:
                    if operations is not None:
                        operations.append({'op': 'merge', 'left': left,
                                           'right': right})
                    pairs[left] = replacement
                    del pairs[right]
                    mergers += 1
                    found = True
                    break
            if found:
                break
        if not found:
            return ClosureResult(pairs, pair_tests, mergers, 0, 0)
