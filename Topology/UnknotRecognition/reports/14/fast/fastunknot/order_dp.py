"""Exact bounded-window optimization of a crossing scan order.

Each subset of a fixed window has a uniquely determined frontier.  Two passes
over its subset lattice first minimize the *global* peak, then minimize an
additive frontier cost subject to that optimum.  A single lexicographic label
per subset would be incorrect: a later peak can erase an earlier advantage.

This optimizes a combinatorial proxy for scanner work, not scanner runtime.
The returned order is always a permutation; unchanged outside frontier sets
make every accepted replacement improve the selected global objective.
"""
from __future__ import annotations

from time import monotonic

from .geometry import ScanLimit
from .ordering import _graph, best_scan_order, validate_order


def frontier_sizes(pd, order):
    boundary = set()
    result = []
    for crossing in order:
        for edge in pd[crossing]:
            if edge in boundary:
                boundary.remove(edge)
            else:
                boundary.add(edge)
        result.append(len(boundary))
    return result


def _cost(width, objective):
    return width if objective == "sum" else 1 << (width // 2)


def _score(widths, objective):
    return max(widths, default=0), sum(_cost(w, objective) for w in widths)


def _validate_objective(objective):
    if objective not in ("sum", "mass"):
        raise ValueError("objective must be 'sum' or 'mass'")


def _window(pd, order, start, stop, objective, check):
    block = order[start:stop]
    k = len(block)
    widths_before = frontier_sizes(pd, order)
    outside_peak = max(widths_before[:start] + widths_before[stop:], default=0)
    boundary = set()
    for crossing in order[:start]:
        for edge in pd[crossing]:
            if edge in boundary:
                boundary.remove(edge)
            else:
                boundary.add(edge)
    labels = {edge for crossing in block for edge in pd[crossing]}
    edge_index = {edge: i for i, edge in enumerate(sorted(labels))}
    fixed = len(boundary - labels)
    local = sum(1 << edge_index[e] for e in boundary & labels)
    toggles = []
    for crossing in block:
        mask = 0
        for edge in pd[crossing]:
            mask ^= 1 << edge_index[edge]
        toggles.append(mask)

    count = 1 << k
    masks, widths = [0] * count, [0] * count
    widths[0] = fixed + local.bit_count()
    minimax = [None] * count
    minimax[0] = outside_peak
    for subset in range(1, count):
        if subset & 255 == 0:
            check()
        low = subset & -subset
        masks[subset] = masks[subset ^ low] ^ toggles[low.bit_length() - 1]
        width = widths[subset] = fixed + (local ^ masks[subset]).bit_count()
        options = subset
        best = None
        while options:
            last = options & -options
            previous = minimax[subset ^ last]
            candidate = max(previous, width)
            best = candidate if best is None else min(best, candidate)
            options ^= last
        minimax[subset] = best
    optimal_peak = minimax[-1]

    distance, parent = [None] * count, [-1] * count
    distance[0] = 0
    for subset in range(1, count):
        if subset & 255 == 0:
            check()
        width = widths[subset]
        if width > optimal_peak:
            continue
        options = subset
        best = None
        while options:
            last = options & -options
            previous = distance[subset ^ last]
            if previous is not None:
                candidate = previous + _cost(width, objective)
                if best is None or candidate < best:
                    best, parent[subset] = candidate, last.bit_length() - 1
            options ^= last
        distance[subset] = best

    subset, chosen = count - 1, []
    while subset:
        j = parent[subset]
        if j < 0:
            raise ArithmeticError("minimax-feasible subset path was not reconstructed")
        chosen.append(block[j])
        subset ^= 1 << j
    chosen.reverse()
    candidate = order[:start] + chosen + order[stop:]
    old_score = _score(widths_before, objective)
    new_score = _score(frontier_sizes(pd, candidate), objective)
    if new_score > old_score:
        raise ArithmeticError("exact window optimizer worsened the global objective")
    changed = new_score < old_score
    return (candidate if changed else list(order)), {
        "start": start, "stop": stop, "states": count,
        "old_score": old_score, "new_score": new_score,
        "changed": changed, "optimal_peak": optimal_peak,
    }


def optimize_window(pd, order, start, stop, *, objective="mass", check=lambda: None):
    """Globally optimal (peak, cost) with only order[start:stop] permutable.

    'sum' uses sum(frontier width); 'mass' uses sum(2**(width//2)).
    The second is motivated by a morphism basis dimension, without claiming
    it bounds or predicts the complete scanner's cost.
    """
    pd = [tuple(row) for row in pd]
    _graph(pd)
    order = validate_order(len(pd), order)
    _validate_objective(objective)
    if not (type(start) is int and type(stop) is int and 0 <= start < stop <= len(pd)):
        raise ValueError("invalid nonempty window")
    check()
    return _window(pd, order, start, stop, objective, check)


def improve_scan_order(pd, *, order=None, window=10, stride=None, passes=2,
                       objective="mass", seconds=None):
    """Apply exact overlapping windows, retaining the best completed order.

    The budget covers optimization after the initial order is supplied or
    constructed.  Exhaustion returns that best order with complete=False.
    The window length is explicit because memory is exponential in it.
    """
    pd = [tuple(row) for row in pd]
    _graph(pd)
    _validate_objective(objective)
    n = len(pd)
    if type(window) is not int or window < 1:
        raise ValueError("window must be a positive integer")
    if type(passes) is not int or passes < 0:
        raise ValueError("passes must be a nonnegative integer")
    if stride is None:
        stride = max(1, window // 2)
    if type(stride) is not int or stride < 1:
        raise ValueError("stride must be a positive integer")
    if seconds is not None and seconds < 0:
        raise ValueError("seconds must be nonnegative")
    order = (best_scan_order(pd, tries=min(n, 12)) if order is None
             else validate_order(n, order))
    initial = list(order)
    started = monotonic()
    deadline = None if seconds is None else started + seconds

    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("scan-order optimization time budget exhausted")

    history, complete = [], True
    width = min(window, n)
    starts = sorted(set(range(0, max(0, n - width) + 1, stride)) | {max(0, n - width)})
    try:
        if n > 1:
            for iteration in range(passes):
                improved = False
                for start in starts if iteration % 2 == 0 else reversed(starts):
                    check()
                    order, record = _window(pd, order, start, start + width, objective, check)
                    record["pass"] = iteration
                    history.append(record)
                    improved |= record["changed"]
                if not improved:
                    break
    except ScanLimit:
        complete = False
    return {
        "order": order, "initial_order": initial,
        "initial_score": _score(frontier_sizes(pd, initial), objective),
        "score": _score(frontier_sizes(pd, order), objective),
        "objective": objective, "window": window, "passes": passes,
        "windows": history, "complete": complete,
        "seconds": monotonic() - started,
    }
