"""A Boolean determinant sieve for exact forest-compatible row peeling.

Only the ordinary SCCs incident to non-inert columns of support greater
than two enter the state table.  Free SCCs are removed.  If the resulting
reachability poset has J ideals on d elements, discovery has J*poly(input
size) time and J*poly(input size) space; J <= 2**d and d <= 3k for k triples.

SUCCESS always has a producer-independent tree/peeling certificate.  A zero
randomized evaluation gives INCONCLUSIVE.  The input is a supplied finite
graph and unsigned matrix, not a knot diagram or an authenticated manifold.
"""

from random import Random, SystemRandom

from . import base
from .solver import (DEFAULT_PRIME, CoverageSieve, _bits, _forced_cover,
                     _prepare, _prime64)


def _closure_table(prepared, special, work, initial_masks=None):
    full = sum(1 << row for row in special)
    rules = [(sum(1 << row for row in rows), sum(1 << row for row in units))
             for _, rows, units in prepared["triples"]]
    values = []
    if initial_masks is None:
        initial_masks = range(1 << len(special))
    for mask in initial_masks:
        work.tick("closure_table_masks")
        known = prepared["known"]
        for index in _bits(mask):
            known |= prepared["reach"][special[index]]
        while True:
            previous = known
            for support, unit in rules:
                work.tick("nonlinear_rule_tests")
                missing = support & ~known
                if missing and missing & (missing - 1) == 0 and missing & unit:
                    row = missing.bit_length() - 1
                    known |= prepared["reach"][row]
            if known == previous:
                break
        values.append(int(known & full == full))
    return values


def _mobius_filter(values, work):
    r"""c[A] = sum_{B subset A} (-1)**|A\B| f(U\B), over the integers."""
    size = len(values)
    full = size - 1
    coefficients = [values[full ^ mask] for mask in range(size)]
    bit = 1
    while bit < size:
        for mask in range(size):
            if mask & bit:
                coefficients[mask] -= coefficients[mask ^ bit]
                work.tick("mobius_updates")
        bit <<= 1
    return coefficients


def _iter_ideal_masks(prepared, special, work, max_states=None):
    """Stream ideals in topological color order with O(d*J) DFS visits."""
    predecessors = []
    for index, row in enumerate(special):
        predecessors.append(sum(1 << previous for previous in range(index)
                                if prepared["ancestors"][row] & (1 << special[previous])))
    produced, stack = 0, [(0, 0)]
    while stack:
        index, mask = stack.pop()
        work.tick("ideal_prefixes")
        if index == len(special):
            produced += 1
            if max_states is not None and produced > max_states:
                raise base.BudgetExhausted("ideal-state limit exceeded")
            yield mask
            continue
        stack.append((index + 1, mask))
        if predecessors[index] & mask == predecessors[index]:
            stack.append((index + 1, mask | (1 << index)))


def _ideal_masks(prepared, special, work, max_states=None):
    return sorted(_iter_ideal_masks(prepared, special, work, max_states))


def _ideal_mobius(ideals, values, dimensions, work):
    """Invert subset sums on ideals; reverse topological order is essential."""
    position = {mask: index for index, mask in enumerate(ideals)}
    coefficients = list(values)
    for color in reversed(range(dimensions)):
        bit = 1 << color
        for index, mask in enumerate(ideals):
            work.tick("ideal_mobius_tests")
            if mask & bit and (mask ^ bit) in position:
                coefficients[index] -= coefficients[position[mask ^ bit]]
                work.tick("ideal_mobius_updates")
    return tuple(zip(ideals, coefficients))


def _special_state(data, work):
    prepared = _prepare(data, work, support_bound=None)
    original_special = sorted({row for _, rows, _ in prepared["triples"] for row in rows})
    # Ancestor sets coincide exactly within an ordinary SCC.  Ordering by
    # their cardinality gives a linear extension: strict reachability implies
    # strict ancestor inclusion.  Free SCCs require no activation coordinate.
    representatives = {}
    for row in original_special:
        if not prepared["known"] & (1 << row):
            representatives.setdefault(prepared["ancestors"][row], row)
    special = sorted(representatives.values(),
                     key=lambda row: (prepared["ancestors"][row].bit_count(), row))
    work.tick("exceptional_columns", len(prepared["triples"]))
    work.tick("special_rows", len(original_special))
    work.tick("table_bits", len(special))
    special_mask = sum(1 << row for row in original_special)
    mandatory = []
    for group in prepared["source_groups"]:
        mask = sum(1 << row for row in group)
        if not mask & special_mask:
            mandatory.append(mask & prepared["eligible"])
    return prepared, special, mandatory


def solve_boolean(problem, *, max_work=None, max_table_bits=None, max_states=None,
                  seed=None, prime=DEFAULT_PRIME, trials=1):
    """One-sided witness discovery in J*poly(N) <= 2**d poly(N), exact replay.

    The probability theorem assumes independent uniform field samples.
    ``seed`` is for reproducible experiments only.  The fixed 64-bit prime
    implementation requires prime > twice the eligible edge count; the
    unbounded mathematical algorithm chooses a suitable prime as input grows.
    A requested table/work limit returns INCONCLUSIVE, never a negative verdict.
    """
    data = base.normalize(problem)
    work = base.Work(max_work)
    if max_table_bits is not None and (type(max_table_bits) is not int
                                      or max_table_bits < 0):
        raise base.InvalidProblem("max_table_bits must be nonnegative or None")
    if type(trials) is not int or trials < 1:
        raise base.InvalidProblem("trials must be a positive integer")
    if max_states is not None and (type(max_states) is not int or max_states < 0):
        raise base.InvalidProblem("max_states must be nonnegative or None")
    if seed is not None and type(seed) is not int:
        raise base.InvalidProblem("seed must be an integer or None")
    if not _prime64(prime):
        raise base.InvalidProblem("prime must be prime and smaller than 2**64")
    method = "boolean_forest_sieve"
    try:
        failure = base._source_connectivity(data, work)
        if failure:
            return dict(status="NO_FOREST", method=method, certificate=failure,
                        stats=work.export())
        prepared, special, mandatory = _special_state(data, work)
        if max_table_bits is not None and len(special) > max_table_bits:
            return dict(status="INCONCLUSIVE", method=method,
                        reason="exceptional-row table limit exceeded", stats=work.export())
        # This exact feasibility precheck addresses the partition requirements
        # only.  Failure is sound; success still needs the nonlinear filter.
        candidate = _forced_cover(data, mandatory, (), work)
        if candidate is None:
            return dict(status="NO_FOREST", method=method, certificate=None,
                        evidence="deterministic mandatory-group matroid obstruction",
                        stats=work.export())
        schedule, residual = base._peel(data, set(range(len(data[3]))) - set(candidate), work)
        if not residual:
            return dict(status="SUCCESS", method=method,
                        certificate=dict(kind="success", tree=candidate, peeling=schedule),
                        stats=work.export())
        ideals = _ideal_masks(prepared, special, work, max_states)
        full = (1 << len(special)) - 1
        values = _closure_table(prepared, special, work,
                                (full ^ mask for mask in ideals))
        mask_coefficients = _ideal_mobius(ideals, values, len(special), work)
        requirements = tuple(prepared["ancestors"][row] & prepared["eligible"]
                             for row in special)
        work.tick("ideal_states", len(ideals))
        work.tick("nonzero_filter_coefficients",
                  sum(value != 0 for _, value in mask_coefficients))
        rng = SystemRandom() if seed is None else Random(seed)
        for _ in range(trials):
            work.tick("randomized_trials")
            sieve = CoverageSieve(data, mandatory, requirements, prime, rng, work,
                                  mask_coefficients=mask_coefficients)
            tree = sieve.tree()
            if tree is not None:
                certificate = base._positive(data, tree, work)
                return dict(status="SUCCESS", method=method, certificate=certificate,
                            stats=work.export())
        return dict(status="INCONCLUSIVE", method=method,
                    reason="zero Boolean-filter evaluations; no negative certificate",
                    uniform_random_failure_bound=dict(numerator=data[0] - 1,
                                                      denominator=prime, power=trials),
                    randomness="uniform system randomness" if seed is None else
                    "seeded reproducible experiment; probability theorem needs uniform samples",
                    stats=work.export())
    except base.BudgetExhausted as error:
        return dict(status="INCONCLUSIVE", method=method, reason=str(error),
                    stats=work.export())


def solve_width(problem, *, max_work=None, max_states=None):
    """Deterministic exact discovery in J*(m+1)**w*poly(N), polynomial space.

    Ideals and representative choices are streamed.  An exhaustive negative
    answer is an algorithmic conclusion; this implementation exports no
    portable negative certificate except for source disconnection.  Every
    success is checked against the original unsigned matrix.  A work/state
    limit returns INCONCLUSIVE.
    """
    data, work = base.normalize(problem), base.Work(max_work)
    method = "width_forest_search"
    if max_states is not None and (type(max_states) is not int or max_states < 0):
        raise base.InvalidProblem("max_states must be nonnegative or None")
    try:
        failure = base._source_connectivity(data, work)
        if failure:
            return dict(status="NO_FOREST", method=method, certificate=failure,
                        stats=work.export())
        prepared, special, mandatory = _special_state(data, work)
        candidate = _forced_cover(data, mandatory, (), work)
        if candidate is not None:
            schedule, residual = base._peel(data, set(range(len(data[3]))) - set(candidate), work)
            if not residual:
                return dict(status="SUCCESS", method=method,
                            certificate=dict(kind="success", tree=candidate, peeling=schedule),
                            stats=work.export())
            full = (1 << len(special)) - 1
            for ideal in _iter_ideal_masks(prepared, special, work, max_states):
                work.tick("ideal_states")
                hit = full ^ ideal
                if not _closure_table(prepared, special, work, (hit,))[0]:
                    continue
                minimum = [i for i in _bits(hit) if not any(
                    prepared["ancestors"][special[i]] & (1 << special[j])
                    for j in _bits(hit) if j != i)]
                work.tick("accepted_ideal_states")
                work.counts["largest_minimal_frontier"] = max(
                    work.counts.get("largest_minimal_frontier", 0), len(minimum))
                requirements = tuple(prepared["ancestors"][special[i]] & prepared["eligible"]
                                     for i in minimum)
                tree = _forced_cover(data, mandatory, requirements, work)
                if tree is not None:
                    return dict(status="SUCCESS", method=method,
                                certificate=base._positive(data, tree, work), stats=work.export())
        return dict(status="NO_FOREST", method=method, certificate=None,
                    evidence="mandatory-group obstruction or exhaustive ideal-state and representative search",
                    stats=work.export())
    except base.BudgetExhausted as error:
        return dict(status="INCONCLUSIVE", method=method, reason=str(error),
                    stats=work.export())


def main():
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("--seed", type=int)
    parser.add_argument("--max-work", type=int)
    parser.add_argument("--max-table-bits", type=int)
    parser.add_argument("--max-states", type=int)
    parser.add_argument("--trials", type=int, default=1)
    parser.add_argument("--deterministic-width", action="store_true")
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as stream:
        problem = json.load(stream)
    if args.deterministic_width:
        result = solve_width(problem, max_work=args.max_work, max_states=args.max_states)
    else:
        result = solve_boolean(problem, seed=args.seed, max_work=args.max_work,
                               max_table_bits=args.max_table_bits, max_states=args.max_states,
                               trials=args.trials)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
