"""Exact finite checks of the flow and local-dispersion arguments.

Python 3 standard library. Every location and cost used in the checks is integral.
"""
from itertools import product
from statistics import median_low


def sequence_cost(left, right, penalty):
    """Noncrossing matching by a sequence alignment. Absolute cost is Monge."""
    previous = [penalty * j for j in range(len(right) + 1)]
    for i, x in enumerate(left, 1):
        current = [penalty * i]
        for j, y in enumerate(right, 1):
            current.append(min(previous[j] + penalty,
                               current[-1] + penalty,
                               previous[j - 1] + abs(x - y)))
        previous = current
    return previous[-1]


def unmatched_or_paired(left, right, penalty):
    """Unrestricted subset DP, with no order imposed on the partners."""
    states = {0: 0}
    for x in left:
        updated = {}
        for mask, cost in states.items():
            updated[mask] = min(updated.get(mask, float("inf")), cost + penalty)
            for j, y in enumerate(right):
                bit = 1 << j
                if mask & bit:
                    continue
                nxt = mask | bit
                updated[nxt] = min(updated.get(nxt, float("inf")), cost + abs(x - y))
        states = updated
    return min(cost + penalty * (len(right) - mask.bit_count())
               for mask, cost in states.items())


def path_cost(counts, locations, penalty, monotone=False):
    """Minimize integral |F-g| plus penalty times variation on the path."""
    total = sum(counts)
    first = last = cumulative = 0
    for count in counts:
        cumulative += count
        first = min(first, cumulative)
        last = max(last, cumulative)
    levels = range(first, last + 1)
    direction = 1 if total >= 0 else -1
    costs = {0: 0}
    cumulative = 0
    for i in range(len(locations) - 1):
        cumulative += counts[i]
        width = locations[i + 1] - locations[i]
        next_costs = {}
        for g in levels:
            options = [v + penalty * abs(g - old)
                       for old, v in costs.items()
                       if not monotone or (g - old) * direction >= 0]
            if options:
                next_costs[g] = min(options) + width * abs(cumulative - g)
        costs = next_costs
    return min(v + penalty * abs(total - g) for g, v in costs.items()
               if not monotone or (total - g) * direction >= 0)


def lower_bound(left, right, penalty, mesh, offset):
    """Median oscillations on complete, disjoint blocks in [0,10]."""
    value = (penalty - mesh) * abs(len(left) - len(right))
    for start in range(offset, 11 - mesh, mesh):
        samples = [sum(y <= x for y in left) - sum(y <= x for y in right)
                   for x in range(start, start + mesh)]
        center = median_low(samples)
        value += sum(abs(x - center) for x in samples)
    return value


def main():
    locations = (1, 3, 6, 10)
    list_pairs = matching_checks = median_checks = 0
    for counts in product(range(-2, 3), repeat=len(locations)):
        left = [x for x, n in zip(locations, counts) for _ in range(max(0, n))]
        right = [x for x, n in zip(locations, counts) for _ in range(max(0, -n))]
        list_pairs += 1
        excess = abs(len(left) - len(right))
        # Price 20 exceeds all distances, so it forces maximum cardinality.
        full_distance = sequence_cost(left, right, 20) - 20 * excess
        assert path_cost(counts, locations, 0, monotone=True) == full_distance
        for price in (1, 2, 3, 5, 20):
            expected = unmatched_or_paired(left, right, price)
            assert sequence_cost(left, right, price) == expected
            assert path_cost(counts, locations, price) == expected
            matching_checks += 1
            for mesh in range(1, min(price, 5) + 1):
                for offset in range(mesh):
                    assert lower_bound(left, right, price, mesh, offset) <= expected
                    median_checks += 1
        # Common occurrences cancel in the metric, even if other matches cross them.
        assert sequence_cost(sorted(left + [3]), sorted(right + [3]), 2) == sequence_cost(left, right, 2)
    print(f"Signed four-site configurations with multiplicity: {list_pairs}")
    print(f"Unrestricted matching, ordered matching, and integral flow agree: {matching_checks}")
    print(f"Maximum-cardinality displacement agrees with monotone flow: {list_pairs}")
    print(f"Local median lower bounds verified: {median_checks}")
    print("All exact checks passed.")


if __name__ == "__main__":
    main()
