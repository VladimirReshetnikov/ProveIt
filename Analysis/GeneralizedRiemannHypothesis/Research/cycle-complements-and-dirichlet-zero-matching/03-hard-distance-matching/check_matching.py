"""Exhaustive finite checks for the two deterministic matching inequalities.

All lists are multisets, all distances are integers. No L-function computation
or probabilistic assumption enters this test. Run with Python 3.10 or later.
"""

from itertools import combinations_with_replacement, product


def greedy_matching(left, right, allowance):
    """Maximum number of pairs for sorted lists and a hard distance cap."""
    if allowance < 0:
        raise ValueError("allowance must be nonnegative")
    i = j = 0
    pairs = []
    while i < len(left) and j < len(right):
        if right[j] - left[i] > allowance:
            i += 1
        elif left[i] - right[j] > allowance:
            j += 1
        else:
            pairs.append((i, j))
            i += 1
            j += 1
    return pairs


def matching_by_augmentation(left, right, allowance):
    """Independent maximum bipartite matching; no order restriction."""
    partner = [-1] * len(right)

    def augment(i, visited):
        for j, value in enumerate(right):
            if j in visited or abs(left[i] - value) > allowance:
                continue
            visited.add(j)
            if partner[j] == -1 or augment(partner[j], visited):
                partner[j] = i
                return True
        return False

    return sum(augment(i, set()) for i in range(len(left)))


def count_in_window(values, start, end):
    return sum(start < value <= end for value in values)


def check_window_inequalities(left, right, allowance, pairs, width):
    """Integrate exactly: each step function is constant at integer starts
    on [k,k+1), apart from endpoint conventions of measure zero."""
    discarded = len(left) + len(right) - 2 * len(pairs)
    symmetric_difference = 0
    expanded_deficit = 0
    for start in range(-width - allowance, 5 + allowance):
        end = start + width
        a = count_in_window(left, start, end)
        b = count_in_window(right, start, end)
        a_expanded = count_in_window(left, start - allowance, end + allowance)
        b_expanded = count_in_window(right, start - allowance, end + allowance)
        symmetric_difference += abs(a - b)
        expanded_deficit += max(0, a - b_expanded) + max(0, b - a_expanded)
    move_cost = sum(min(width, abs(left[i] - right[j])) for i, j in pairs)
    assert symmetric_difference <= width * discarded + 2 * move_cost
    assert expanded_deficit <= width * discarded


def main():
    lists = [
        values
        for size in range(4)
        for values in combinations_with_replacement(range(5), size)
    ]
    instances = 0
    inequalities = 0
    for left, right, allowance in product(lists, lists, range(5)):
        pairs = greedy_matching(left, right, allowance)
        assert len(pairs) == matching_by_augmentation(left, right, allowance)
        for width in range(1, 5):
            check_window_inequalities(left, right, allowance, pairs, width)
            inequalities += 2
        instances += 1
    print(f"Multisets in each list family: {len(lists)}")
    print(f"Optimal match counts checked by bipartite augmentation: {instances}")
    print(f"Exact integrated window inequalities checked: {inequalities}")
    print("All checks passed.")


if __name__ == "__main__":
    main()
