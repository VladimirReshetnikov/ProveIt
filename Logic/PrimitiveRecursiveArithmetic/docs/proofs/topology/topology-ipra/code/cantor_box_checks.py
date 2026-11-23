"""Exact finite regressions for the Cantor and rational-box constructions."""
from fractions import Fraction as Q
from itertools import product


def eps(k):
    return Q(1, 2**k)


def clip(x):
    return min(Q(1), max(Q(0), x))


def cantor_interval(word):
    numerator = 0
    for bit in word:
        numerator = 3 * numerator + 2 * bit
    return Q(numerator, 3**len(word)), Q(numerator + 1, 3**len(word))


def interval_distance(q, interval):
    lo, hi = interval
    return max(0, lo - q, q - hi)


def check_decoder():
    count = 0
    for n in range(7):
        intervals = [(w, cantor_interval(w)) for w in product((0, 1), repeat=n)]
        for word, (lo, hi) in intervals:
            # Constant zero tail, constant one tail, periodic 0101... tail.
            for tail in (Q(0), Q(1), Q(1, 4)):
                x = lo + (hi - lo) * tail
                for noise in (-1, 0, 1):
                    sample = x + noise * eps(2 * n + 3)
                    decoded, actual_interval = min(
                        intervals, key=lambda item: interval_distance(sample, item[1]))
                    assert decoded == word and actual_interval == (lo, hi)
                    count += 1
    return count


def run_proposals(indices):
    points, accepted = [], []
    for k, index in enumerate(indices):
        denominator = 2**(k + 4)
        size = denominator + 1
        candidate = Q(index % size, denominator)
        use = k == 0 or abs(candidate - points[-1]) <= eps(k + 1)
        points.append(candidate if use else points[-1])
        accepted.append(use)
    return points, accepted


def check_surjection():
    stages = 7
    lifted_stages = 0
    for j in range(42):
        target = Q(j, 41)
        bits, offsets = [], [0]
        for k in range(stages):
            denominator = 2**(k + 4)
            sample = clip(target + (-1)**k * eps(k + 4))
            # Select the first net center within 1/denominator of the sample.
            scaled = sample * denominator - 1
            index = max(0, -(-scaled.numerator // scaled.denominator))
            assert abs(Q(index, denominator) - sample) <= eps(k + 4)
            size = denominator + 1
            bits.extend((index >> i) & 1 for i in range(size))
            offsets.append(len(bits))
        indices = [sum(bits[t] << (t - offsets[k])
                       for t in range(offsets[k], offsets[k + 1]))
                   for k in range(stages)]
        points, accepted = run_proposals(indices)
        assert all(accepted)
        for k, q in enumerate(points):
            assert abs(q - target) <= eps(k + 3)
            lifted_stages += 1

    # Independently vary proposals after common prefixes, including rejection.
    pair_count, saw_rejection = 0, False
    for i in range(25):
        original = [(i + 1) * (k + 1)**2 for k in range(stages)]
        left, left_flags = run_proposals(original)
        saw_rejection |= not all(left_flags)
        for k in range(stages):
            changed = original[:k + 1] + [1000 - 3 * t for t in range(k + 1, stages)]
            right, _ = run_proposals(changed)
            assert left[k] == right[k]
            assert abs(left[-1] - left[k]) <= eps(k + 1)
            assert abs(left[-1] - right[-1]) <= eps(k)
            pair_count += 1
    assert saw_rejection
    return lifted_stages, pair_count


def inside(box, point):
    return all(lo < x < hi for (lo, hi), x in zip(box, point))


def box_cover(dim, boxes):
    """Result is (missed point, None, None) or (None, radius, selector)."""
    assert all(len(box) == dim for box in boxes)
    if dim == 0:
        return (None, Q(1), lambda point: 0) if boxes else ((), None, None)
    valid = [(i, box) for i, box in enumerate(boxes)
             if all(lo < hi for lo, hi in box)]
    breaks, representatives = [], []
    for j in range(dim):
        values = sorted({Q(0), Q(1)} | {x for _, box in valid for x in box[j]})
        breaks.append(values)
        inner = [v for v in values if 0 <= v <= 1]
        representatives.append(inner + [(u + v) / 2 for u, v in zip(inner, inner[1:])])
    for point in product(*representatives):
        if not any(inside(box, point) for _, box in valid):
            return point, None, None
    delta = min(v - u for axis in breaks for u, v in zip(axis, axis[1:])) / 4

    def select(point):
        snapped = tuple(next((v for v in axis if abs(x - v) <= delta), x)
                        for x, axis in zip(point, breaks))
        assert all(0 <= x <= 1 for x in snapped)
        return next(i for i, box in valid if inside(box, snapped))
    return None, delta / 2, select


def check_boxes():
    # All subsets of this small family; the ground cases include open seams,
    # a missing endpoint, a degenerate entry and endpoints beyond the cube.
    intervals = [(Q(-1), Q(1, 2)), (Q(1, 2), Q(2)), (Q(1, 4), Q(3, 4)),
                 (Q(0), Q(2)), (Q(-1), Q(1)), (Q(1, 2), Q(1, 2))]
    cases = []
    for mask in range(1 << len(intervals)):
        chosen = [(iv,) for i, iv in enumerate(intervals) if mask & (1 << i)]
        # All possible membership changes occur at multiples of 1/4.
        expected = all(any(inside(box, (Q(k, 8),)) for box in chosen) for k in range(9))
        cases.append((1, chosen, expected))
    full = (Q(-1, 10), Q(101, 100))
    low, high = (Q(-1), Q(2, 3)), (Q(1, 3), Q(2))
    seam_low, seam_high = (Q(-1), Q(1, 2)), (Q(1, 2), Q(2))
    cases.extend([
        (0, [], False), (0, [()], True), (0, [(), ()], True),
        (2, [(full, low), (full, high)], True),
        (2, [(full, seam_low), (full, seam_high)], False),
        (2, [(low, low), (low, high), (high, low)], False),
        (2, [(low, low), (low, high), (high, low), (high, high)], True),
        (3, [(full, full, full)], True),
    ])
    selections = 0
    for dim, boxes, expected in cases:
        missed, radius, selector = box_cover(dim, boxes)
        assert (missed is None) == expected
        if not expected:
            assert all(not inside(box, missed) for box in boxes)
            continue
        for x in product((Q(0), Q(1, 3), Q(1, 2), Q(2, 3), Q(1)), repeat=dim):
            for noise in (-1, 0, 1):
                sample = tuple(clip(t + noise * radius / 4) for t in x)
                box = boxes[selector(sample)]
                # Check the whole relative ball by its coordinate extrema.
                assert all(lo < max(0, t - radius) and min(1, t + radius) < hi
                           for (lo, hi), t in zip(box, x))
                selections += 1
    return len(cases), selections


if __name__ == "__main__":
    decodings = check_decoder()
    lifts, perturbations = check_surjection()
    covers, selections = check_boxes()
    print(f"{decodings} Cantor decodings, {lifts} lifted stages, {perturbations} prefix comparisons, "
          f"{covers} box-cover decisions, {selections} neighborhood selections: all passed.")
