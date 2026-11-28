#!/usr/bin/env python3
"""Check two-sided isolation of finite Egyptian prefixes in exact arithmetic.

A witness may have fewer terms, or repeated denominators. No denominator cutoff
is imposed. Run without arguments to reproduce the experiments in the report.
"""
from fractions import Fraction as F
from itertools import product
import json


def ceil(x):
    return -(-x.numerator // x.denominator)


def total(word):
    return sum((F(1, n) for n in word), F(0))


def witness(word, lo, hi, include_lo, include_hi):
    """Find a different nondecreasing list of at most len(word) in the interval."""
    def visit(prefix, partial):
        valid_low = partial > lo or (include_lo and partial == lo)
        valid_high = partial < hi or (include_hi and partial == hi)
        if valid_low and valid_high and prefix != word:
            return prefix
        slots = len(word) - len(prefix)
        if slots == 0 or partial >= hi:
            return None
        # To remain below hi, the next denominator must be at least this big.
        threshold = 1 / (hi - partial)
        first = ceil(threshold) if include_hi else int(threshold) + 1
        first = max(first, prefix[-1] if prefix else 1)
        if partial >= lo:
            # A further term can be arbitrarily small. At most one denominator
            # could create the excluded word, so the next integer suffices.
            for n in (first, first + 1):
                enlarged = prefix + (n,)
                if enlarged != word:
                    return enlarged
            raise AssertionError("Two distinct candidates cannot equal one word.")
        # At most 'slots' remaining terms, all at most 1/n: reaching lo
        # forces n <= slots/(lo - partial), strictly if the left end is open.
        threshold = slots / (lo - partial)
        last = int(threshold) if include_lo else ceil(threshold) - 1
        for n in range(first, last + 1):
            found = visit(prefix + (n,), partial + F(1, n))
            if found is not None:
                return found
        return None

    answer = visit((), F(0))
    if answer is not None:
        s = total(answer)
        assert answer != word and len(answer) <= len(word)
        assert s > lo or (include_lo and s == lo)
        assert s < hi or (include_hi and s == hi)
    return answer


def isolation(word, scale):
    s = total(word)
    h = F(1, 32 * scale ** 2)
    return {
        "below": witness(word, s-h, s, True, False),
        "equal": witness(word, s, s, True, True),
        "above": witness(word, s, s+h, False, True),
    }


def inspect(scales, digits):
    counts = {"below": 0, "equal": 0, "above": 0}
    examples = {}
    isolated = examined = 0
    for word in product(*digits):
        examined += 1
        rivals = isolation(word, scales[-1])
        if all(q is None for q in rivals.values()):
            isolated += 1
        for side, q in rivals.items():
            if q is None:
                continue
            counts[side] += 1
            example = {"word": word, "rival": q, "rival_minus_word": str(total(q)-total(word))}
            examples.setdefault(side, example)
            if len(q) != len(set(q)):
                examples.setdefault("repeated_denominator", example)
    return {"scales": scales, "examined": examined, "isolated_at_last_order": isolated,
            "rival_counts_by_side": counts, "examples": examples}


def main():
    # Direct checks include the two strict directions, an exact tie, and a
    # repeated-denominator competitor.
    assert witness((3, 8), F(1, 2), F(1, 2), True, True) is not None
    assert witness((4, 12), F(1, 3), F(1, 3), True, True) is not None
    assert witness((3, 15), F(2, 5), F(2, 5), True, True) == (5, 5)
    scales = (4, 42, 360)
    results = [inspect(scales[:m], [range(4, 8), range(42, 50), range(360, 384)][:m])
               for m in (1, 2, 3)]
    results.append(inspect((4, 42, 9216), [range(4, 8), range(42, 46), range(9216, 9220)]))
    # Two levels on the exact integer schedule in Section 6 of the manuscript.
    large = 256**6 * 8**2
    results.append(inspect((8, large), [range(8, 16), range(large, large + 20)]))
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
