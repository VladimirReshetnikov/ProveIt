"""Finite checks for the two hook formulas and permutation insertion."""

from collections import Counter
from functools import cache
from itertools import permutations
from math import comb, factorial, prod


def shapes(size, bound):
    if not size:
        yield ()
    for first in range(1, min(size, bound) + 1):
        for tail in shapes(size - first, first):
            yield (first,) + tail


def hooks(shape):
    return [w - j + sum(t > j for t in shape[i + 1:])
            for i, w in enumerate(shape) for j in range(w)]


@cache
def standard(shape):
    if not shape:
        return 1
    result = 0
    for i, w in enumerate(shape):
        if i + 1 == len(shape) or w > shape[i + 1]:
            reduced = list(shape)
            reduced[i] -= 1
            result += standard(tuple(v for v in reduced if v))
    return result


def semistandard(shape, alphabet):
    cells = [(i, j) for i, w in enumerate(shape) for j in range(w)]
    index = {cell: k for k, cell in enumerate(cells)}
    values = [0] * len(cells)

    def fill(k):
        if k == len(cells):
            return 1
        i, j = cells[k]
        minimum = max(1, values[k - 1] if j else 1,
                      values[index[(i - 1, j)]] + 1 if i else 1)
        count = 0
        for choice in range(minimum, alphabet + 1):
            values[k] = choice
            count += fill(k + 1)
        return count

    return fill(0)


def insert(word):
    insertion, recording = [], []
    for time, label in enumerate(word, 1):
        for row_index, row in enumerate(insertion):
            slot = next((j for j, other in enumerate(row) if other > label), len(row))
            if slot == len(row):
                row.append(label)
                recording[row_index].append(time)
                break
            row[slot], label = label, row[slot]
        else:
            insertion.append([label])
            recording.append([time])
    return insertion, recording


def reverse(insertion, recording):
    insertion = [row[:] for row in insertion]
    recording = [row[:] for row in recording]
    word = []
    for time in range(sum(map(len, recording)), 0, -1):
        i = next(i for i, row in enumerate(recording) if row and row[-1] == time)
        recording[i].pop()
        carry = insertion[i].pop()
        for row in reversed(insertion[:i]):
            j = max(j for j, v in enumerate(row) if v < carry)
            row[j], carry = carry, row[j]
        word.append(carry)
    return tuple(reversed(word))


def longest_increasing(word):
    best = []
    for i, a in enumerate(word):
        best.append(1 + max((best[j] for j in range(i) if word[j] < a), default=0))
    return max(best, default=0)


def main():
    for n in range(16):
        rows = list(shapes(n, n))
        assert all(standard(s) * prod(hooks(s)) == factorial(n) for s in rows)
        assert sum(standard(s) ** 2 for s in rows) == factorial(n)
    for n in range(8):
        for shape in shapes(n, n):
            for alphabet in range(len(shape), 6):
                contents = [alphabet + j - i for i, w in enumerate(shape) for j in range(w)]
                assert semistandard(shape, alphabet) * prod(hooks(shape)) == prod(contents)
    assert standard((5, 4, 1)) == 288
    assert semistandard((5, 4, 1), 7) == 66528
    for n in range(8):
        observed = Counter()
        for word in permutations(range(1, n + 1)):
            p, q = insert(word)
            assert reverse(p, q) == word
            shape = tuple(map(len, p))
            assert shape == tuple(map(len, q))
            assert (shape[0] if shape else 0) == longest_increasing(word)
            observed[shape] += 1
        assert all(observed[s] == standard(s) ** 2 for s in shapes(n, n))
        avoid = sum(count for shape, count in observed.items() if not shape or shape[0] <= 2)
        assert avoid * (n + 1) == comb(2 * n, n)
    print("Passed hook, content, insertion, reverse, subsequence and avoidance checks.")


if __name__ == "__main__":
    main()
