"""Independent small exact audits for the raw-singleton epoch theorem.

This deliberately does not import the maintained group implementation.
"""
from __future__ import annotations

import itertools
import json
import random
import time
from functools import lru_cache
from pathlib import Path


def permanent(a):
    n = len(a)
    return sum(
        prod(a[i][p[i]] for i in range(n))
        for p in itertools.permutations(range(n))
    )


def prod(xs):
    y = 1
    for x in xs:
        y *= x
    return y


def pivot(a, row, col):
    assert a[row][col] == 1
    return tuple(
        tuple(a[i][j] + a[i][col] * a[row][j]
              for j in range(len(a)) if j != col)
        for i in range(len(a)) if i != row
    )


@lru_cache(maxsize=None)
def has_complete_raw_epoch(a):
    if not a:
        return True
    return any(
        has_complete_raw_epoch(pivot(a, i, j))
        for i in range(len(a)) for j in range(len(a))
        if a[i][j] == 1
    )


def peel(a):
    """Return (original row, original column) dependencies-first matching."""
    rows = list(range(len(a)))
    cols = set(rows)
    trace = []
    while rows:
        found = None
        for i in rows:
            nonzero = [j for j in cols if a[i][j]]
            if len(nonzero) == 1 and a[i][nonzero[0]] == 1:
                found = i, nonzero[0]
                break
        if found is None:
            return None
        trace.append(found)
        rows.remove(found[0])
        cols.remove(found[1])
    return trace


def inv(w):
    return tuple(-x for x in reversed(w))


def subst(w, x, image):
    inverse = inv(image)
    return tuple(y for a in w for y in (image if a == x else
                 inverse if a == -x else (a,)))


def reduce(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def solve(w, x):
    where = [i for i, a in enumerate(w) if abs(a) == x]
    assert len(where) == 1
    i = where[0]
    left, right = w[:i], w[i + 1:]
    return inv(left) + inv(right) if w[i] == x else right + left


def old_epoch(words, selected_order):
    current = list(words)
    all_letters = {abs(x) for word in words for x in word}
    images = {x: (x,) for x in all_letters}
    for slot, x in selected_order:
        image = solve(current[slot], x)
        current = [() if j == slot else subst(w, x, image)
                   for j, w in enumerate(current)]
        images = {g: subst(w, x, image) for g, w in images.items()}
        if max(map(len, images.values()), default=0) > 100_000:
            return None
    return current, images


def flatten(words, slots, eliminated):
    matrix = tuple(tuple(sum(abs(a) == x for a in words[j])
                         for x in eliminated) for j in slots)
    order = peel(matrix)
    assert order is not None
    images = {abs(x): (abs(x),) for w in words for x in w}
    for local_slot, local_x in order:
        x = eliminated[local_x]
        word = solve(words[slots[local_slot]], x)
        for y, image in images.items():
            if y != x:
                word = subst(word, y, image)
        images[x] = word
    out = []
    for j, word in enumerate(words):
        if j in slots:
            out.append(())
            continue
        for x in eliminated:
            word = subst(word, x, images[x])
        out.append(word)
    return out, images, [(slots[i], eliminated[j]) for i, j in order]


def audit_matrices():
    records = []
    for n, alphabet in [(1, range(3)), (2, range(3)),
                        (3, range(3)), (4, range(2))]:
        count = unique = successful = 0
        for entries in itertools.product(alphabet, repeat=n*n):
            a = tuple(tuple(entries[i*n:(i+1)*n]) for i in range(n))
            p = permanent(a)
            possible = has_complete_raw_epoch(a)
            peeling = peel(a) is not None
            assert possible == (p == 1) == peeling, (a, p, possible, peeling)
            # Every reverse step with a uniquely matched residual must also
            # have an original matrix with permanent one.
            for i in range(n):
                for j in range(n):
                    if a[i][j] == 1:
                        b = pivot(a, i, j)
                        if permanent(b) == 1:
                            assert p == 1
            count += 1
            unique += p == 1
            successful += possible
        records.append(dict(n=n, alphabet=list(alphabet), count=count,
                            unique_permanent=unique, successful=successful))
    return records


def audit_signed_words(seed=92763, trials=2000):
    rng = random.Random(seed)
    completed = compared = reordered = spelling_differences = 0
    for _ in range(trials):
        k = rng.randrange(1, 6)
        survivors = [k+1, k+2]
        words = []
        # A triangular source with one occurrence of its matched variable;
        # repeat earlier dependencies and survivor letters arbitrarily.
        for x in range(1, k+1):
            support = list(range(1, x)) + survivors
            left = tuple(rng.choice(support) * rng.choice([-1, 1])
                         for _ in range(rng.randrange(4)))
            right = tuple(rng.choice(support) * rng.choice([-1, 1])
                          for _ in range(rng.randrange(4)))
            words.append(left + (x * rng.choice([-1, 1]),) + right)
        words += [tuple(rng.randrange(1, k+3) * rng.choice([-1, 1])
                        for _ in range(rng.randrange(1, 9)))
                  for _ in range(2)]
        current = list(words)
        unused = set(range(k))
        unknown = set(range(1, k+1))
        sequence = []
        while unused:
            choices = [(j, x) for j in unused for x in unknown
                       if sum(abs(a) == x for a in current[j]) == 1]
            if not choices:
                break
            j, x = rng.choice(choices)
            image = solve(current[j], x)
            current = [() if z == j else subst(w, x, image)
                       for z, w in enumerate(current)]
            unused.remove(j)
            unknown.remove(x)
            sequence.append((j, x))
            if max(map(len, current)) > 50_000:
                break
        if unused or unknown:
            continue
        completed += 1
        sequential = old_epoch(words, sequence)
        if sequential is None:
            continue
        flat_words, flat_images, order = flatten(words, list(range(k)),
                                               list(range(1, k+1)))
        seq_words, seq_images = sequential
        assert [reduce(w) for w in flat_words] == [reduce(w) for w in seq_words]
        assert {x: reduce(w) for x, w in flat_images.items()} == {
            x: reduce(w) for x, w in seq_images.items()}
        compared += 1
        reordered += set(sequence) != set(order)
        spelling_differences += flat_words != seq_words
    return dict(seed=seed, trials=trials, completed=completed,
                compared=compared, donor_reassignments=reordered,
                unequal_raw_spelling=spelling_differences)


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        'results' / 'raw_epoch_audit.json')
    args = parser.parse_args()
    start = time.perf_counter()
    matrices = audit_matrices()
    words = audit_signed_words()
    result = dict(matrix_exhaustion=matrices, signed_words=words,
                  elapsed_seconds=time.perf_counter()-start)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
