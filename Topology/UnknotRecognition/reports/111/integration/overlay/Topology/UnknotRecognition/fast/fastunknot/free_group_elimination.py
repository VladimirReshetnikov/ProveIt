"""Small, nonincreasing Tietze certificates of freeness.

This module proves a group is free.  It does not interpret word cancellation
as a geometric handle move.  The source-cut wrapper supplies the separate
topological and Euler-characteristic hypotheses needed for handlebodies.
"""

from collections import Counter
from hashlib import sha256
import json


def _presentation(generators, relators):
    if type(generators) is not list or type(relators) is not list:
        raise ValueError('generators and relators must be lists')
    if any(type(g) is not int or g <= 0 for g in generators):
        raise ValueError('generator labels must be positive integers')
    if len(set(generators)) != len(generators):
        raise ValueError('duplicate generator label')
    alphabet = set(generators)
    rows = {}
    for row in relators:
        if type(row) is not dict or type(row.get('id')) is not int or row['id'] < 0:
            raise ValueError('invalid relator label')
        word = row.get('word')
        if type(word) is not list or any(type(x) is not int or abs(x) not in alphabet
                                         for x in word):
            raise ValueError('invalid signed relator word')
        if row['id'] in rows:
            raise ValueError('duplicate relator label')
        rows[row['id']] = tuple(word)
    original = dict(generators=sorted(generators),
                    relators=[dict(id=r, word=list(rows[r])) for r in sorted(rows)])
    digest = sha256(json.dumps(original, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return alphabet, rows, digest


def cyclic_reduce(word, *, check=lambda: None):
    """Freely reduce, then remove inverse letters at the two cyclic ends."""
    stack = []
    for letter in word:
        check()
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    lo, hi = 0, len(stack)
    while lo < hi and stack[lo] == -stack[hi - 1]:
        check()
        lo += 1
        hi -= 1
    return tuple(stack[lo:hi])


def _normalise(rows, check):
    current, dropped = {}, []
    for r in sorted(rows):
        word = cyclic_reduce(rows[r], check=check)
        if word:
            current[r] = word
        else:
            dropped.append(r)
    return current, dropped


def _substitution(word, generator):
    positions = [i for i, x in enumerate(word) if abs(x) == generator]
    if len(positions) != 1:
        raise ValueError('pivot generator is not a singleton in its relator')
    index = positions[0]
    tail = word[index + 1:] + word[:index]
    return tuple(-x for x in reversed(tail)) if word[index] > 0 else tail


def _trial(rows, row_id, generator, check):
    image = _substitution(rows[row_id], generator)
    inverse = tuple(-x for x in reversed(image))
    result, dropped, visits = {}, [], 0
    for r, word in rows.items():
        check()
        if r == row_id:
            continue

        def letters():
            nonlocal visits
            for x in word:
                replacement = image if x == generator else inverse if x == -generator else (x,)
                for y in replacement:
                    visits += 1
                    yield y

        reduced = cyclic_reduce(letters(), check=check)
        if reduced:
            result[r] = reduced
        else:
            dropped.append(r)
    return result, dropped, visits


def certify_free_group(generators, relators, *, check=lambda: None):
    """Try a deterministic polynomial policy and return COMPLETE/INCONCLUSIVE.

    Initially trivial relators are deleted.  A column private to one relator
    is preferred.  Otherwise all current singleton generator/relator pairs
    are tried, and a pair with minimum resulting total cyclically reduced
    length is accepted only when that length does not increase.  Ties use
    relator then generator labels.  There is no backtracking or completeness
    claim for this policy.  At most one generator disappears per pivot, and
    no accepted state exceeds the initial reduced total length.
    """
    check()
    alive, source, digest = _presentation(generators, relators)
    rows, dropped = _normalise(source, check)
    length = sum(map(len, rows.values()))
    initial_length = length
    moves, lengths = [], [length]
    stats = dict(initial_generators=len(alive), initial_relators=len(source),
                 source_word_length=sum(map(len, source.values())),
                 initial_reduced_length=length, peak_accepted_length=length,
                 candidate_trials=0, trial_letter_visits=0, private_pivots=0,
                 substitution_pivots=0, trivial_relators=len(dropped))
    while rows:
        check()
        total, singles = Counter(), []
        for r, word in rows.items():
            counts = Counter(map(abs, word))
            total.update(counts)
            singles.extend((r, g) for g, n in counts.items() if n == 1)
        private = [(r, g) for r, g in singles if total[g] == 1]
        if private:
            r, g = min(private)
            next_rows = dict(rows)
            del next_rows[r]
            newly_dropped = []
            next_length = length - len(rows[r])
            stats['private_pivots'] += 1
        else:
            best = None
            for r, g in sorted(singles):
                check()
                candidate, removed, visits = _trial(rows, r, g, check)
                stats['candidate_trials'] += 1
                stats['trial_letter_visits'] += visits
                new_length = sum(map(len, candidate.values()))
                score = (new_length, r, g)
                if new_length <= length and (best is None or score < best[0]):
                    best = score, candidate, removed
            if best is None:
                stats.update(final_generators=len(alive), final_relators=len(rows),
                             final_length=length, pivots=len(moves),
                             trivial_relators=len(dropped))
                return dict(status='INCONCLUSIVE', reason='no_nonincreasing_singleton',
                            remaining_generators=sorted(alive),
                            remaining_relators=[dict(id=r, word=list(w)) for r, w in rows.items()],
                            stats=stats)
            (next_length, r, g), next_rows, newly_dropped = best
            stats['substitution_pivots'] += 1
        alive.remove(g)
        moves.append([r, g])
        dropped.extend(newly_dropped)
        rows, length = next_rows, next_length
        lengths.append(length)
    stats.update(final_generators=len(alive), final_relators=0, final_length=0,
                 pivots=len(moves), trivial_relators=len(dropped))
    proof = dict(schema='free-presentation-elimination-v1', presentation_sha256=digest,
                 policy='nonincreasing', moves=moves, free_generators=sorted(alive),
                 free_rank=len(alive), trivial_relators=sorted(dropped),
                 initial_reduced_length=initial_length)
    return dict(status='COMPLETE', free_rank=len(alive), certificate=proof,
                accepted_lengths=lengths, stats=stats)
