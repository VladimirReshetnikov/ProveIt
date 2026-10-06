#!/usr/bin/env python3
"""Construct and audit every critical zero-height profile for a=2,...,9.

A profile is a positive integer Laurent polynomial with coefficient sum a
whose support is a consecutive interval containing -1 and 0. Its realization
is a word starting in 1, with a zeros and a-1 ones.

Construction: on the integer line, put c_h up-edges h -> h+1 and
c_h - 1_{h=0} down-edges h+1 -> h. Prescribe the first down-edge 0 -> -1
by removing it. Every up-edge remains, so the underlying graph stays
connected. The remaining outdegree minus indegree is +1 at -1, -1 at 1,
and zero elsewhere. The directed Euler-trail criterion therefore gives
a trail from -1 to 1. Prepending the removed edge yields the desired word.

The independent finite audit also enumerates all words with the required
letter counts and compares their profile set with the proposed class.
Only Python's standard library is required. Run from any working directory:
    python code/verify_profile_realization.py
The recorded JSON is written relative to this script, under ../data/.
"""

from collections import Counter, defaultdict
from itertools import combinations
from math import comb
from pathlib import Path
import json


def positive_compositions(total, parts):
    """Yield all ordered compositions of total into positive parts."""
    if parts == 1:
        yield (total,)
        return
    for first in range(1, total - parts + 2):
        for tail in positive_compositions(total - first, parts - 1):
            yield (first,) + tail


def admissible_profiles(a):
    """Yield canonical tuples (height, multiplicity), with no duplicates."""
    for size in range(2, a + 1):
        for low in range(1 - size, 0):
            for coefficients in positive_compositions(a, size):
                yield tuple((low + j, c) for j, c in enumerate(coefficients))


def zero_height_profile(word):
    """Compute heights just before zeros, giving zeros weight +1."""
    height = 0
    counts = Counter()
    for letter in word:
        if letter == "0":
            counts[height] += 1
            height += 1
        elif letter == "1":
            height -= 1
        else:
            raise ValueError("A binary word is required.")
    return tuple(sorted(counts.items()))


def realize_profile(profile):
    """Return a deterministic Euler-trail realization beginning with 1."""
    profile = tuple(profile)
    heights = [height for height, _ in profile]
    counts = dict(profile)
    if not heights or heights != list(range(heights[0], heights[-1] + 1)):
        raise ValueError("The support must be a consecutive interval.")
    if not (heights[0] <= -1 and heights[-1] >= 0):
        raise ValueError("The support must contain -1 and 0.")
    if any(not isinstance(c, int) or c <= 0 for c in counts.values()):
        raise ValueError("Profile multiplicities must be positive integers.")

    a = sum(counts.values())
    edges = defaultdict(Counter)
    for height, multiplicity in profile:
        edges[height][height + 1] += multiplicity
        down = multiplicity - int(height == 0)
        if down:
            edges[height + 1][height] += down

    # Prescribe the first letter 1, which is the down-edge 0 -> -1.
    assert edges[0][-1] > 0
    edges[0][-1] -= 1

    incoming = Counter()
    outgoing = Counter()
    neighbors = defaultdict(set)
    for start, row in edges.items():
        for end, multiplicity in row.items():
            if multiplicity:
                outgoing[start] += multiplicity
                incoming[end] += multiplicity
                neighbors[start].add(end)
                neighbors[end].add(start)

    # Check both hypotheses of the Euler-trail criterion after removal.
    active = set(incoming) | set(outgoing)
    for vertex in active:
        expected = int(vertex == -1) - int(vertex == 1)
        assert outgoing[vertex] - incoming[vertex] == expected
    reached = {-1}
    frontier = [-1]
    while frontier:
        vertex = frontier.pop()
        for neighbor in neighbors[vertex]:
            if neighbor not in reached:
                reached.add(neighbor)
                frontier.append(neighbor)
    assert reached == active

    # Hierholzer's algorithm; the ordering makes the chosen word reproducible.
    stack = [-1]
    reverse_trail = []
    while stack:
        vertex = stack[-1]
        destinations = [
            end for end, multiplicity in edges[vertex].items() if multiplicity
        ]
        if destinations:
            end = min(destinations)
            edges[vertex][end] -= 1
            stack.append(end)
        else:
            reverse_trail.append(stack.pop())

    trail = list(reversed(reverse_trail))
    assert trail[0] == -1 and trail[-1] == 1
    assert len(trail) == 2 * a - 1
    assert all(multiplicity == 0 for row in edges.values()
               for multiplicity in row.values())
    vertices = [0] + trail
    letters = []
    for start, end in zip(vertices, vertices[1:]):
        assert abs(end - start) == 1
        letters.append("0" if end == start + 1 else "1")
    word = "".join(letters)
    assert word.startswith("1")
    assert word.count("0") == a and word.count("1") == a - 1
    assert zero_height_profile(word) == profile
    return word


def literal_word_profiles(a):
    """Independent comparison by literal enumeration of all admissible words."""
    profiles = set()
    count = 0
    length = 2 * a - 1
    for zero_positions in combinations(range(1, length), a):
        zeros = set(zero_positions)
        word = "".join("0" if index in zeros else "1"
                       for index in range(length))
        assert word[0] == "1"
        profiles.add(zero_height_profile(word))
        count += 1
    assert count == comb(2 * a - 2, a)
    return profiles, count


def main():
    rows = []
    examples = []
    total_profiles = 0
    total_words = 0
    for a in range(2, 10):
        profiles = list(admissible_profiles(a))
        proposed = set(profiles)
        assert len(proposed) == len(profiles)
        for profile in profiles:
            word = realize_profile(profile)
            if a == 3:
                examples.append({
                    "a": a,
                    "profile": [[height, c] for height, c in profile],
                    "realizing_word": word,
                })
        actual, word_count = literal_word_profiles(a)
        expected = (a - 1) * 2 ** (a - 2)
        composition_sum = sum(
            (size - 1) * comb(a - 1, size - 1)
            for size in range(2, a + 1)
        )
        assert proposed == actual
        assert len(proposed) == expected == composition_sum
        rows.append({
            "a": a,
            "constructed_profiles": len(proposed),
            "literal_word_profiles": len(actual),
            "all_admissible_words": word_count,
            "expected_A001787_at_a_minus_1": expected,
            "profile_sets_equal": True,
            "all_realizations_verified": True,
            "post_removal_degree_and_connectivity_checks": len(proposed),
        })
        total_profiles += len(proposed)
        total_words += word_count

    report = {
        "status": "passed",
        "arithmetic": "exact integer arithmetic",
        "a_range": [2, 9],
        "profiles_constructively_realized": total_profiles,
        "admissible_words_independently_enumerated": total_words,
        "enumeration_formula": "(a-1)*2**(a-2)",
        "oeis_reference": "https://oeis.org/A001787",
        "oeis_index": "a-1",
        "counts_by_a": rows,
        "examples": examples,
        "scope": (
            "Finite checks support the constructive proof; the all-a theorem "
            "uses the Euler-trail argument in the article."
        ),
    }
    output = Path(__file__).resolve().parents[1] / "data" / "profile_realization_checks.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    rendered = json.dumps(report, indent=2) + "\n"
    with output.open("w", encoding="utf-8", newline="\n") as stream:
        stream.write(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()

