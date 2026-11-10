"""Finite illustration of the unit-translation collapse argument.

This is not an arithmetic proof checker or a proof of the universal theorem.
It exhaustively checks the finite dependency profiles of dimensions up to 4
by default. Each output of a putative binary tuple operation is either
uniformly bounded, bounded through x[j], or bounded through y[j].

For a unit e, L(z)=f(e,z) kills x-controlled coordinates and R(z)=f(z,e)
kills y-controlled coordinates. A surviving bound has only one dependency.
The returned word is ordered OUTSIDE TO INSIDE: "LR" represents L composed
with R, so R is applied to actual tuple values first.

Run:
    python3 unit_collapse.py
    python3 unit_collapse.py --max-dimension 4 --output results.json
"""

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path


def dependency(profile, state, letter):
    """Return the surviving dependency index, or None for a constant bound."""
    side, index = profile[state]
    if (side, letter) in (("x", "R"), ("y", "L")):
        return index
    return None


def killing_word(profile):
    """Greedily kill at least half the currently live bound dependencies."""
    live = set(range(len(profile)))
    word = ""
    trace = []
    while live:
        killed = {
            letter: {state for state in live
                     if dependency(profile, state, letter) is None}
            for letter in "LR"
        }
        # Iteration order breaks ties in favor of L, reproducibly.
        letter = max("LR", key=lambda candidate: len(killed[candidate]))
        following = {
            dependency(profile, state, letter)
            for state in live - killed[letter]
        }
        if len(following) > len(live) // 2:
            raise AssertionError("The live dependency set did not halve")
        trace.append({"before": sorted(live), "letter": letter,
                      "killed": sorted(killed[letter]),
                      "after": sorted(following)})
        word += letter
        live = following
    return word, trace


def kills_each_origin(profile, word):
    """Independent per-origin simulation, without set-based compression."""
    for origin in range(len(profile)):
        current = origin
        for letter in word:
            side, target = profile[current]
            survives = ((letter == "L" and side == "y")
                        or (letter == "R" and side == "x"))
            if not survives:
                current = None
                break
            current = target
        if current is not None:
            return False
    return True


def shortest_word(profile):
    """Brute-force all words by length; an independent minimality oracle."""
    upper_bound = len(profile).bit_length()
    for length in range(upper_bound + 1):
        for letters in itertools.product("LR", repeat=length):
            word = "".join(letters)
            if kills_each_origin(profile, word):
                return word
    raise AssertionError("No killing word within the proved bound")


def describe(profile):
    return [{"coordinate": i, "controller": side, "input_index": target}
            for i, (side, target) in enumerate(profile)]


def examine_dimension(dimension):
    choices = [("constant", None)]
    choices += [(side, index) for side in ("x", "y")
                for index in range(dimension)]
    expected_profiles = (2 * dimension + 1) ** dimension
    greedy_histogram = Counter()
    shortest_histogram = Counter()
    examined = 0
    worst_greedy = None
    worst_shortest = None
    largest_gap = None

    for profile in itertools.product(choices, repeat=dimension):
        word, trace = killing_word(profile)
        if not kills_each_origin(profile, word):
            raise AssertionError("Greedy word leaves an origin alive")
        if len(word) > dimension or len(word) > dimension.bit_length():
            raise AssertionError("Greedy word exceeds a universal bound")
        shortest = shortest_word(profile)
        if len(shortest) > len(word):
            raise AssertionError("Minimality oracle contradicts greedy word")

        greedy_histogram[len(word)] += 1
        shortest_histogram[len(shortest)] += 1
        examined += 1
        record = {"profile": describe(profile), "greedy_word": word,
                  "shortest_word": shortest, "trace": trace}
        if worst_greedy is None or len(word) > len(worst_greedy["greedy_word"]):
            worst_greedy = record
        if (worst_shortest is None
                or len(shortest) > len(worst_shortest["shortest_word"])):
            worst_shortest = record
        gap = len(word) - len(shortest)
        if largest_gap is None or gap > largest_gap["gap"]:
            largest_gap = {"gap": gap, **record}

    if examined != expected_profiles:
        raise AssertionError("Profile enumeration was incomplete")
    return {
        "dimension": dimension,
        "profiles_checked": examined,
        "expected_profiles": expected_profiles,
        "word_length_upper_bound": dimension.bit_length(),
        "greedy_length_histogram": dict(sorted(greedy_histogram.items())),
        "shortest_length_histogram": dict(sorted(shortest_histogram.items())),
        "max_greedy_length_example": worst_greedy,
        "max_shortest_length_example": worst_shortest,
        "largest_greedy_gap_example": largest_gap,
    }


def sharp_tree(height):
    """The complete binary-tree profile of dimension 2**height - 1."""
    profile = [("constant", None)]
    profile += [("x" if state % 2 else "y", (state - 1) // 2)
                for state in range(1, 2 ** height - 1)]
    return tuple(profile)


def examine_sharp_trees():
    """Check finite sharp examples, with exhaustive words through height 7."""
    results = []
    for height in range(1, 11):
        profile = sharp_tree(height)
        greedy, trace = killing_word(profile)
        if len(greedy) != height or not kills_each_origin(profile, greedy):
            raise AssertionError("Binary-tree example has the wrong height")

        # At a full prefix of 2**level-1 states, BOTH letter images are the
        # full prefix of 2**(level-1)-1 states. Check this finite identity.
        for level in range(1, height + 1):
            live = range(2 ** level - 1)
            expected = set(range(2 ** (level - 1) - 1))
            for letter in "LR":
                actual = {dependency(profile, state, letter) for state in live}
                actual.discard(None)
                if actual != expected:
                    raise AssertionError("Binary-tree prefix image mismatch")

        words_tested = 0
        if height <= 7:
            for length in (height - 1, height):
                for letters in itertools.product("LR", repeat=length):
                    word = "".join(letters)
                    if kills_each_origin(profile, word) != (length == height):
                        raise AssertionError("Binary-tree sharpness check failed")
                    words_tested += 1
        results.append({"height": height, "dimension": len(profile),
                        "greedy_word": greedy, "minimum_word_length": height,
                        "prefix_identity_checked": True,
                        "exhaustive_words_tested": words_tested,
                        "trace_sizes": [len(step["before"]) for step in trace]
                                       + [0]})
    return results


def sharp_shift(dimension):
    """A sharp profile in every positive dimension, using binary shifts."""
    if dimension < 1:
        raise ValueError("The sharp shift family needs positive dimension")
    active = 1 << (dimension.bit_length() - 1)
    if active == 1:
        profile = [("x", 0)]  # Survive R forever; L kills this state.
    else:
        profile = [("y" if state < active // 2 else "x",
                    (2 * state + 1) % active)
                   for state in range(active)]
    profile += [("constant", None)] * (dimension - active)
    return tuple(profile)


def examine_sharp_shifts():
    """Brute-force minimum words for the sharp family in dimensions 1..64."""
    results = []
    for dimension in range(1, 65):
        profile = sharp_shift(dimension)
        greedy, unused_trace = killing_word(profile)
        shortest = shortest_word(profile)
        expected = dimension.bit_length()
        if len(greedy) != expected or len(shortest) != expected:
            raise AssertionError("Shift-family sharpness check failed")
        results.append({"dimension": dimension, "minimum_word_length": expected,
                        "greedy_word": greedy, "shortest_word": shortest})
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-dimension", type=int, default=4)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("unit_collapse_results.json"))
    args = parser.parse_args()
    if args.max_dimension < 0:
        parser.error("Maximum dimension must be nonnegative")

    dimensions = [examine_dimension(d) for d in range(args.max_dimension + 1)]
    result = {
        "status": "PASS",
        "scope": "Finite dependency-automaton illustration, not a universal proof",
        "profile_meaning": "Each coordinate is constant, x[j]-bounded, or y[j]-bounded",
        "word_order": "Outside to inside: LR denotes L composed with R",
        "universal_length_bound": "floor(log2(d)) + 1 for d>0; 0 for d=0",
        "checks": ["complete profile enumeration", "greedy live-set halving",
                   "independent per-origin word simulation",
                   "brute-force shortest-word comparison"],
        "total_profiles_checked": sum(d["profiles_checked"] for d in dimensions),
        "dimensions": dimensions,
        "sharp_binary_tree_examples": examine_sharp_trees(),
        "sharp_shift_examples": examine_sharp_shifts(),
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "total_profiles_checked": result["total_profiles_checked"],
                      "maximum_lengths": [
                          {"dimension": d["dimension"],
                           "greedy": max(d["greedy_length_histogram"]),
                           "shortest": max(d["shortest_length_histogram"])}
                          for d in dimensions],
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
