#!/usr/bin/env python3
"""Executable checks of every algebraic identity in the synchronization proof.

The article, not these finite tests, supplies the universal proof.
"""
from __future__ import annotations
from collections import deque
from pathlib import Path
import random
import sys
from automata import (compose, construction, expanded_reset_word, make_family,
                      power, quotient_colours, reset_length, short_merging_word,
                      word_action)
from verify_certificates import independent_model

ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def strong_connectivity(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    reverse: list[list[int]] = [[] for _ in a]
    for q in range(len(a)):
        reverse[a[q]].append(q)
        reverse[b[q]].append(q)
    for backward in [False, True]:
        visited, queue = {0}, deque([0])
        while queue:
            q = queue.popleft()
            for target in (reverse[q] if backward else [a[q], b[q]]):
                if target not in visited:
                    visited.add(target)
                    queue.append(target)
        if len(visited) != len(a):
            return False
    return True


def check_parameter(k: int) -> None:
    aut = make_family(k)
    ai, bi = independent_model(k)
    require(aut.a == tuple(ai) and aut.b == tuple(bi), "Constructor mismatch")
    r, m = k+4, 2*k+4
    require(len(set(aut.a)) == aut.n-1 == len(set(aut.b)), "Letter ranks")
    require(strong_connectivity(aut.a, aut.b), "Strong connectivity")
    maps = construction(k)
    C = [0] + list(range(1, m, 2)) + [2]
    inv = {q: j for j, q in enumerate(C)}
    require(len(C) == r and set(maps["p"]) == set(C), "Retraction image")
    require([maps["p"][q] for q in C] == C, "Retraction restriction")
    require([maps["c"][q] for q in C] == C[1:]+C[:1], "Cycle action")
    expected = {
        "F": [1 if j == r-2 else (-j) % r for j in range(r)],
        "H": [(1-j) % r for j in range(r)],
        "e": [r-1 if j == r-2 else j for j in range(r)],
        "h": [r-2 if j == r-2 else (j-1) % r for j in range(r)]}
    for name, target in expected.items():
        require([inv[maps[name][q]] for q in C] == target, name+" identity")
    require(set(maps["R"]) == {2}, "Reset identity")
    for exponent in sorted(set([0, 1, r//2, r-2, r-1, r])):
        ht = power(maps["h"], exponent)
        require(len({ht[q] for q in C}) == max(1, r-exponent), "Rank profile")
    # Known upper bound: evaluate its two long blocks without word expansion.
    u = compose(aut.b, aut.a)
    w = compose(power(u, r-2), power(maps["c"], r-2))
    require(w[0] == w[2] == 2, "Known short merging word")
    smaller = make_family(k, shortened=True)
    ai, bi = independent_model(k, shortened=True)
    require(smaller.a == tuple(ai) and smaller.b == tuple(bi), "Shortened model")
    colours = quotient_colours(k, shortened=True)
    require(set(colours) == set(range(r)), "Quotient surjectivity")
    for q in range(smaller.n):
        require(colours[smaller.a[q]] == -colours[q] % r, "a quotient")
        require(colours[smaller.b[q]] == (1-colours[q]) % r, "b quotient")
    colours = quotient_colours(k)
    defects = [(q, letter) for q in range(aut.n) for letter, trans in
               [("a", aut.a), ("b", aut.b)]
               if colours[trans[q]] != ((-colours[q]) if letter == "a" else
                                         (1-colours[q])) % r]
    require(defects == [(aut.n-1, "a" if (aut.n-1) % 2 == 0 else "b")],
            "Single endpoint defect")


def main() -> None:
    for k in list(range(1, 301)) + [500, 1000, 10000]:
        check_parameter(k)
    print("PASS: all structural identities, k=1..300 and k=500,1000,10000")
    print("PASS: both automaton constructors agree on these parameters")
    print("PASS: shortened-family permutation quotient and single endpoint defect")
    for k in range(1, 11):
        aut = make_family(k)
        word = expanded_reset_word(k)
        require(len(word) == reset_length(k), "Expanded reset length")
        image = word_action(aut, word)
        require(set(image) == {2}, "Expanded reset word")
        # A second, state-by-state evaluator avoids tuple composition.
        for start in range(aut.n):
            state = start
            for letter in word:
                state = aut.a[state] if letter == "a" else aut.b[state]
            require(state == 2, "Direct reset simulation")
    rng = random.Random(20260920)
    for _ in range(300):
        k = rng.randrange(1, 11)
        aut = make_family(k)
        word = "".join(rng.choice("ab") for _ in range(rng.randrange(50)))
        image = word_action(aut, word)
        for start in range(aut.n):
            state = start
            for letter in word:
                state = aut.a[state] if letter == "a" else aut.b[state]
            require(state == image[start], "Word evaluator orientation")
    print("PASS: expanded reset words k=1..10, two independent evaluators")
    print("PASS: 300 reproducible random-word orientation checks")
    for bad in [0, -1, 1.5, True]:
        try:
            make_family(bad)
        except ValueError:
            continue
        raise ValueError("Invalid parameter was accepted")
    try:
        expanded_reset_word(10000)
    except ValueError:
        pass
    else:
        raise ValueError("Expansion guard failed")
    print("PASS: invalid-parameter rejection and large-word expansion guard")
    print("All checks complete. These checks are finite, not a formal universal proof.")

if __name__ == "__main__":
    main()
