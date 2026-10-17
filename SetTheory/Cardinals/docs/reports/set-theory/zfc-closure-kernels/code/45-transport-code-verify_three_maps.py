#!/usr/bin/env python3
"""Reproduce finite evidence for the three-map construction; standard library."""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
import random
import statistics
import time

from transport26 import (NEW_MODES, apply_stream_word, compile_four, downward,
                        encode, evaluate, factor_four, factor_three, free_names,
                        reduce_word, rename, scalar, swap_interval, swap_live,
                        table, transduce)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def verify():
    started = time.monotonic()
    result = {"status": "PASS", "scope": "finite executable evidence, not a proof-assistant certificate or TM"}
    algebra = 0
    for x in range(-100, 101):
        require(evaluate("gg", x) == (1 if x == 2 else x), "g squared")
        require(evaluate("ggg", x) == scalar("g", x), "g cubed")
        algebra += 2
    for j in range(-12, 13):
        for x in range(-20, 21):
            require(evaluate(downward(j), x) == (x - 1 if x == j else x), "downward")
            algebra += 1
    result["scalar_identity_checks"] = algebra

    swaps = 0
    for lo in range(-7, 8):
        for size in range(2, 17):
            hi = lo + size - 1
            for i in range(lo, hi):
                word = swap_interval(lo, hi, i)
                require(len(word) == 3 * size - 2 + abs(2 - lo) + abs(hi - 1), "exact word length")
                for x in range(lo, hi + 1):
                    wanted = i + 1 if x == i else i if x == i + 1 else x
                    require(evaluate(word, x) == wanted, "interval swap")
                    require(evaluate(reduce_word(word), x) == wanted, "reduced interval swap")
                    swaps += 1
    result["interval_swap_point_checks"] = swaps

    live_checks = 0
    universe = list(range(-3, 6))
    for mask in range(1 << len(universe)):
        live = {x for k, x in enumerate(universe) if (mask >> k) & 1}
        for i in range(-3, 5):
            word = swap_live(live, i)
            for x in live:
                require(evaluate(word, x) == (i + 1 if x == i else i if x == i + 1 else x), "live swap")
                live_checks += 1
        for mode in "tk":
            word = compile_four(mode, live)
            for x in live:
                require(evaluate(word, x) == scalar(mode, x), "four-mode macro")
                live_checks += 1
    result["live_macro_point_checks"] = live_checks

    distributions = []
    total_maps = 0
    for n in range(1, 6):
        old_sizes, new_sizes, contractions = [], [], []
        for image in product(range(n), repeat=n):
            mapping = dict(enumerate(image))
            old = factor_four(mapping)
            new = compile_four(old, set(mapping))
            require(set(new) <= NEW_MODES, "unexpected new mode")
            for source, target in mapping.items():
                require(evaluate(old, source) == target, "four-mode control")
                require(evaluate(new, source) == target, "three-mode factorization")
            old_sizes.append(len(old))
            new_sizes.append(len(new))
            contractions.append(n - len(set(image)))
            total_maps += 1
        distributions.append({"n": n, "maps": n ** n,
                              "four_length_mean": statistics.mean(old_sizes),
                              "four_length_max": max(old_sizes),
                              "three_length_mean": statistics.mean(new_sizes),
                              "three_length_max": max(new_sizes),
                              "three_shorter": sum(a < b for a, b in zip(new_sizes, old_sizes)),
                              "same_length": sum(a == b for a, b in zip(new_sizes, old_sizes)),
                              "three_longer": sum(a > b for a, b in zip(new_sizes, old_sizes))})
    result["exhaustive_total_maps"] = total_maps
    result["map_distributions"] = distributions

    rng = random.Random(20261017)
    for _ in range(300):
        sources = rng.sample(range(-9, 10), rng.randrange(9))
        mapping = {x: rng.randrange(-9, 10) for x in sources}
        word = factor_three(mapping)
        for x, y in mapping.items():
            require(evaluate(word, x) == y, "signed map")
    result["signed_random_maps"] = 300

    stream_checks = 0
    for x in range(-24, 25):
        for depth in range(1, 8):
            atom = ("rel", ("f", x), ("b", depth - 1))
            for mode in "sSg":
                require(transduce(mode, encode(atom)) == encode(rename(atom, lambda z: scalar(mode, z))), "stream scalar")
                stream_checks += 1

    def random_formula(depth=0, budget=4):
        if budget == 0 or rng.random() < 0.5:
            if rng.random() < 0.08:
                return ("bot",)
            def var():
                if depth and rng.random() < 0.45:
                    return ("b", rng.randrange(depth))
                return ("f", rng.randrange(-3, 4))
            return ("rel", var(), var())
        if rng.random() < 0.5:
            return ("all", random_formula(depth + 1, budget - 1))
        return ("imp", random_formula(depth, budget - 1), random_formula(depth, budget - 1))

    for _ in range(100):
        formula = random_formula()
        live = free_names(formula)
        mapping = {x: rng.randrange(-3, 4) for x in live}
        word = factor_three(mapping)
        expect = encode(rename(formula, lambda x: mapping[x]))
        require(apply_stream_word(word, encode(formula)) == expect, "capture-free whole stream")
        stream_checks += 1
    result["stream_formula_checks"] = stream_checks
    result["transducer_tables"] = {mode: table(mode) for mode in "sSg"}
    result["stream_control_states"] = {mode: table(mode)["states"] for mode in "sSg"}

    # A concrete colliding composite instance: the free-name map 0->1 acts
    # on every occurrence in an implication and beneath a binder, while b0
    # remains bound.  This is the transport interface required by source28.
    formula = ("imp", ("rel", ("f", 0), ("f", 1)),
               ("all", ("imp", ("rel", ("b", 0), ("f", 0)),
                                ("rel", ("f", 1), ("b", 0)))))
    word, certificate = compile_four("k", free_names(formula), with_certificate=True)
    expected = rename(formula, lambda x: 1 if x == 0 else x)
    require(apply_stream_word(word, encode(formula)) == encode(expected), "composite collision")
    result["composite_collision"] = {"input": formula, "output": expected,
                                     "word": word, "length": len(word), "certificate": certificate}

    # Deliberate invalid replacement: g alone is not a global swap because
    # live name2 would collide.  The support gate must reject this shortcut.
    require(evaluate("g", 2) != 2, "negative control was not negative")
    require(swap_live({0, 1, 2}, 0) != "g", "unsafe spare name shortcut")
    result["negative_controls"] = ["g is not a global transposition",
                                    "the spare-name shortcut is disabled when 2 is live"]
    result["elapsed_seconds"] = round(time.monotonic() - started, 6)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="three_maps_results.json")
    args = parser.parse_args()
    evidence = verify()
    Path(args.output).write_text(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps({key: evidence[key] for key in
                      ("status", "exhaustive_total_maps", "stream_formula_checks", "stream_control_states", "elapsed_seconds")}))
