#!/usr/bin/env python3
"""Exhaustive finite checks for two simple total streaming renamings."""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
import random
import statistics
import time

from transport26 import (TWO_MODES, apply_stream_word, compile_three_to_two,
                        down_two, encode, evaluate, factor_four, factor_three,
                        factor_two, free_names, rename, scalar, table, transduce)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def verify():
    started = time.monotonic()
    result = {"status": "PASS", "scope": "finite checks of explicit two-map finite-live transport; no TM or kernel theorem"}
    orbit = 0
    for x in range(2, 70):
        for b in range(x - 1, x + 30):
            require(evaluate("v" * b, x) == x - b - 2, "crossing formula")
            orbit += 1
    for x in range(-100, 101):
        require(evaluate("vu", x) == scalar("g", x), "global g reconstruction")
        orbit += 1
    result["orbit_identity_checks"] = orbit

    decrement = 0
    for lo in range(-20, 21):
        for size in range(1, 21):
            hi = lo + size - 1
            live = set(range(lo, hi + 1))
            word = down_two(live)
            require(len(word) == 2 * (max(0, 2 - lo) + max(0, hi)) - 1, "decrement length")
            for x in live:
                require(evaluate(word, x) == x - 1, "finite decrement")
                decrement += 1
    result["decrement_point_checks"] = decrement

    distributions, total = [], 0
    for n in range(1, 6):
        old_lengths, three_lengths, two_lengths = [], [], []
        for image in product(range(n), repeat=n):
            mapping = dict(enumerate(image))
            old = factor_four(mapping)
            three = factor_three(mapping)
            two = compile_three_to_two(three, set(mapping))
            require(set(two) <= TWO_MODES, "invalid opcode")
            for x, y in mapping.items():
                require(evaluate(two, x) == y, "finite substitution")
            old_lengths.append(len(old))
            three_lengths.append(len(three))
            two_lengths.append(len(two))
            total += 1
        distributions.append({"n": n, "maps": n ** n,
                              "four_mean": statistics.mean(old_lengths), "four_max": max(old_lengths),
                              "three_mean": statistics.mean(three_lengths), "three_max": max(three_lengths),
                              "two_mean": statistics.mean(two_lengths), "two_max": max(two_lengths)})
    result["exhaustive_maps"] = total
    result["length_distributions"] = distributions

    rng = random.Random(2026101702)
    for _ in range(150):
        live = rng.sample(range(-10, 11), rng.randrange(8))
        mapping = {x: rng.randrange(-10, 11) for x in live}
        word = factor_two(mapping)
        require(all(evaluate(word, x) == y for x, y in mapping.items()), "signed arbitrary map")
    result["signed_random_maps"] = 150

    scanner = 0
    for x in range(-30, 31):
        for j in range(7):
            atom = ("rel", ("f", x), ("b", j))
            for mode in "uv":
                require(transduce(mode, encode(atom)) == encode(rename(atom, lambda z: scalar(mode, z))), "scanner")
                scanner += 1
    result["scanner_atom_checks"] = scanner
    result["stream_control_states"] = {mode: table(mode)["states"] for mode in "uv"}
    result["transducer_tables"] = {mode: table(mode) for mode in "uv"}

    composite = ("imp", ("rel", ("f", 0), ("f", 1)),
                 ("all", ("imp", ("rel", ("b", 0), ("f", 0)),
                                  ("rel", ("f", 1), ("b", 0)))))
    samples = []
    for mapping in ({0: 1, 1: 1}, {0: 1, 1: 0}, {0: -2, 1: 3}):
        word = factor_two(mapping)
        expected = rename(composite, lambda x: mapping[x])
        require(apply_stream_word(word, encode(composite)) == encode(expected), "whole composite stream")
        samples.append({"map": mapping, "word": word, "length": len(word),
                        "input_bits": encode(composite), "output_bits": encode(expected)})
    result["composite_stream_samples"] = samples

    for _ in range(100):
        free = rng.sample(range(-3, 4), rng.randrange(1, 5))
        f = ("all", ("imp", ("rel", ("b", 0), ("f", free[0])),
                             ("all", ("rel", ("f", free[-1]), ("b", 1)))))
        actual = free_names(f)
        mapping = {x: rng.randrange(-3, 4) for x in actual}
        word = factor_two(mapping)
        require(apply_stream_word(word, encode(f)) == encode(rename(f, mapping.__getitem__)), "binder preservation")
    result["nested_formula_maps"] = 100
    result["elapsed_seconds"] = round(time.monotonic() - started, 6)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="two_maps_results.json")
    args = parser.parse_args()
    evidence = verify()
    Path(args.output).write_text(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps({k: evidence[k] for k in ("status", "exhaustive_maps", "stream_control_states", "elapsed_seconds")}))
