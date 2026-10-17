#!/usr/bin/env python3
"""Reproducible finite checks of the 24-control two-map construction."""
from __future__ import annotations

import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import statistics
import time

import name_transport as new
import transport26 as original


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def verify():
    started = time.monotonic()
    root = Path(__file__).resolve().parent
    result = {"status": "PASS", "scope": "finite evidence for 24-control fixed renaming component; no TM state claim",
              "code_sha256": {f: hashlib.sha256((root / f).read_bytes()).hexdigest()
                              for f in ("transport26.py", "name_transport.py", "verify_name_transport.py")}}

    identities = 0
    for x in range(-100, 101):
        require(new.evaluate("wu", x) == new.scalar("h", x), "h reconstruction")
        identities += 1
    for x in range(1, 70):
        for b in range(x, x + 30):
            require(new.evaluate("w" * b, x) == x - b - 1, "crossing formula")
            identities += 1
    result["scalar_identity_checks"] = identities

    interval_swaps = 0
    for lo in range(-7, 8):
        for size in range(2, 17):
            hi = lo + size - 1
            for i in range(lo, hi):
                word = new.swap_interval(lo, hi, i)
                require(len(word) == 2 * size + 3 + abs(1 - lo) + abs(hi), "swap length")
                if lo == 0:
                    require(len(word) == 3 * size + 3, "normalized swap length")
                for x in range(lo, hi + 1):
                    expected = i + 1 if x == i else i if x == i + 1 else x
                    require(new.evaluate(word, x) == expected, "protected interval swap")
                    interval_swaps += 1
    result["interval_swap_point_checks"] = interval_swaps

    live_points = 0
    universe = list(range(-3, 6))
    for mask in range(1 << len(universe)):
        live = {x for j, x in enumerate(universe) if mask >> j & 1}
        for i in range(-3, 5):
            word = new.swap_live(live, i)
            for x in live:
                expected = i + 1 if x == i else i if x == i + 1 else x
                require(new.evaluate(word, x) == expected, "sparse live swap")
                live_points += 1
        for mode in "tk":
            word = new.compile_four(mode, live)
            for x in live:
                require(new.evaluate(word, x) == original.scalar(mode, x), "t/k macro")
                live_points += 1
    result["live_macro_point_checks"] = live_points

    decrement = 0
    for lo in range(-20, 21):
        for size in range(1, 21):
            live = set(range(lo, lo + size))
            hi = lo + size - 1
            word = new.down_two(live)
            require(len(word) == 2 * (max(0, 1 - lo) + max(0, hi)), "decrement length")
            for x in live:
                require(new.evaluate(word, x) == x - 1, "finite decrement")
                decrement += 1
    result["decrement_point_checks"] = decrement

    distributions, total = [], 0
    for n in range(1, 6):
        four_lengths, three_lengths, two_lengths = [], [], []
        for image in product(range(n), repeat=n):
            mapping = dict(enumerate(image))
            old = original.factor_four(mapping)
            middle = new.compile_four(old, set(mapping))
            word = new.compile_three_to_two(middle, set(mapping))
            require(set(word) <= new.TWO_MODES, "opcode alphabet")
            for x, y in mapping.items():
                require(new.evaluate(word, x) == y, "finite substitution")
            four_lengths.append(len(old))
            three_lengths.append(len(middle))
            two_lengths.append(len(word))
            total += 1
        distributions.append({"n": n, "maps": n ** n,
                              "four_mean": statistics.mean(four_lengths), "four_max": max(four_lengths),
                              "h_three_mean": statistics.mean(three_lengths), "h_three_max": max(three_lengths),
                              "two24_mean": statistics.mean(two_lengths), "two24_max": max(two_lengths)})
    result["exhaustive_maps"] = total
    result["length_distributions"] = distributions

    rng = random.Random(2026101724)
    for _ in range(150):
        live = rng.sample(range(-10, 11), rng.randrange(8))
        mapping = {x: rng.randrange(-10, 11) for x in live}
        word = new.factor_two(mapping)
        require(all(new.evaluate(word, x) == y for x, y in mapping.items()), "signed arbitrary map")
    result["signed_random_maps"] = 150

    for _ in range(100):
        word = "".join(rng.choice("sStk") for _ in range(rng.randrange(15)))
        live = set(rng.sample(range(-7, 8), rng.randrange(8)))
        converted = new.compile_four_to_two(word, live)
        require(all(new.evaluate(converted, x) == original.evaluate(word, x) for x in live), "source word API")
    result["signed_source_words"] = 100

    scanner = 0
    for x in range(-30, 31):
        for j in range(7):
            atom = ("rel", ("f", x), ("b", j))
            for mode in "uw":
                require(new.transduce(mode, new.encode(atom)) ==
                        new.encode(new.rename(atom, lambda z: new.scalar(mode, z))), "scanner")
                scanner += 1
    result["scanner_atom_checks"] = scanner
    result["stream_control_states"] = {mode: new.table(mode)["states"] for mode in "uw"}
    result["transducer_tables"] = {mode: new.table(mode) for mode in "uw"}

    composite = ("imp", ("rel", ("f", 0), ("f", 1)),
                 ("all", ("imp", ("rel", ("b", 0), ("f", 0)),
                                  ("rel", ("f", 1), ("b", 0)))))
    samples = []
    for mapping in ({0: 1, 1: 1}, {0: 1, 1: 0}, {0: -2, 1: 3}):
        word = new.factor_two(mapping)
        expected = new.rename(composite, mapping.__getitem__)
        require(new.apply_stream_word(word, new.encode(composite)) == new.encode(expected), "composite stream")
        samples.append({"map": mapping, "word": word, "length": len(word),
                        "input_bits": new.encode(composite), "output_bits": new.encode(expected)})
    result["composite_stream_samples"] = samples

    for _ in range(100):
        free = rng.sample(range(-3, 4), rng.randrange(1, 5))
        formula = ("all", ("imp", ("rel", ("b", 0), ("f", free[0])),
                                 ("all", ("rel", ("f", free[-1]), ("b", 1)))))
        live = new.free_names(formula)
        mapping = {x: rng.randrange(-3, 4) for x in live}
        word = new.factor_two(mapping)
        require(new.apply_stream_word(word, new.encode(formula)) ==
                new.encode(new.rename(formula, mapping.__getitem__)), "binder preservation")
    result["nested_formula_maps"] = 100
    # The bare local map h is not a swap, especially with its collision donor live.
    require(new.evaluate("wu", 0) != 1, "negative swap control")
    require(new.evaluate("wu", 0) == new.evaluate("wu", 2), "intentional global singularity")
    result["negative_controls"] = "PASS"
    result["elapsed_seconds"] = round(time.monotonic() - started, 6)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="name_transport_results.json")
    args = parser.parse_args()
    evidence = verify()
    Path(args.output).write_text(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps({k: evidence[k] for k in ("status", "exhaustive_maps", "stream_control_states", "elapsed_seconds")}))
