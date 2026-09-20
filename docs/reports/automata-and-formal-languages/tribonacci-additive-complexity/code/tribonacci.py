#!/usr/bin/env python3
"""Exact additive complexity and prefix counts for the Tribonacci word.

Standard library only.  Read digits most-significant first; -1 is an invalid
transition.  Counts use the half-open interval 0 <= n < N.  At n=0 the output
is 1, corresponding to the empty factor.  See article.tex for the proof.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
LABELS = (1, 3, 4, 5)
PHI = {"0": "01", "1": "02", "2": "0"}
Pair = tuple[str, str]
State = frozenset[Pair]


def require(condition: bool, message: str) -> None:
    """Unlike assert, this check remains active under python -O."""
    if not condition:
        raise ValueError(message)


def morphism(word: str) -> str:
    return "".join(PHI[a] for a in word)


def decompose(top: str, bottom: str) -> State:
    """Cut at every common Parikh-prefix vector; return the set of pieces."""
    require(len(top) == len(bottom), "Unequal lengths in co-decomposition")
    start = 0
    difference = [0, 0, 0]
    pieces: set[Pair] = set()
    for end, (a, b) in enumerate(zip(top, bottom), start=1):
        difference[int(a)] += 1
        difference[int(b)] -= 1
        if difference == [0, 0, 0]:
            pieces.add((top[start:end], bottom[start:end]))
            start = end
    require(start == len(top), "Words have unequal Parikh vectors")
    return frozenset(pieces)


def transform(state: State, digit: int) -> State:
    require(digit in (0, 1), "The digit must be 0 or 1")
    pieces: set[Pair] = set()
    for top, bottom in sorted(state):
        top, bottom = morphism(top), morphism(bottom)
        if digit:
            require(bottom.startswith("0"), "Rotation needs an initial zero")
            bottom = bottom[1:] + "0"
        pieces.update(decompose(top, bottom))
    return frozenset(pieces)


def relative_sums(state: State) -> tuple[int, ...]:
    values = {0}
    for top, bottom in state:
        total = 0
        for a, b in zip(top, bottom):
            total += int(b) - int(a)
            values.add(total)
    return tuple(sorted(values))


def build_automaton() -> tuple[dict, dict]:
    """Reconstruct the finite model, rather than infer it from sample values.

    Exhaustive closure: 277 sets of pairs.  Restriction to the no-111 language:
    296 reachable (set, trailing-one-count) states.  Output-preserving Moore
    refinement produces 76 live states and one omitted invalid sink.
    """
    initial: State = frozenset({("0", "0"), ("01", "10"), ("02", "20")})
    states = [initial]
    index = {initial: 0}
    raw_transitions: list[list[int]] = []
    for state in states:
        row = []
        for digit in (0, 1):
            following = transform(state, digit)
            if following not in index:
                index[following] = len(states)
                states.append(following)
            row.append(index[following])
        raw_transitions.append(row)
        require(len(states) <= 10000, "Unexpectedly large closure")
    raw_outputs = [len(relative_sums(state)) for state in states]

    products = [(0, 1)]
    product_index = {products[0]: 0}
    partial: list[list[int]] = []
    for state, run in products:
        row = []
        for digit in (0, 1):
            if digit == 1 and run == 2:
                row.append(-1)
                continue
            following = (raw_transitions[state][digit], run + 1 if digit else 0)
            if following not in product_index:
                product_index[following] = len(products)
                products.append(following)
            row.append(product_index[following])
        partial.append(row)

    dead, empty = len(products), len(products) + 1
    complete = [[dead if t < 0 else t for t in row] for row in partial]
    complete.extend([[dead, dead], [empty, 0]])
    outputs = [raw_outputs[q] for q, _ in products] + [0, 1]
    partition = outputs[:]
    refinement_rounds = 0
    while True:
        identifiers: dict[tuple, int] = {}
        following_partition = []
        for q, output in enumerate(outputs):
            signature = (output, tuple(partition[t] for t in complete[q]))
            following_partition.append(identifiers.setdefault(signature,
                                                               len(identifiers)))
        refinement_rounds += 1
        if following_partition == partition:
            break
        partition = following_partition
    size = max(partition) + 1
    quotient: list[list[int]] = [[] for _ in range(size)]
    quotient_outputs = [0] * size
    for q, output in enumerate(outputs):
        quotient[partition[q]] = [partition[t] for t in complete[q]]
        quotient_outputs[partition[q]] = output
    initial_class, dead_class = partition[empty], partition[dead]
    order = [initial_class]
    numbered = {initial_class: 0}
    for q in order:
        for t in quotient[q]:
            if t != dead_class and t not in numbered:
                numbered[t] = len(order)
                order.append(t)
    transitions = [[numbered.get(t, -1) for t in quotient[q]] for q in order]
    values = [quotient_outputs[q] for q in order]

    # Check the entire quotient diagram, not just representative states.
    mapping = [numbered.get(partition[q], -1) for q in range(len(complete))]
    for q in range(len(complete)):
        if q == dead:
            continue
        require(values[mapping[q]] == outputs[q], "Quotient changed an output")
        for digit in (0, 1):
            require(transitions[mapping[q]][digit] == mapping[complete[q][digit]],
                    "Quotient transition does not commute")

    pairs = sorted(set().union(*states))
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    certificate = {
        "pairs": [list(pair) for pair in pairs],
        "sets": [sorted(pair_index[pair] for pair in state) for state in states],
        "raw_transitions": raw_transitions,
        "raw_outputs": raw_outputs,
        "raw_relative_sums": [list(relative_sums(state)) for state in states],
        "product_states": [list(pair) for pair in products],
        "product_to_live": mapping[:len(products)],
        "refinement_rounds": refinement_rounds,
    }
    machine = {"initial": 0, "transitions": transitions, "outputs": values}
    return machine, certificate


def load_automaton(path: Path | None = None) -> dict:
    with (path or ROOT / "data" / "automaton.json").open(encoding="utf-8") as stream:
        data = json.load(stream)
    transitions, outputs = data["transitions"], data["outputs"]
    require(data["initial"] == 0, "Expected initial state 0")
    require(len(transitions) == len(outputs) == 76, "Expected 76 live states")
    require(all(len(row) == 2 for row in transitions), "Expected binary transitions")
    require(all(isinstance(t, int) and -1 <= t < 76
                for row in transitions for t in row), "Invalid target state")
    require(all(o in LABELS for o in outputs), "Invalid output label")
    return data


def representation(n: int) -> str:
    require(isinstance(n, int) and not isinstance(n, bool) and n >= 0,
            "n must be a nonnegative integer")
    if n == 0:
        return ""
    weights = [1, 2, 4]
    while weights[-1] <= n:
        weights.append(sum(weights[-3:]))
    while weights[-1] > n:
        weights.pop()
    digits = []
    remaining = n
    for weight in reversed(weights):
        digit = int(remaining >= weight)
        digits.append(str(digit))
        remaining -= digit * weight
    word = "".join(digits)
    require(remaining == 0 and "111" not in word, "Numeration failure")
    return word


def complexity(n: int, machine: dict | None = None) -> int:
    data = machine or load_automaton()
    state = data["initial"]
    for digit in representation(n):
        state = data["transitions"][state][int(digit)]
        require(state >= 0, "A canonical representation was rejected")
    return data["outputs"][state]


def suffix_counts(length: int, machine: dict) -> list[list[list[int]]]:
    transitions, outputs = machine["transitions"], machine["outputs"]
    tables = [[[int(output == value) for value in LABELS] for output in outputs]]
    for _ in range(length):
        previous = tables[-1]
        tables.append([[sum(previous[t][i] for t in row if t >= 0)
                        for i in range(len(LABELS))] for row in transitions])
    return tables


def prefix_counts(N: int, machine: dict | None = None) -> dict[int, int]:
    """Return #{0 <= n < N : complexity(n)=j}, for j=1,3,4,5."""
    data = machine or load_automaton()
    digits = representation(N)
    tables = suffix_counts(len(digits), data)
    counts = [0] * len(LABELS)
    state = data["initial"]
    for position, digit in enumerate(digits):
        remaining = len(digits) - position - 1
        if digit == "1":
            alternative = data["transitions"][state][0]
            if alternative >= 0:
                for i, count in enumerate(tables[remaining][alternative]):
                    counts[i] += count
        state = data["transitions"][state][int(digit)]
        require(state >= 0, "A canonical bound was rejected")
    require(sum(counts) == N, "Prefix count does not equal the requested range")
    return dict(zip(LABELS, counts))


def tribonacci_numbers(length: int) -> list[int]:
    require(length >= 0, "length must be nonnegative")
    values = [1, 2, 4]
    while len(values) < length:
        values.append(sum(values[-3:]))
    return values[:length]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--value", type=int, metavar="N")
    group.add_argument("--count", type=int, metavar="N")
    args = parser.parse_args()
    try:
        if args.value is not None:
            result = {"n": args.value, "tribonacci_representation": representation(args.value),
                      "additive_complexity": complexity(args.value)}
        else:
            result = {"N": args.count, "interval": "0 <= n < N",
                      "counts": prefix_counts(args.count)}
        print(json.dumps(result, indent=2))
    except (OSError, ValueError, KeyError) as error:
        parser.exit(2, f"error: {error}\n")


if __name__ == "__main__":
    main()
