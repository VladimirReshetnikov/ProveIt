#!/usr/bin/env python3
"""Exact checks for the accompanying article (Python 3.10+, standard library).

This is an executable arithmetic checker and regression suite, not a formal
proof assistant. RLE witnesses use exactly the coordinates printed in the
article. Integers are arbitrary precision; no floating-point arithmetic occurs.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


@dataclass(frozen=True)
class Network:
    """Active destinations are 0..n-1, absorbing sinks n..n+s-1."""
    periods: tuple[tuple[tuple[int, int], ...], ...]
    sinks: int

    def __post_init__(self) -> None:
        if self.sinks < 1 or not self.periods:
            raise ValueError("Need at least one active vertex and one sink")
        for blocks in self.periods:
            if not blocks:
                raise ValueError("Periods must be nonempty")
            for dest, length in blocks:
                if (type(dest) is not int or type(length) is not int
                        or not (0 <= dest < self.n + self.sinks) or length < 1):
                    raise ValueError("Invalid destination or block length")

    @property
    def n(self) -> int:
        return len(self.periods)

    @property
    def m(self) -> int:
        return sum(map(len, self.periods))

    def length(self, v: int) -> int:
        return sum(length for _, length in self.periods[v])

    def prefix(self, v: int, count: int) -> tuple[list[int], int | None]:
        if count < 0:
            raise ValueError("Negative firing count")
        out = [0] * (self.n + self.sinks)
        if count == 0:
            return out, None
        q, r = divmod(count - 1, self.length(v))
        r += 1
        for dest, length in self.periods[v]:
            out[dest] += q * length
        last = None
        for dest, length in self.periods[v]:
            take = min(r, length)
            out[dest] += take
            r -= take
            if r == 0:
                last = dest
                break
        return out, last

    def symbol(self, v: int, index: int) -> int:
        if index < 1:
            raise ValueError("Stack positions are one-based")
        _, last = self.prefix(v, index)
        assert last is not None
        return last


def simulate(net: Network, initial: tuple[int, ...], high: bool = False
             ) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    """Direct deterministic simulation with exact finite-state cycle detection."""
    if len(initial) != net.n or any(x < 0 for x in initial):
        raise ValueError("Invalid initial chip vector")
    chips = list(initial)
    odometer = [0] * net.n
    outputs = [0] * net.sinks
    seen: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    while any(chips):
        key = (tuple(chips), tuple(odometer[v] % net.length(v)
                                 for v in range(net.n)))
        if key in seen:
            return None
        seen.add(key)
        active = [v for v, amount in enumerate(chips) if amount]
        v = active[-1] if high else active[0]
        odometer[v] += 1
        dest = net.symbol(v, odometer[v])
        chips[v] -= 1
        if dest < net.n:
            chips[dest] += 1
        else:
            outputs[dest - net.n] += 1
    return tuple(odometer), tuple(outputs)


def forest_heights(last: list[int | None], n: int) -> list[int] | None:
    """Canonical distances; return None precisely when selected edges cycle."""
    heights = [0] * n
    done = {v for v in range(n) if last[v] is None}
    for start in range(n):
        if start in done:
            continue
        path: list[int] = []
        on_path: set[int] = set()
        current = start
        while current < n and current not in done:
            if current in on_path:
                return None
            on_path.add(current)
            path.append(current)
            successor = last[current]
            assert successor is not None
            current = successor
        height = heights[current] if current < n else 0
        for v in reversed(path):
            height += 1
            heights[v] = height
            done.add(v)
    return heights


def rle_witness(net: Network, u: tuple[int, ...]) -> dict[str, int] | None:
    """Canonical candidate coordinates; feasibility is checked separately."""
    if len(u) != net.n or any(t < 0 for t in u):
        raise ValueError("Invalid candidate odometer")
    w: dict[str, int] = {}
    lasts: list[int | None] = []
    outputs = [0] * net.sinks
    for v, count in enumerate(u):
        w[f"u:{v}"] = count
        w[f"z:{v}"] = int(count > 0)
        q, rem = divmod(count - 1, net.length(v)) if count else (0, -1)
        rem += 1
        w[f"q:{v}"] = q
        selected = False
        for j, (dest, length) in enumerate(net.periods[v]):
            b = t = 0
            if rem > 0 and not selected:
                if rem <= length:
                    b, t, selected = 1, rem, True
                else:
                    rem -= length
            w[f"b:{v}:{j}"] = b
            w[f"t:{v}:{j}"] = t
            w[f"alpha:{v}:{j}"] = t - b
            w[f"beta:{v}:{j}"] = length * b - t
        counts, last = net.prefix(v, count)
        lasts.append(last)
        for s in range(net.sinks):
            outputs[s] += counts[net.n + s]
    heights = forest_heights(lasts, net.n)
    if heights is None:
        return None
    for v, height in enumerate(heights):
        w[f"h:{v}"] = height
    for s, value in enumerate(outputs):
        w[f"y:{s}"] = value
    assert len(w) == 4 * net.n + 4 * net.m + net.sinks
    assert all(isinstance(value, int) and value >= 0 for value in w.values())
    return w


def rle_residuals(net: Network, x: tuple[int, ...], w: dict[str, int]
                  ) -> list[int]:
    """Evaluate the 6n+2m+s signed, degree-at-most-two residuals verbatim."""
    if any(type(value) is not int or value < 0 for value in w.values()):
        raise ValueError("Witness coordinates must be natural integers")
    flows = [[0] * (net.n + net.sinks) for _ in range(net.n)]
    residuals: list[int] = []
    for v, blocks in enumerate(net.periods):
        q, z, u, h = (w[f"{name}:{v}"] for name in ("q", "z", "u", "h"))
        prefix = [0] * (net.n + net.sinks)
        phase_sum = selected_sum = successor_height = 0
        for j, (dest, length) in enumerate(blocks):
            b, t, alpha, beta = (w[f"{name}:{v}:{j}"]
                                 for name in ("b", "t", "alpha", "beta"))
            selected_sum += b
            phase_sum += sum(prefix) * b + t
            for target in range(net.n + net.sinks):
                flows[v][target] += prefix[target] * b
            flows[v][dest] += t + length * q
            if dest < net.n:
                successor_height += b * w[f"h:{dest}"]
            residuals.extend([t - b - alpha, t + beta - length * b])
            prefix[dest] += length
        residuals.extend([z * (z - 1), selected_sum - z, q * (1 - z),
                          u - net.length(v) * q - phase_sum,
                          h - z - successor_height])
    for v in range(net.n):
        residuals.append(w[f"u:{v}"] - x[v] - sum(flows[a][v]
                                                     for a in range(net.n)))
    for s in range(net.sinks):
        residuals.append(w[f"y:{s}"] - sum(flows[v][net.n + s]
                                             for v in range(net.n)))
    assert len(residuals) == 6 * net.n + 2 * net.m + net.sinks
    return residuals


def balanced(net: Network, x: tuple[int, ...], u: tuple[int, ...]) -> bool:
    incoming = [0] * net.n
    for v in range(net.n):
        counts, _ = net.prefix(v, u[v])
        for dest in range(net.n):
            incoming[dest] += counts[dest]
    return all(u[v] == x[v] + incoming[v] for v in range(net.n))


# Straight-line grammar nodes: ('T', destination) or ('C', left_index, right_index).
Node = tuple


def grammar_metadata(nodes: tuple[Node, ...], alphabet: int
                     ) -> tuple[list[int], list[list[int]]]:
    lengths: list[int] = []
    counts: list[list[int]] = []
    for index, node in enumerate(nodes):
        if node[0] == "T":
            dest = node[1]
            if not 0 <= dest < alphabet:
                raise ValueError("Invalid terminal")
            lengths.append(1)
            vec = [0] * alphabet
            vec[dest] = 1
            counts.append(vec)
        elif node[0] == "C":
            left, right = node[1:]
            if not (0 <= left < index and 0 <= right < index):
                raise ValueError("Grammar must be in child-before-parent order")
            lengths.append(lengths[left] + lengths[right])
            counts.append([a + b for a, b in zip(counts[left], counts[right])])
        else:
            raise ValueError("Unknown node kind")
    if not nodes:
        raise ValueError("Empty grammar")
    return lengths, counts


def grammar_expand(nodes: tuple[Node, ...]) -> tuple[int, ...]:
    words: list[tuple[int, ...]] = []
    for node in nodes:
        words.append((node[1],) if node[0] == "T"
                     else words[node[1]] + words[node[2]])
    return words[-1]


def grammar_witness(nodes: tuple[Node, ...], alphabet: int, prefix: int
                    ) -> dict[str, int]:
    lengths, _ = grammar_metadata(nodes, alphabet)
    if not 0 <= prefix <= lengths[-1]:
        raise ValueError("Prefix is outside the period")
    w: dict[str, int] = {}
    for a, node in enumerate(nodes):
        for name in ("a", "k", "eta", "theta"):
            w[f"{name}:{a}"] = 0
        if node[0] == "C":
            for name in ("l", "r", "sigma", "tau"):
                w[f"{name}:{a}"] = 0
    if prefix:
        a, offset = len(nodes) - 1, prefix
        while True:
            w[f"a:{a}"], w[f"k:{a}"] = 1, offset
            w[f"eta:{a}"] = offset - 1
            w[f"theta:{a}"] = lengths[a] - offset
            node = nodes[a]
            if node[0] == "T":
                break
            left, right = node[1:]
            if offset <= lengths[left]:
                w[f"l:{a}"] = 1
                w[f"sigma:{a}"] = lengths[left] - offset
                a = left
            else:
                w[f"r:{a}"] = 1
                w[f"tau:{a}"] = offset - lengths[left] - 1
                offset -= lengths[left]
                a = right
    return w


def grammar_residuals(nodes: tuple[Node, ...], alphabet: int, prefix: int,
                      w: dict[str, int]) -> tuple[list[int], list[int], int | None]:
    lengths, counts = grammar_metadata(nodes, alphabet)
    active_in = [0] * len(nodes)
    offset_in = [0] * len(nodes)
    flow = [0] * alphabet
    selected_terminals: list[int] = []
    residuals: list[int] = []
    for a, node in enumerate(nodes):
        active, k, eta, theta = (w[f"{name}:{a}"]
                                 for name in ("a", "k", "eta", "theta"))
        residuals.extend([active * (active - 1), k - active - eta,
                          k + theta - lengths[a] * active])
        if node[0] == "T":
            flow[node[1]] += active
            if active:
                selected_terminals.append(node[1])
        else:
            left, right = node[1:]
            l, r, sigma, tau = (w[f"{name}:{a}"]
                                for name in ("l", "r", "sigma", "tau"))
            residuals.extend([l + r - active,
                              sigma - l * (lengths[left] - k),
                              tau - r * (k - lengths[left] - 1)])
            active_in[left] += l
            active_in[right] += r
            offset_in[left] += l * k
            offset_in[right] += r * (k - lengths[left])
            for target in range(alphabet):
                flow[target] += r * counts[left][target]
    for a in range(len(nodes) - 1):
        residuals.extend([w[f"a:{a}"] - active_in[a],
                          w[f"k:{a}"] - offset_in[a]])
    root = len(nodes) - 1
    residuals.extend([w[f"a:{root}"] - int(prefix > 0),
                      w[f"k:{root}"] - prefix])
    last = selected_terminals[0] if len(selected_terminals) == 1 else None
    return residuals, flow, last


def bounded_rank(k: int, initial: int, step: Callable[[int], int],
                 halted: Callable[[int], bool]) -> int:
    """Exponentially dilated clock, instantiated here with a toy machine.

    P_x(k)=1 iff the machine halts within floor(log2(k)) steps (P_x(0)=0).
    Hence a first halt at T makes the unique sink symbol occur at 2**T.
    The article proves the general construction for a fixed universal TM.
    """
    if k < 0:
        raise ValueError("Negative prefix")
    if k == 0:
        return 0
    state = initial
    budget = k.bit_length() - 1
    for t in range(budget + 1):
        if halted(state):
            return 1
        if t < budget:
            state = step(state)
    return 0


def run_tests() -> dict:
    result: dict = {"arithmetic": "exact Python integers", "seed": 20260930,
                    "formal_proof_assistant_checked": False}
    network_cases = candidate_cases = balanced_cases = roots = mutations = 0
    max_halting_time = 0
    # All two-vertex, one-sink, length-two switching networks, including repeats.
    for destinations in itertools.product(range(3), repeat=4):
        net = Network((((destinations[0], 1), (destinations[1], 1)),
                       ((destinations[2], 1), (destinations[3], 1))), 1)
        for initial in itertools.product(range(3), repeat=2):
            network_cases += 1
            outcome = simulate(net, initial)
            assert simulate(net, initial, high=True) == outcome
            if outcome is not None:
                u, y = outcome
                max_halting_time = max(max_halting_time, sum(u))
                w = rle_witness(net, u)
                assert w is not None and not any(rle_residuals(net, initial, w))
                assert tuple(w[f"y:{s}"] for s in range(net.sinks)) == y
                for key in w:
                    bad = w.copy()
                    bad[key] += 1
                    assert any(rle_residuals(net, initial, bad))
                    mutations += 1
            for u in itertools.product(range(13), repeat=2):
                candidate_cases += 1
                if not balanced(net, initial, u):
                    continue
                balanced_cases += 1
                w = rle_witness(net, u)
                accepts = w is not None and not any(rle_residuals(net, initial, w))
                assert accepts == (outcome is not None and outcome[0] == u)
                roots += int(accepts)
    result["exhaustive_rle"] = {
        "networks": 81, "initial_vectors_per_network": 9,
        "network_input_pairs": network_cases,
        "odometer_candidates_in_0_through_12_squared": candidate_cases,
        "balanced_candidates": balanced_cases, "accepted_candidates": roots,
        "single_coordinate_plus_one_mutations_rejected": mutations,
        "maximum_observed_halting_time": max_halting_time,
        "schedules_compared": "smallest versus largest active index"}

    rng = random.Random(20260930)
    prefix_tests = random_halts = 0
    for _ in range(200):
        n, sinks = 3, 2
        # Last block is a real sink, so every active vertex can reach a sink.
        periods = tuple(tuple([(rng.randrange(n + sinks), rng.randrange(1, 6))
                               for _ in range(rng.randrange(1, 5))]
                              + [(n + rng.randrange(sinks), rng.randrange(1, 6))])
                        for _ in range(n))
        net = Network(periods, sinks)
        initial = tuple(rng.randrange(4) for _ in range(n))
        outcome = simulate(net, initial)
        assert outcome is not None and simulate(net, initial, True) == outcome
        w = rle_witness(net, outcome[0])
        assert w is not None and not any(rle_residuals(net, initial, w))
        random_halts += 1
        for v in range(n):
            word = tuple(dest for dest, length in periods[v] for _ in range(length))
            for k in range(2 * len(word) + 1):
                counts, last = net.prefix(v, k)
                expanded = [word[i % len(word)] for i in range(k)]
                assert counts == [expanded.count(a) for a in range(n + sinks)]
                assert last == (expanded[-1] if expanded else None)
                prefix_tests += 1
    result["random_rle"] = {"halting_networks": random_halts,
                             "expanded_prefix_crosschecks": prefix_tests}

    big = 1 << 4096
    net = Network((((0, big), (1, 1)),), 1)
    u = (big * (big + 1),)
    w = rle_witness(net, u)
    assert w is not None
    residuals = rle_residuals(net, (big,), w)
    assert sum(r * r for r in residuals) == 0
    result["huge_exact_example"] = {
        "L_and_M": "2^4096", "firing_count": "2^8192 + 2^4096",
        "firing_count_bit_length": u[0].bit_length(),
        "natural_witness_variables": len(w), "quadratic_residuals": len(residuals),
        "sum_of_squared_residuals": 0,
        "execution_simulated": False}

    grammar_tests = grammar_mutations = 0
    for _ in range(150):
        nodes: list[Node] = [("T", a) for a in range(3)]
        for a in range(3, rng.randrange(5, 11)):
            nodes.append(("C", rng.randrange(a), rng.randrange(a)))
        grammar = tuple(nodes)
        expanded = grammar_expand(grammar)
        for k in range(len(expanded) + 1):
            witness = grammar_witness(grammar, 3, k)
            residuals, flow, last = grammar_residuals(grammar, 3, k, witness)
            assert not any(residuals)
            assert flow == [expanded[:k].count(a) for a in range(3)]
            assert last == (expanded[k - 1] if k else None)
            grammar_tests += 1
            for key in witness:
                bad = witness.copy()
                bad[key] += 1
                assert any(grammar_residuals(grammar, 3, k, bad)[0])
                grammar_mutations += 1
    # Exponential grammar sharing, never expanded.
    huge_nodes: list[Node] = [("T", 0), ("T", 1), ("C", 0, 1)]
    for _ in range(1024):
        a = len(huge_nodes) - 1
        huge_nodes.append(("C", a, a))
    huge_grammar = tuple(huge_nodes)
    length = 1 << 1025
    for k in (0, 1, 2, length // 2 + 1, length - 1, length):
        witness = grammar_witness(huge_grammar, 2, k)
        residuals, flow, last = grammar_residuals(huge_grammar, 2, k, witness)
        assert not any(residuals)
        assert flow == [(k + 1) // 2, k // 2]
        assert last == (None if not k else (k - 1) % 2)
    result["grammar"] = {"small_grammars": 150, "prefix_crosschecks": grammar_tests,
        "single_coordinate_plus_one_mutations_rejected": grammar_mutations,
        "unexpanded_large_grammar_nodes": len(huge_grammar),
        "unexpanded_large_period_length": "2^1025", "large_prefix_checks": 6}

    rank_tests = 0
    for t in range(21):
        h = 1 << t
        for k in (0, 1, h - 1, h, h + 1, 2 * h):
            assert bounded_rank(k, t, lambda state: state - 1,
                                lambda state: state == 0) == int(k >= h)
            rank_tests += 1
        assert h.bit_length() >= t + 1
    for bits in range(1, 80):
        assert bounded_rank((1 << bits) - 1, 1, lambda state: state,
                            lambda state: state == 0) == 0
        rank_tests += 1
    result["universal_boundary_mechanism"] = {
        "toy_countdown_and_loop_checks": rank_tests,
        "note": "Checks the dilated-clock rank mechanism, not a universal-machine proof."}
    result["status"] = "PASS"
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("test_results.json"))
    args = parser.parse_args()
    result = run_tests()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
