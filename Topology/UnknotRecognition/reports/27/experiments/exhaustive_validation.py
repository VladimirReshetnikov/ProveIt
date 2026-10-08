#!/usr/bin/env python3
"""Deterministic finite validation of the causal-branch search theorem's code.

This is not a proof of the mathematical theorem and is not a test of knot
geometry.  It compares the normal-form search with an unrestricted BFS oracle on
small randomly generated strongly local reversible rewrite systems.
"""
from __future__ import annotations

import argparse
import json
import random
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from prototype.causal_search import (  # noqa: E402
    BooleanLocalSystem,
    Move,
    Reduction,
    accumulated_strict_example,
    birth_front_unlock,
    birth_number,
    branching_example,
    dependency_graph,
    frontload_births,
    graph_connected,
    last_touch_unlock,
    replay,
    shortest_unlock_bfs,
    support_history_example,
    truncate_at_first_reduction,
)


def random_system(rng: random.Random, n_sites: int, n_moves: int, n_reductions: int) -> BooleanLocalSystem:
    moves: list[Move] = []
    for index in range(n_moves):
        target = rng.randrange(n_sites)
        candidates = [site for site in range(n_sites) if site != target]
        rng.shuffle(candidates)
        guard_count = rng.randrange(0, min(3, n_sites))
        guard_sites = candidates[:guard_count]
        guard = tuple(sorted((site, rng.randrange(2)) for site in guard_sites))
        support = frozenset({target, *guard_sites})
        moves.append(Move(f"m{index:02d}", support, frozenset({target}), guard))

    reductions: list[Reduction] = []
    for index in range(n_reductions):
        size = rng.randrange(1, min(4, n_sites + 1))
        sites = sorted(rng.sample(range(n_sites), size))
        required = tuple((site, rng.randrange(2)) for site in sites)
        reductions.append(Reduction(f"r{index}", frozenset(sites), required))
    return BooleanLocalSystem(n_sites, tuple(moves), tuple(reductions))


def validate_hand_examples() -> dict:
    branch_system, branch_initial = branching_example()
    branch_oracle = shortest_unlock_bfs(branch_system, branch_initial, 4)
    branch_one = birth_front_unlock(branch_system, branch_initial, 4, 1)
    branch_two = birth_front_unlock(branch_system, branch_initial, 4, 2)

    strict_system, strict_initial = accumulated_strict_example()
    strict_oracle = shortest_unlock_bfs(strict_system, strict_initial, 4)
    strict_last = last_touch_unlock(strict_system, strict_initial, 4)
    strict_acc = birth_front_unlock(strict_system, strict_initial, 4, 1)

    history_system, history_initial = support_history_example()
    history_oracle = shortest_unlock_bfs(history_system, history_initial, 4)
    history_bounded = birth_front_unlock(history_system, history_initial, 4, 1)

    assert branch_oracle.found and branch_two.found and not branch_one.found
    assert strict_oracle.found and strict_acc.found and not strict_last.found
    assert history_oracle.found and history_bounded.found

    return {
        "two_birth_branch": {
            "oracle_trace": list(branch_oracle.trace or ()),
            "births": birth_number(branch_system, branch_oracle.trace or ()),
            "one_birth_found": branch_one.found,
            "two_birth_found": branch_two.found,
            "dependency_connected": graph_connected(
                dependency_graph(branch_system, branch_two.trace or (), branch_two.reduction or "R")
            ),
        },
        "accumulated_vs_last_touch": {
            "oracle_trace": list(strict_oracle.trace or ()),
            "births": birth_number(strict_system, strict_oracle.trace or ()),
            "last_touch_found": strict_last.found,
            "accumulated_found": strict_acc.found,
            "accumulated_trace": list(strict_acc.trace or ()),
        },
        "support_history_repeat": {
            "oracle_trace": list(history_oracle.trace or ()),
            "oracle_births": birth_number(history_system, history_oracle.trace or ()),
            "one_birth_trace": list(history_bounded.trace or ()),
            "one_birth_found": history_bounded.found,
        },
    }


def run_random(args: argparse.Namespace) -> dict:
    birth_histogram: Counter[int] = Counter()
    depth_histogram: Counter[int] = Counter()
    min_birth_histogram: Counter[int] = Counter()
    oracle_nodes = 0
    normal_nodes = 0
    initial_terminal = 0
    no_witness = 0
    witnessed = 0
    frontload_failures = 0
    completeness_failures = 0
    dependency_disconnects = 0
    shorter_after_frontload = 0
    examples: list[dict] = []

    for seed in range(args.seed_start, args.seed_start + args.systems):
        rng = random.Random(seed)
        system = random_system(rng, args.sites, args.moves, args.reductions)
        initial = rng.randrange(1 << args.sites)
        if system.legal_reductions(initial):
            initial_terminal += 1
            continue

        oracle = shortest_unlock_bfs(system, initial, args.depth)
        oracle_nodes += oracle.explored_nodes
        if not oracle.found:
            no_witness += 1
            continue

        witnessed += 1
        trace = oracle.trace or ()
        births = birth_number(system, trace)
        birth_histogram[births] += 1
        depth_histogram[len(trace)] += 1

        front = truncate_at_first_reduction(system, initial, frontload_births(system, trace))
        try:
            _, reduction = replay(system, initial, front, require_first_unlock=True)
        except ValueError:
            frontload_failures += 1
            continue
        if reduction is None or len(front) > len(trace):
            frontload_failures += 1
            continue
        if len(front) < len(trace):
            shorter_after_frontload += 1

        if oracle.reduction is not None:
            graph = dependency_graph(system, trace, oracle.reduction)
            if not graph_connected(graph):
                dependency_disconnects += 1

        minimum = None
        found_result = None
        for bound in range(1, births + 1):
            candidate = birth_front_unlock(system, initial, len(trace), bound)
            normal_nodes += candidate.explored_nodes
            if candidate.found:
                minimum = bound
                found_result = candidate
                break
        if minimum is None or found_result is None:
            completeness_failures += 1
            if len(examples) < 10:
                examples.append(
                    {
                        "seed": seed,
                        "oracle_trace": list(trace),
                        "births": births,
                        "initial": initial,
                    }
                )
            continue
        min_birth_histogram[minimum] += 1
        if len(found_result.trace or ()) > len(trace):
            completeness_failures += 1

    return {
        "parameters": {
            "seed_start": args.seed_start,
            "systems": args.systems,
            "sites": args.sites,
            "moves": args.moves,
            "reductions": args.reductions,
            "depth": args.depth,
        },
        "counts": {
            "initially_reducible": initial_terminal,
            "no_witness_within_depth": no_witness,
            "witnessed": witnessed,
            "frontload_failures": frontload_failures,
            "normal_form_completeness_failures": completeness_failures,
            "shorter_after_frontload": shorter_after_frontload,
            "shortest_dependency_disconnects": dependency_disconnects,
        },
        "histograms": {
            "oracle_birth_number": dict(sorted(birth_histogram.items())),
            "minimum_birth_bound_found": dict(sorted(min_birth_histogram.items())),
            "oracle_depth": dict(sorted(depth_histogram.items())),
        },
        "search_nodes": {
            "unrestricted_bfs": oracle_nodes,
            "normal_form_iterative": normal_nodes,
        },
        "failure_examples": examples,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--systems", type=int, default=5000)
    parser.add_argument("--seed-start", type=int, default=0)
    parser.add_argument("--sites", type=int, default=6)
    parser.add_argument("--moves", type=int, default=9)
    parser.add_argument("--reductions", type=int, default=3)
    parser.add_argument("--depth", type=int, default=6)
    parser.add_argument("--output", type=Path, default=ROOT / "results" / "validation.json")
    args = parser.parse_args()

    payload = {
        "scope": (
            "Finite software validation for abstract Boolean local systems; "
            "not a proof and not a ProveIt knot-diagram regression run."
        ),
        "hand_examples": validate_hand_examples(),
        "random_validation": run_random(args),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload["random_validation"]["counts"], sort_keys=True))
    if payload["random_validation"]["counts"]["frontload_failures"]:
        raise SystemExit(1)
    if payload["random_validation"]["counts"]["normal_form_completeness_failures"]:
        raise SystemExit(1)
    if payload["random_validation"]["counts"]["shortest_dependency_disconnects"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
