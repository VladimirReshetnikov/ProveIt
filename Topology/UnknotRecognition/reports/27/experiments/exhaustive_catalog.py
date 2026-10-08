#!/usr/bin/env python3
"""Exhaust a finite catalog of three-site strongly local rewrite systems.

Catalog:
* three Boolean sites;
* all 27 one-bit involutions whose guard assigns 0/1/absent to each of the
  other two sites (the footprint is target plus guarded sites);
* every three-element move set from those 27 templates;
* every one of the 26 nonempty local bit-pattern terminal predicates;
* all eight initial states;
* unrestricted and birth-front searches through depth four by default.

This is a finite software validation, not a proof about all rewrite systems or
about knot diagrams.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from itertools import combinations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from prototype.causal_search import (  # noqa: E402
    BooleanLocalSystem,
    Move,
    Reduction,
    birth_front_unlock,
    birth_number,
    dependency_graph,
    frontload_births,
    graph_connected,
    replay,
    shortest_unlock_bfs,
    truncate_at_first_reduction,
)


def move_templates(n_sites: int = 3) -> tuple[Move, ...]:
    moves: list[Move] = []
    for target in range(n_sites):
        others = [site for site in range(n_sites) if site != target]
        for choices in product((-1, 0, 1), repeat=len(others)):
            guard = tuple(
                (site, value)
                for site, value in zip(others, choices)
                if value >= 0
            )
            support = frozenset({target, *(site for site, _ in guard)})
            code = "".join("x" if value < 0 else str(value) for value in choices)
            moves.append(
                Move(
                    f"t{target}_{code}",
                    support,
                    frozenset({target}),
                    guard,
                )
            )
    return tuple(moves)


def reduction_templates(n_sites: int = 3) -> tuple[Reduction, ...]:
    reductions: list[Reduction] = []
    for choices in product((-1, 0, 1), repeat=n_sites):
        if all(value < 0 for value in choices):
            continue
        required = tuple(
            (site, value) for site, value in enumerate(choices) if value >= 0
        )
        support = frozenset(site for site, _ in required)
        code = "".join("x" if value < 0 else str(value) for value in choices)
        reductions.append(Reduction(f"r_{code}", support, required))
    return tuple(reductions)


def run(depth: int, moves_per_system: int) -> dict:
    moves = move_templates()
    reductions = reduction_templates()
    counts = {
        "instances": 0,
        "initially_reducible": 0,
        "no_witness_within_depth": 0,
        "witnessed": 0,
        "frontload_failures": 0,
        "normal_form_completeness_failures": 0,
        "shortest_dependency_disconnects": 0,
    }
    oracle_nodes = 0
    normal_nodes = 0
    started = time.perf_counter()

    for chosen_moves in combinations(moves, moves_per_system):
        for reduction in reductions:
            system = BooleanLocalSystem(3, chosen_moves, (reduction,))
            for initial in range(1 << 3):
                counts["instances"] += 1
                if system.legal_reductions(initial):
                    counts["initially_reducible"] += 1
                    continue

                oracle = shortest_unlock_bfs(system, initial, depth)
                oracle_nodes += oracle.explored_nodes
                if not oracle.found:
                    counts["no_witness_within_depth"] += 1
                    continue

                counts["witnessed"] += 1
                trace = oracle.trace or ()
                front = truncate_at_first_reduction(
                    system, initial, frontload_births(system, trace)
                )
                try:
                    _, reduction_name = replay(
                        system, initial, front, require_first_unlock=True
                    )
                except ValueError:
                    reduction_name = None
                if reduction_name is None or len(front) > len(trace):
                    counts["frontload_failures"] += 1

                if not graph_connected(
                    dependency_graph(
                        system,
                        trace,
                        oracle.reduction or reduction.name,
                    )
                ):
                    counts["shortest_dependency_disconnects"] += 1

                births = birth_number(system, trace)
                candidate = birth_front_unlock(
                    system, initial, len(trace), births
                )
                normal_nodes += candidate.explored_nodes
                if not candidate.found or len(candidate.trace or ()) > len(trace):
                    counts["normal_form_completeness_failures"] += 1

    return {
        "scope": (
            "Exhaustive software validation for the stated finite three-site "
            "catalog; not a proof and not a knot-diagram test."
        ),
        "parameters": {
            "sites": 3,
            "move_templates": len(moves),
            "moves_per_system": moves_per_system,
            "move_sets": sum(1 for _ in combinations(moves, moves_per_system)),
            "terminal_predicates": len(reductions),
            "initial_states": 8,
            "depth": depth,
        },
        "counts": counts,
        "search_nodes": {
            "unrestricted_bfs": oracle_nodes,
            "birth_front": normal_nodes,
        },
        "elapsed_seconds_observed": time.perf_counter() - started,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--moves-per-system", type=int, default=3)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results" / "exhaustive_catalog.json",
    )
    args = parser.parse_args()
    if args.depth < 1:
        raise SystemExit("--depth must be positive")
    if not 1 <= args.moves_per_system <= 27:
        raise SystemExit("--moves-per-system must lie in 1..27")

    payload = run(args.depth, args.moves_per_system)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(payload["counts"], sort_keys=True))
    bad = (
        payload["counts"]["frontload_failures"]
        + payload["counts"]["normal_form_completeness_failures"]
        + payload["counts"]["shortest_dependency_disconnects"]
    )
    if bad:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
