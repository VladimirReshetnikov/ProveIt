"""Run the exact finite examples shipped with the OCiPRA report."""

from __future__ import annotations

import json
from fractions import Fraction
from math import floor
from pathlib import Path

from ocipra import (
    ContractDAG,
    DeterministicNode,
    FiniteCloudSystem,
    TheoremProfile,
    classify_profile,
    json_value,
    least_bounded,
    monotone_closure,
)


def deterministic_demo() -> dict:
    add = DeterministicNode(
        name="sum",
        dependencies=("x", "y"),
        demand=lambda p: {"x": p + 1, "y": p + 1},
        evaluate=lambda d, _p: d["x"] + d["y"],
        verify=lambda d, _p, out: out == d["x"] + d["y"],
        description="exact addition with a conservative one-bit demand margin",
    )
    square = DeterministicNode(
        name="square",
        dependencies=("sum",),
        demand=lambda p: {"sum": p + 2},
        evaluate=lambda d, _p: d["sum"] * d["sum"],
        verify=lambda d, _p, out: out == d["sum"] ** 2,
    )
    finish = DeterministicNode(
        name="out",
        dependencies=("square", "x"),
        demand=lambda p: {"square": p + 1, "x": p + 1},
        evaluate=lambda d, _p: d["square"] + d["x"],
        verify=lambda d, _p, out: out == d["square"] + d["x"],
    )
    dag = ContractDAG([add, square, finish], external_inputs={"x", "y"})
    run = dag.run({"x": 3, "y": 4}, "out", requested=2)
    return {
        "inputs": {"x": 3, "y": 4},
        "goal": "out",
        "output": run.output,
        "demands": dict(run.demands),
        "trace": [json_value(entry) for entry in run.trace],
        "replay_valid": dag.verify_run({"x": 3, "y": 4}, run),
    }


def cloud_demo() -> dict:
    layers = [
        [Fraction(1), Fraction(2)],
        [Fraction(3, 2), Fraction(4, 3)],
        [Fraction(7, 5), Fraction(17, 12)],
        [Fraction(41, 29), Fraction(99, 70)],
    ]
    cloud = FiniteCloudSystem(
        layers=layers,
        compatible=lambda i, a, b: abs(a - b) <= Fraction(1, 2 ** (i + 1)),
        terminal_good=lambda q: abs(q * q - 2) <= Fraction(1, 100),
    )
    viability = cloud.viability()
    path = cloud.least_path()
    invariant, value = cloud.observable_invariant(floor)
    diameter = cloud.observable_diameter(lambda q: q)
    return {
        "viable_indices": viability.viable_indices,
        "least_path": path,
        "terminal_residual": abs(path[-1] * path[-1] - 2),
        "floor_observable_invariant": invariant,
        "floor_value": value,
        "endpoint_diameter": diameter,
    }


def closure_demo() -> dict:
    def transform(v: tuple[int, int]) -> tuple[int, int]:
        a, b = v
        return min(10, b + 1), min(10, (a + 1) // 2 + 2)

    cert = monotone_closure((2, 1), (10, 10), transform, check_monotone=True)
    return {"steps": cert.steps, "result": cert.result, "verified": cert.verify(transform)}


def search_demo() -> dict:
    cert = least_bounded(lambda n: n * n >= 30, 10)
    return json_value(cert)


def profile_demo() -> dict:
    profiles = [
        TheoremProfile(
            name="fixed finite matrix identity",
            fixed_or_clocked_programs=True,
            primitive_recursive_resource_bound=True,
            bounded_decidable_verifier=True,
            object_local_derivations=True,
            producer_supplied_or_proved=True,
        ),
        TheoremProfile(
            name="Faltings-style finite-point verifier without a height producer",
            fixed_or_clocked_programs=True,
            primitive_recursive_resource_bound=True,
            bounded_decidable_verifier=True,
            object_local_derivations=True,
            producer_supplied_or_proved=False,
            finiteness_used=True,
            height_or_complete_list_supplied=False,
        ),
        TheoremProfile(
            name="exact root label through a collision",
            fixed_or_clocked_programs=True,
            primitive_recursive_resource_bound=True,
            bounded_decidable_verifier=True,
            object_local_derivations=True,
            producer_supplied_or_proved=True,
            exact_selector_requested=True,
            collisions_possible=True,
            separation_gap_supplied=False,
        ),
    ]
    return {
        p.name: json_value(classify_profile(p))
        for p in profiles
    }


def main() -> None:
    result = {
        "bounded_search": search_demo(),
        "demand_closure": closure_demo(),
        "deterministic_dag": deterministic_demo(),
        "relational_cloud": cloud_demo(),
        "admissibility": profile_demo(),
    }
    text = json.dumps(json_value(result), indent=2, sort_keys=True)
    print(text)
    out = Path(__file__).resolve().parents[1] / "validation" / "demo_output.json"
    out.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
