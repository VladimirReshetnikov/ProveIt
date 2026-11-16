from __future__ import annotations

import json

from darc_reference import (
    Atom,
    DemandNetwork,
    ExistsBounded,
    ForallBounded,
    ResourceShape,
    ThresholdRule,
    backward_viability,
    build_strategy,
    check_strategy,
    check_trace,
    closure_report,
    run_trace,
)


def main() -> None:
    shape = ResourceShape(
        (
            "query:value",
            "query:witness",
            "cert:branch",
            "cert:trace",
            "precision:root",
            "precision:integral",
            "guard:separation",
            "guard:denominator",
            "residual:tail_modulus",
            "residual:height_bound",
        ),
        (1, 1, 1, 1, 6, 6, 1, 1, 1, 1),
    )
    network = DemandNetwork(
        shape,
        [
            ThresholdRule.make(
                {"query:value": 1},
                {"precision:root": 3},
                "value query seeds root precision",
            ),
            ThresholdRule.make(
                {"query:witness": 1},
                {"cert:branch": 1, "guard:separation": 1},
                "named root requires branch and separation",
            ),
            ThresholdRule.make(
                {"precision:root": 1},
                {"precision:integral": 2, "guard:denominator": 1},
                "root evaluator requests integral precision",
            ),
            ThresholdRule.make(
                {"precision:integral": 2},
                {"precision:root": 5},
                "feedback modulus raises root precision",
            ),
            ThresholdRule.make(
                {"precision:root": 5},
                {"precision:integral": 6, "residual:tail_modulus": 1},
                "high precision exposes a tail modulus",
            ),
            ThresholdRule.make(
                {"cert:trace": 1},
                {"residual:height_bound": 1},
                "public trace would require a height bound",
            ),
        ],
    )
    seed = shape.demand({"query:value": 1})
    demand = closure_report(network, seed)

    parity = Atom("even-sum", lambda e: (e["i"] + e["j"]) % 2 == 0)
    formula = ForallBounded("i", 5, ExistsBounded("j", 4, parity))
    strategy = build_strategy(formula)

    step = lambda s: {"n": s["n"] + 1, "acc": s["acc"] + 2 * s["n"] + 1}
    trace = run_trace({"n": 0, "acc": 0}, step, 5)
    trace_ok = check_trace(trace, step, lambda s: s["acc"] == s["n"] ** 2)

    layers = [list(range(3)), list(range(5)), list(range(7)), list(range(9))]
    relation = backward_viability(layers, lambda i, x, y: y in (x, x + 1), start=1)

    result = {
        "artifact": "DARC-iPRA finite metalevel demonstration",
        "demand_analysis": demand,
        "bounded_strategy": {
            "formula": "forall i<5 exists j<4, i+j is even",
            "certificate": strategy,
            "accepted": check_strategy(formula, strategy),
        },
        "normalized_trace": {
            "invariant": "acc = n^2",
            "states": trace,
            "accepted": trace_ok,
        },
        "relational_viability": {
            "viable_layers": [list(layer) for layer in relation.viable_layers],
            "least_path": list(relation.least_path) if relation.least_path is not None else None,
        },
        "interpretation": {
            "dead_certificates": ["cert:branch", "cert:trace"],
            "exposed_residuals": demand["residuals"],
            "note": "The JSON validates finite compiler analyses only; it is not an iPRA proof.",
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
