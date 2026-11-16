from __future__ import annotations

import json
from pathlib import Path

from strive_reference import formula_summary, least_demand_closure
from test_strive_reference import FALSE_CHALLENGE, TRUE_CHALLENGE, atom, exists, forall

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples"
EXAMPLES.mkdir(parents=True, exist_ok=True)


def dump(name, payload):
    path = EXAMPLES / name
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


dump(
    "bounded_challenge_success.json",
    {"formula": TRUE_CHALLENGE, "audit": formula_summary(TRUE_CHALLENGE)},
)
dump(
    "bounded_challenge_failure.json",
    {"formula": FALSE_CHALLENGE, "audit": formula_summary(FALSE_CHALLENGE)},
)

ex0 = exists("x", 0, atom(True, "empty existential body"))
all0 = forall("x", 0, atom(False, "empty universal body"))
dump(
    "empty_bounds.json",
    {
        "empty_existential": {"formula": ex0, "audit": formula_summary(ex0)},
        "empty_universal": {"formula": all0, "audit": formula_summary(all0)},
    },
)

caps = (3, 3, 4)


def transfer(d):
    return (max(1, d[1]), min(3, d[0] + 1), max(2, d[0], d[1]))

closure = least_demand_closure((0, 0, 0), caps, transfer)
dump(
    "cyclic_demand_closure.json",
    {
        "capacities": caps,
        "initial": (0, 0, 0),
        "result": closure.value,
        "trace": closure.trace,
        "strict_step_budget": closure.capacity_budget,
        "rules": [
            "d0 >= 1 and d0 >= d1",
            "d1 >= min(3,d0+1)",
            "d2 >= 2,d0,d1",
        ],
    },
)
