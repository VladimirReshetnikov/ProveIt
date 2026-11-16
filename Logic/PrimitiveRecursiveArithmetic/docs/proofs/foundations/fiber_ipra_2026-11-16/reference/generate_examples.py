from fractions import Fraction
import json
from pathlib import Path

from fiber_reference import (
    NetCertificate,
    Quantifier,
    bisection_trace,
    finite_demand_closure,
    master_certificate,
    verify_bounded_strategy,
)

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples"
EXAMPLES.mkdir(exist_ok=True)


def frac(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


capacities = (4, 5, 3)

def demand_step(v: tuple[int, ...]) -> tuple[int, ...]:
    x, y, z = v
    return (min(4, y), min(5, x + 1), min(3, (y + 1) // 2))

closure = finite_demand_closure(capacities, demand_step)
(EXAMPLES / "demand_closure.json").write_text(
    json.dumps(
        {
            "capacities": capacities,
            "history": closure.history,
            "fixed_point": closure.fixed_point,
            "potential_bound": closure.potential_bound,
        },
        indent=2,
    )
    + "\n"
)

bounds = (8, 9, 6)
verifiers = (
    lambda x: x >= 3 and x % 2 == 1,
    lambda x: x * x >= 20,
    lambda x: x == 4,
)
code, witnesses = master_certificate(bounds, verifiers)
(EXAMPLES / "master_certificate.json").write_text(
    json.dumps({"bounds": bounds, "witnesses": witnesses, "code": code}, indent=2)
    + "\n"
)

quantifiers = (
    Quantifier("forall", lambda h: 5),
    Quantifier("exists", lambda h: 6),
)
strategy = {(x,): x + 1 for x in range(5)}
strategy_ok = verify_bounded_strategy(
    quantifiers, strategy, lambda h: h[1] == h[0] + 1
)
(EXAMPLES / "strategy.json").write_text(
    json.dumps(
        {
            "formula": "forall x<5 exists y<6, y=x+1",
            "strategy": {str(list(k)): v for k, v in strategy.items()},
            "verified": strategy_ok,
        },
        indent=2,
    )
    + "\n"
)

poly = lambda x: x * x - 2
trace = bisection_trace(poly, Fraction(1), Fraction(2), 10)
(EXAMPLES / "sqrt2_bisection.json").write_text(
    json.dumps(
        {
            "polynomial": "x^2-2",
            "trace": [[frac(l), frac(r)] for l, r in trace],
            "final_width": frac(trace[-1][1] - trace[-1][0]),
        },
        indent=2,
    )
    + "\n"
)

net = NetCertificate((Fraction(0), Fraction(1, 2), Fraction(1)), Fraction(1, 4))
(EXAMPLES / "finite_net.json").write_text(
    json.dumps(
        {
            "points": [frac(x) for x in net.points],
            "epsilon": frac(net.epsilon),
            "example_function": "x(1-x)",
            "net_point_bound": "1/4",
            "modulus_delta": "1/4",
            "lifted_bound": "1/2",
        },
        indent=2,
    )
    + "\n"
)
