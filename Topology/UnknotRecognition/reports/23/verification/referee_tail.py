"""Independent finite-chain checks of tail endpoints, Euler, and dominance.

This verifier uses the maintained explicit macro builder, not any internal
helpers of the proposed tail implementation.  Homological ranks are reduced
over F_2, with quantum grading forgotten.
"""
from __future__ import annotations

import json
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "implementation" / "fast"))
from fastunknot.twist.core import (  # noqa: E402
    Run, Budget, _Meter, _rank, build_complex, components,
    verify_d_squared,
)


def inspect(strands, context, selected, generator, sign, magnitude):
    runs = list(context)
    runs.insert(selected, Run(generator, sign * magnitude))
    meter = _Meter(Budget(max_states=2_000_000, max_basis=2_000_000,
                          max_matrix_bits=3_000_000_000,
                          max_xors=200_000_000))
    c = build_complex(strands, runs, meter=meter)
    verify_d_squared(c, meter)
    ranks = {h: _rank(cols, meter) for h, cols in c.columns.items()}
    betti = {h: d - ranks.get(h-1, 0) - ranks.get(h, 0)
             for h, d in c.dimensions.items()}
    assert min(betti.values()) >= 0
    rank = sum(betti.values())
    euler = sum((-1 if h % 2 else 1) * d
                for h, d in c.dimensions.items())
    number = components(strands, runs)
    assert euler == 1 << (number - 1), (runs, euler, number)
    return c, ranks, {h:d for h,d in betti.items() if d}, rank, number


def main():
    rng = random.Random(20261008)
    results = []
    for case in range(96):
        strands = rng.randrange(2, 6)
        length = case % 5
        context = [Run(rng.randrange(1, strands), rng.choice([-1, 1]))
                   for _ in range(length)]
        selected = rng.randrange(length + 1)
        generator = rng.randrange(1, strands)
        sign = -1 if case % 2 else 1
        alpha = sum(min(0, sign*r.exponent) for r in context)
        beta = sum(max(0, sign*r.exponent) for r in context)
        values = [inspect(strands, context, selected, generator, sign, m)
                  for m in (length+1, length+2, length+3, length+5)]
        one, cap, three, farther = values
        source_h = beta+1 if sign > 0 else -beta-2
        A = cap[0].columns[source_h]
        width = cap[0].dimensions[source_h]
        assert width == cap[0].dimensions[source_h+1]
        if sign > 0:
            assert three[0].columns[beta+1] == A
            assert three[0].columns[beta+2] == A
        else:
            assert three[0].columns[-beta-2] == A
            assert three[0].columns[-beta-3] == A
        nu = width - 2*cap[1][source_h]
        assert nu >= 0
        assert cap[3] - one[3] == nu
        assert three[3] - cap[3] == nu
        assert farther[3] - cap[3] == 3*nu
        predicted = {h if sign*h <= beta+1 else h+sign*3: d
                     for h,d in cap[2].items()}
        if nu:
            for q in range(beta+2, beta+5):
                h = sign*q
                assert h not in predicted
                predicted[h] = nu
        assert predicted == farther[2], (case, predicted, farther[2])
        for index, magnitude in enumerate((length+1, length+2,
                                          length+3, length+5)):
            if values[index][4] == 1:
                assert nu % 2 == 1
                if magnitude >= length+2:
                    n = magnitude-length-1
                    assert values[index][3] >= n+1+(n % 2)
        results.append({"case":case, "strands":strands,
                        "context": [[r.generator,r.exponent] for r in context],
                        "selected":selected, "generator":generator,
                        "sign":sign, "interior_dimension":width,
                        "interior_rank":cap[1][source_h], "nu":nu,
                        "ranks": [v[3] for v in values],
                        "components": [v[4] for v in values]})
    # Sharpness at the excluded boundary m=L+1, with arbitrary L.
    for length in range(1, 9):
        context=[Run(1,-length)]
        value=inspect(2,context,0,1,1,length+1)
        assert value[3] == 1 and value[4] == 1
    report={"random_cases":len(results), "explicit_complexes":4*len(results)+8,
            "tests":"d_squared; Euler exact; canonical interior equality; "
                    "one-slice endpoint; affine ranks; compact degree profile; "
                    "dominance parity; sharpness boundary",
            "status":"PASS", "seed":20261008, "cases":results}
    output=Path(__file__).with_name("referee_tail_results.json")
    output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k!="cases"},indent=2))


if __name__ == "__main__":
    main()
