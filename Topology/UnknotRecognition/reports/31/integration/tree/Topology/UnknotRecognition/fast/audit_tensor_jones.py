"""Independent cube and discrete-turning audit for the full tensor polynomial."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import sys

from fastunknot import Diagram
from fastunknot.tensor_jones import rotation_cochain, tensor_jones
from fastunknot.separator_order import verify_width_bounded_order
from check_potts_independent import laurent_jones

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/"tests"))
from test_tensor_jones import diagrams, independent_turning_numbers, coefficients


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(2643)
    cases = [(f"random-{i}", d.pd) for i, (d, _) in enumerate(diagrams(100, 2644))]
    for name in ("trefoil", "conway", "kinoshita_terasaka", "hard_unknot_8"):
        d = Diagram.from_json(json.loads((ROOT/"examples"/(name+".json")).read_text()))
        cases.append((name, d.pd))
    cases.append(("empty", []))
    rows, comparisons, circles, smoothings = [], 0, 0, 0
    for name, pd in cases:
        cube = {-e: c for e, c in laurent_jones(Diagram.from_pd(pd)).items()}
        variants = []
        for mirrored in (False, True):
            d = Diagram.from_pd(pd)
            if mirrored:
                d = d.mirror()
            labels = sorted({x for row in d.pd for x in row})
            renamed = dict(zip(labels, rng.sample(range(-1_000_000, 1_000_000), len(labels))))
            shuffled = [tuple(renamed[x] for x in row) for row in d.pd]
            rng.shuffle(shuffled)
            d = Diagram.from_pd(shuffled)
            expected = {-e if mirrored else e: c for e, c in cube.items()}
            order = list(range(d.crossings))
            rng.shuffle(order)
            for outer in (0, len(d.faces())-1 if d.crossings else 0):
                result = tensor_jones(d, order=order, outer_face=outer)
                assert coefficients(result) == expected
                integer_result = tensor_jones(d, order=order, outer_face=outer,
                                               arithmetic="integer")
                assert coefficients(integer_result) == expected
                global_result = tensor_jones(d, order=order, outer_face=outer,
                                             arithmetic="integer-global")
                assert coefficients(global_result) == expected
                if d.crossings:
                    assert verify_width_bounded_order(d.pd, result["order_certificate"])
                comparisons += 3
                turn_count = smoothing_count = 0
                if d.crossings <= 10:
                    beta = rotation_cochain(d, outer_face=outer)
                    for state in range(1 << d.crossings):
                        turns = independent_turning_numbers(d, state, beta)
                        assert all(abs(turn) == 4 for turn in turns)
                        smoothing_count += 1
                        turn_count += len(turns)
                    circles += turn_count
                    smoothings += smoothing_count
                variants.append(dict(mirrored=mirrored, pd=d.pd, supplied_order=order,
                                     outer_face=outer, result=result,
                                     integer_result=integer_result,
                                     global_integer_result=global_result,
                                     circle_rotations_checked=turn_count,
                                     smoothing_states_checked=smoothing_count))
        rows.append(dict(name=name, crossings=len(pd), variants=variants))
    paths = ["audit_tensor_jones.py", "fastunknot/tensor_jones.py",
             "fastunknot/separator_order.py", "tests/test_tensor_jones.py",
             "check_potts_independent.py"]
    result = dict(algorithm="binary-rotation-tensor-v1", seed=2643, input_seed=2644,
                  python=sys.version, platform=platform.platform(),
                  source_sha256={p: sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
                  independent_polynomial_comparisons=comparisons,
                  independent_smoothing_states=smoothings,
                  independent_circle_rotations=circles, rows=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ("independent_polynomial_comparisons",
                     "independent_smoothing_states", "independent_circle_rotations")}))


if __name__ == "__main__":
    main()
