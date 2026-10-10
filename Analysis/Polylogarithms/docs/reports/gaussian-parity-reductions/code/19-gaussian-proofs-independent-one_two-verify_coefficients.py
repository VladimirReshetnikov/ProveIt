"""Cross-check all exported rational coefficient rows against quadrature."""

import argparse
import json
from pathlib import Path

import mpmath as mp

from one_two_identities import one_two_quadrature


def evaluate_row(row, atoms):
    answer = mp.mpf(0)
    for term in row["terms"]:
        value = mp.mpf(term["numerator"]) / term["denominator"]
        for name, exponent in term["powers"].items():
            value *= atoms[name] ** exponent
        answer += value
    return answer


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    result_dir=Path(__file__).resolve().parents[3]/"results"/"independent"/"one_two"
    parser.add_argument("--coefficients",type=Path,default=result_dir/"coefficients.json")
    parser.add_argument("--output",type=Path,default=result_dir/"coefficient_verification.json")
    args=parser.parse_args()
    mp.mp.dps = 100
    table = json.loads(args.coefficients.read_text())
    assert len(table["rows"]) == 24
    w = (1 + mp.j) / 2
    atoms = {"ell": mp.log(2), "pi": mp.pi, "G": mp.catalan,
             "zeta_3": mp.zeta(3), "zeta_5": mp.zeta(5)}
    for k in range(3, 7):
        value = mp.polylog(k, w)
        atoms[f"lambda_{k}"] = mp.im(value)
        if k >= 4:
            atoms[f"mu_{k}"] = mp.re(value)
    values = {}
    result = []
    for row in table["rows"]:
        key = (row["a"], row["b"])
        if key not in values:
            values[key] = one_two_quadrature(*key, mp.j)
        lhs = (mp.re if row["component"] == "real" else mp.im)(values[key])
        rhs = evaluate_row(row, atoms)
        result.append({"indices": row["indices"], "component": row["component"],
                       "value": mp.nstr(lhs, 100),
                       "residual": mp.nstr(abs(lhs - rhs), 8)})
    maximum = max(mp.mpf(row["residual"]) for row in result)
    assert maximum < mp.mpf("1e-96")
    report = {"working_decimal_digits": 100,
              "status": "Numerical cross-check, not interval certification",
              "maximum_residual": mp.nstr(maximum, 8), "rows": result}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(
        json.dumps(report, indent=2) + "\n")
    print(f"Checked {len(result)} exported real/imaginary rows; "
          f"maximum residual {mp.nstr(maximum, 8)}")


if __name__ == "__main__":
    main()
