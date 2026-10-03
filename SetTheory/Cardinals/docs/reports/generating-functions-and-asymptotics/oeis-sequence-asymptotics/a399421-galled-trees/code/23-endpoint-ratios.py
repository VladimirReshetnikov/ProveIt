"""Exact-count/approximation ratios at n=40,80,120,160.

Leading includes exp(beta*d^2/n); corrections are additive multipliers
1+C1(lambda)/sqrt(n) and 1+C1(lambda)/sqrt(n)+C2(lambda)/n.
The C2 term is NOT exponentiated. Finite-size results do not certify an error
bound, monotonic improvement, or the accuracy of a threshold inversion.
"""
import argparse
import csv
import io
import json
import math
from pathlib import Path
import mpmath as mp
from triangle import endpoint_coefficient


def ratio_table(rows, constants):
    with mp.workdps(70):
        c = {key: mp.mpf(value) for key, value in constants.items()}
        result = []
        for n in (40, 80, 120, 160):
            for target in (0.5, 1.0, 1.5, 2.0):
                d = round(target*math.sqrt(n))
                if (n-d) % 2 != 1:
                    d += 1
                k = (n-d-1)//2
                lam = mp.mpf(d)/mp.sqrt(n)
                exact = endpoint_coefficient(rows, n, d)
                leading = 2*c['h0']*c['r0']**(-n)*mp.mpf(n)**(-mp.mpf('1.5')) \
                    *(c['a']*n)**d/mp.factorial(d)*mp.exp(c['beta']*lam**2)
                C1 = c['A']*lam+c['B']*lam**3
                C2 = c['kappa']+c['C22']*lam**2+c['C24']*lam**4+c['C26']*lam**6
                first_factor = 1+C1/mp.sqrt(n)
                second_factor = first_factor+C2/n
                entry = dict(n=n, target_lambda=target, d=d, k=k, exact=str(exact))
                values = dict(actual_lambda=lam, leading=leading,
                              first_correction_factor=first_factor,
                              second_correction_factor=second_factor,
                              ratio_leading=exact/leading,
                              ratio_C1=exact/(leading*first_factor),
                              ratio_C2=exact/(leading*second_factor))
                entry.update({key: mp.nstr(value, 18) for key, value in values.items()})
                result.append(entry)
        return {
            "numerical_status": "non-interval numerical comparison; display at most 12 significant digits",
            "rounding_rule": "round target_lambda*sqrt(n) to nearest integer (ties to even), then increment if n-d is even",
            "leading_definition": "2*h0*r0^(-n)*n^(-3/2)*(a*n)^d/d!*exp(beta*d^2/n)",
            "C1_definition": "A*lambda+B*lambda^3",
            "C2_definition": "kappa+C22*lambda^2+C24*lambda^4+C26*lambda^6",
            "ratios": result,
        }


def as_csv(table):
    out = io.StringIO()
    writer = csv.DictWriter(out, fieldnames=list(table['ratios'][0]), lineterminator="\n")
    writer.writeheader()
    writer.writerows(table['ratios'])
    return out.getvalue()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parents[1]
    parser.add_argument("--triangle", type=Path, default=root/'data/triangle-160.json')
    parser.add_argument("--constants", type=Path, default=root/'data/constants-320.json')
    parser.add_argument("--output", type=Path)
    parser.add_argument("--csv", type=Path)
    args = parser.parse_args()
    table = ratio_table(json.loads(args.triangle.read_text())['rows'],
                        json.loads(args.constants.read_text())['constants'])
    output = json.dumps(table, indent=2)+"\n"
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end="")
    if args.csv:
        args.csv.write_text(as_csv(table))


if __name__ == "__main__":
    main()
