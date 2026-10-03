"""Conditional finite-model inversion checks at known exact deficiency.

Refactored from the independently approved check_inversion.py (2 October
2026). These test K=2 model algebra and exact triangle monotonicity. They do
not certify the asymptotic remainder, true-count inverse error, or threshold
rounding at finite n. The parameter d is held fixed under differentiation.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp


def check_inversion(rows, constants):
    with mp.workdps(100):
        v = {key: mp.mpf(value) for key, value in constants.items()}
        L = -mp.log(v['r0'])

        def S(x, d):
            return 1+v['A']*d/x+v['B']*d**3/x**2+v['kappa']/x \
                +v['C22']*d**2/x**2+v['C24']*d**4/x**3+v['C26']*d**6/x**4

        def S_prime(x, d):
            return -v['A']*d/x**2-2*v['B']*d**3/x**3-v['kappa']/x**2 \
                -2*v['C22']*d**2/x**3-3*v['C24']*d**4/x**4-4*v['C26']*d**6/x**5

        def F(x, d):
            return L*x+(d-mp.mpf('1.5'))*mp.log(x)+v['beta']*d*d/x+mp.log(S(x, d))

        def F_prime(x, d):
            return L+(d-mp.mpf('1.5'))/x-v['beta']*d*d/x**2+S_prime(x, d)/S(x, d)

        cases = []
        for d in (100, 1000, 10000):
            target = mp.mpf(d*d)
            p = d-mp.mpf('1.5')
            Y = F(target, d)
            z = (L/p)*mp.exp(Y/p)
            seed = p/L*mp.lambertw(z, 0)
            carrier_residual = abs(L*seed+p*mp.log(seed)-Y)
            assert carrier_residual < mp.mpf('1e-85')
            # Equivalent logarithmic carrier evaluation avoids forming exp(Y/p).
            log_argument = mp.log(L/p)+Y/p
            w_guess = log_argument-mp.log(log_argument)
            w = mp.findroot(lambda value: value+mp.log(value)-log_argument, w_guess)
            logarithmic_seed = p*w/L
            assert abs(seed-logarithmic_seed) < mp.mpf('1e-85')
            derivative_error = abs(F_prime(seed, d)-mp.diff(lambda x: F(x, d), seed))
            assert derivative_error < mp.mpf('1e-90')
            x1 = seed-(F(seed, d)-Y)/F_prime(seed, d)
            x2 = x1-(F(x1, d)-Y)/F_prime(x1, d)
            assert abs(x2-target) < abs(x1-target) < abs(seed-target)
            cases.append({
                "d": d, "exact_model_root": str(d*d), "lambda": "1",
                "seed_error": mp.nstr(seed-target, 30),
                "newton1_error_times_x^1.5": mp.nstr((x1-target)*target**mp.mpf('1.5'), 30),
                "newton2_error_times_x^4.5": mp.nstr((x2-target)*target**mp.mpf('4.5'), 30),
                "carrier_absolute_residual": mp.nstr(carrier_residual, 8),
                "fixed_d_derivative_absolute_residual": mp.nstr(derivative_error, 8),
                "newton2_model_absolute_residual": mp.nstr(abs(F(x2, d)-Y), 12),
            })
        pairs, equalities = 0, []
        for n in range(1, len(rows)-2):
            for k, count in enumerate(rows[n]):
                assert rows[n+2][k+1] >= count
                pairs += 1
                if rows[n+2][k+1] == count:
                    equalities.append([n, k])
        assert pairs == 6320
        assert equalities == [[1, 0], [3, 1]]
        return {
            "model_K": 2, "working_decimal_precision": 100,
            "scope": "finite-model numerical checks only; no certified asymptotic inverse or threshold guarantee",
            "model_checks": cases,
            "monotone_triangle_pairs_checked": pairs,
            "monotone_inequality": "g[n+2,k+1] >= g[n,k] (fixed deficiency)",
            "equality_pairs_n_k": equalities,
            "largest_n_in_triangle": len(rows)-1,
        }


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--triangle", type=Path, default=root/'data/triangle-160.json')
    parser.add_argument("--constants", type=Path, default=root/'data/constants-320.json')
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check_inversion(json.loads(args.triangle.read_text())['rows'],
                             json.loads(args.constants.read_text())['constants'])
    output = json.dumps(result, indent=2)+"\n"
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
