"""Run exact, independent consistency checks and regenerate the data files.

No network access or third-party packages. A successful run is computational
verification of the reported finite ranges, not a formal proof of the theorems.
"""

import argparse
import csv
import json
import platform
from pathlib import Path
from time import perf_counter

from secant_periodicity import (
    analyze_modulus, euler_phi, factor_integer, is_prime,
    prime_power_period, secant_mod_odd, secant_numbers,
    secant_numbers_entringer,
)


def check(condition: bool, message: str) -> None:
    # Deliberately not an assert: checks remain active with python -O.
    if not condition:
        raise AssertionError(message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).parent / "data")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    started = perf_counter()
    maximum_index = 2100
    values = secant_numbers_entringer(maximum_index)
    recurrence_values = secant_numbers(100)
    check(values[:101] == recurrence_values, "independent recurrence mismatch")
    check(values[19] == 23489580527043108252017828576198947741,
          "unexpected exact counterexample value")
    check(values[1] % 27 == 1 and values[19] % 27 == 10,
          "counterexample failed")

    moment_checks = 0
    for modulus in range(1, 152, 2):
        for n in range(25):
            check(secant_mod_odd(n, modulus) == values[n] % modulus,
                  "moment formula mismatch: n={}, q={}".format(n, modulus))
            moment_checks += 1

    modulus_checks, period_shift_checks, lower_period_checks = 0, 0, 0
    witnesses = []
    for modulus in range(1, 1001):
        data = analyze_modulus(modulus)
        s, period = data.preperiod, data.period
        check(s + 2 * period <= maximum_index, "insufficient coefficient range")
        check(euler_phi(modulus) % period == 0, "period does not divide phi")
        check(data.pure_from_index_one == all(
            p == 2 or exponent <= 2 for p, exponent in data.factorization
        ), "cube-free classification mismatch")
        for n in range(s, s + period + 1):
            check((values[n + period] - values[n]) % modulus == 0,
                  "period shift mismatch at modulus {}".format(modulus))
            period_shift_checks += 1
        if s:
            check((values[s - 1 + period] - values[s - 1]) % modulus != 0,
                  "preperiod not minimal at modulus {}".format(modulus))
        local_witnesses = []
        for prime in factor_integer(period):
            candidate = period // prime
            witness = next((n for n in range(s, s + period)
                            if (values[n + candidate] - values[n]) % modulus), None)
            check(witness is not None, "period not minimal")
            local_witnesses.append({"candidate_period": candidate, "index": witness})
            lower_period_checks += 1
        witnesses.append({"modulus": modulus, "preperiod": s,
                          "period": period, "smaller_period_witnesses": local_witnesses})
        modulus_checks += 1

    defect_checks = 0
    for prime in (3, 5, 7, 11, 13, 17, 19, 23, 29):
        exponent = 1
        while prime ** exponent <= 5000:
            modulus = prime ** exponent
            chi = 1 if prime % 4 == 1 else -1
            period = prime_power_period(prime, exponent)
            # Unit/nonunit splitting and the all-index defect identity.
            for n in range(21):
                depleted = ((1 - chi * pow(prime, 2 * n, modulus)) * values[n]) % modulus
                shifted = secant_mod_odd(n + period, modulus)
                check(shifted == depleted, "Euler-factor defect identity mismatch")
                defect_checks += 1
            exponent += 1

    huge_index_checks = 0
    for modulus in (3, 9, 27, 81, 25, 125, 49, 121, 343):
        data = analyze_modulus(modulus)
        for n in (10 ** 50 + 7, 10 ** 100 + 123456789):
            reduced = data.preperiod + (n - data.preperiod) % data.period
            check(secant_mod_odd(n, modulus) == values[reduced] % modulus,
                  "huge-index reduction failed")
            huge_index_checks += 1

    # Arithmetic check of the prime-power lifting coefficient at the mode -1.
    lift_checks = 0
    for p in (3, 5, 7, 11, 13):
        for exponent in (2, 3, 4):
            count = p ** (exponent - 1)
            left = sum((-1) ** ell * (-2 * ell) for ell in range(count)) % p
            right = sum((-1) ** ell * 2 * (ell + 1) for ell in range(count)) % p
            check(left == 1 and right == 1, "nonzero lifting mode failed")
            lift_checks += 1

    with (args.output / "periods_preperiods_1_10000.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(("modulus", "least_eventual_period", "first_periodic_index",
                         "pure_from_index_1"))
        for modulus in range(1, 10001):
            data = analyze_modulus(modulus)
            writer.writerow((modulus, data.period, data.preperiod,
                             int(data.pure_from_index_one)))

    with (args.output / "secant_residues_mod_27.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(("n", "a_n_mod_27"))
        writer.writerows((n, values[n] % 27) for n in range(101))

    with (args.output / "counterexample.json").open("w") as f:
        json.dump({
            "sequence": "OEIS A000364; sec(x)=sum a(n)*x^(2n)/(2n)!",
            "modulus": 27, "phi_modulus": 18,
            "a_1": 1, "a_19": values[19], "a_1_mod_27": 1,
            "a_19_mod_27": 10, "least_eventual_period": 18,
            "first_periodic_index": 2,
            "periodic_block_a_2_through_a_19": [v % 27 for v in values[2:20]],
            "explanation": "A period dividing 18 would force a(19)=a(1) modulo 27."
        }, f, indent=2)
        f.write("\n")

    report = {
        "all_checks_passed": True,
        "python_version": platform.python_version(),
        "maximum_exact_secant_index": maximum_index,
        "independently_cross_checked_recurrence_indices": [0, 100],
        "moment_formula_checks": moment_checks,
        "period_and_preperiod_moduli_checked": modulus_checks,
        "period_shift_equalities_checked": period_shift_checks,
        "proper_divisor_periods_rejected": lower_period_checks,
        "all_index_defect_checks": defect_checks,
        "huge_index_checks": huge_index_checks,
        "lifting_coefficient_checks": lift_checks,
        "data_modulus_bound": 10000,
        "formal_proof_assistant_used": False,
        "elapsed_seconds": round(perf_counter() - started, 3),
        "scope": "Finite consistency checks; universal claims are proved in article.pdf."
    }
    (args.output / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    (args.output / "minimality_witnesses_1_1000.json").write_text(
        json.dumps(witnesses, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
