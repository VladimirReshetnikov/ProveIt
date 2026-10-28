#!/usr/bin/env python3
"""Exact discrete controls and numerical constants for the new schedule.

These checks support parameter algebra.  They do not run the SAT algorithm,
prove asymptotic statements by sampling, or verify the upstream preprint.
"""
from __future__ import annotations
from fractions import Fraction
import json
import math
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> None:
    r, decay, denom = 48, 8, 128
    budget = Fraction(decay, denom * (decay - 1))
    require(budget == Fraction(1, 112), "Packet budget identity failed")
    require(3**5 < 2**8, "Strict logarithm witness failed")
    require(Fraction(2, r) ** 2 * decay < 1, "Global geometric ratio is not < 1")
    require(decay < 12, "Bootstrap taper does not grow at every active depth")
    kappa = math.pi * math.sqrt(47 / 18)
    K = kappa * math.sqrt(denom) / (math.log(2) * (1 - math.sqrt(decay) / 24))
    low_budget = Fraction(8, 14 * 7)
    require(low_budget == Fraction(4, 49), "Low-degree packet budget failed")
    require(low_budget < Fraction(1, 12), "New packet degree exceeds invariant")
    low_packing_upper = Fraction(8, 49) * Fraction(28, 5) + Fraction(1, 12)
    require(low_packing_upper == Fraction(419, 420), "Low-degree packing witness failed")
    require(low_packing_upper < 1, "Low-degree packing has no strict margin")
    low_K = kappa * math.sqrt(14) / (math.log(2) * (1 - math.sqrt(decay) / 24))
    asym_root = Fraction(1, 81)
    asym_tail = Fraction(1, 108) / (1 - Fraction(1, 4))
    require(asym_tail == asym_root, "Asymmetric root/tail budgets differ")
    asym_total = asym_root + asym_tail
    require(Fraction(8)*asym_root + Fraction(9,10) == Fraction(809,810),
            "Asymmetric root exponent mismatch")
    require(Fraction(4)*asym_total + Fraction(9,10) == Fraction(809,810),
            "Asymmetric retained-side exponent mismatch")
    require(Fraction(9)*asym_total == Fraction(2,9),
            "Asymmetric fresh-side exponent mismatch")
    require(Fraction(809,810) < 1 and Fraction(2,9) < 1,
            "Asymmetric packing lacks strict margin")
    require(4 < 6, "Asymmetric bootstrap taper is not unbounded")
    asym_K = math.pi*math.sqrt(5/2)/math.log(2)*(9+math.sqrt(3))
    rows = []
    # lambda is logarithmic input size, not number of SAT variables.
    # Small lambda often fails asymptotic packing: record it honestly.
    for lam in (10**3, 10**4, 10**6, 10**9, 10**12, 10**18):
        buffer = math.ceil(6 * math.log2(lam))
        dmax = math.ceil(math.log(lam, 12)) + 2
        a = 0
        us = []
        for d in range(dmax + 1):
            u = lam // (denom * decay**d)
            a += u + buffer
            us.append(u)
        expected_bound = budget * lam + (dmax + 1) * buffer
        require(Fraction(a) <= expected_bound, "Cumulative schedule bound failed")
        log_packing_ratio = 2 * a * math.log2(r) - 0.1 * lam
        rows.append({"lambda": lam, "max_hypothetical_depth": dmax,
                     "buffer": buffer, "min_u": min(us),
                     "a_at_max_depth": a,
                     "log2_Q_squared_Delta_over_s_without_polylogs": log_packing_ratio,
                     "strict_power_margin_positive_at_this_sample": log_packing_ratio < 0,
                     "all_sampled_u_positive": min(us) > 0})
    candidates = []
    for groups in range(3, 2049):
        c = 2 / groups
        tau = c**(2/3)
        val = (math.pi / math.log(2)) * math.sqrt((8/3) * (1-1/groups) *
                20 * math.log2(groups)) / (1-tau)**1.5
        candidates.append((val, groups, 1/tau))
    candidates.sort()
    out = {"status": "all exact controls passed", "scope": __doc__,
           "asymmetric_certificate": {"r": 16, "root_u_denominator": 81,
                                      "tail_u_denominator": 108, "tail_decay": 4,
                                      "root_packet_budget": str(asym_root),
                                      "tail_packet_budget": str(asym_tail),
                                      "cumulative_packet_budget": str(asym_total),
                                      "root_and_retained_degree_exponent": "809/810",
                                      "fresh_side_and_padding_exponent": "2/9",
                                      "global_base2_coefficient": asym_K},
           "low_degree_certificate": {"packet_budget": str(low_budget),
                                      "degree_exponent": "1/12",
                                      "strict_packing_exponent_upper": str(low_packing_upper),
                                      "global_base2_coefficient": low_K},
           "exact_controls": {"packet_budget": str(budget),
                              "logarithm_witness_left": 3**5,
                              "logarithm_witness_right": 2**8,
                              "square_geometric_ratio": str(Fraction(2, r)**2 * decay)},
           "comparisons": {"source_schedule_base2_coefficient": 18535.75383166837,
                           "prior_refined_schedule": 648.4410666487529,
                           "prior_refined_plus_factorial_modes": 648.4410666487529 / math.sqrt(3),
                           "new_asymmetric_to_prior_ratio": asym_K / 648.4410666487529},
           "constants": {"r": r, "decay": decay, "denominator": denom,
                         "local_natural_log_coefficient": kappa,
                         "global_base2_coefficient": K,
                         "packing_power_slack": 0.1 - 2*math.log2(r)/112,
                         "bootstrap_minimum_u_power": 1 - math.log(8)/math.log(12)},
           "finite_parameter_controls": rows,
           "best_in_scanned_integer_boundary_family": [
               {"coefficient": x, "groups": g, "optimal_decay": b}
               for x, g, b in candidates[:5]]}
    path = Path(__file__).resolve().parents[1] / "results" / "schedule_results.json"
    path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": out["status"], "symmetric_K": K, "asymmetric_K": asym_K, "low_degree_K": low_K,
                      "exact_packet_budget": str(budget),
                      "results": str(path)}, indent=2))


if __name__ == "__main__":
    main()
