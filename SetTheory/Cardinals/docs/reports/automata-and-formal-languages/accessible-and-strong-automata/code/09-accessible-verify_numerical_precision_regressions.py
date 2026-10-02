"""Regressions for exact imaginary phases and exponentially small large-k terms."""
import json
from pathlib import Path
import mpmath as mp
from generate_coefficients import generate, imaginary_unit_power

root = Path(__file__).resolve().parent.parent / "data"
report = {"status": "PASS"}
mp.mp.dps = 100
exponents = list(range(513)) + [999, 1000, 1001, 10000, 100001]
for m in exponents:
    expected = (mp.mpc(1), mp.mpc(0, 1), mp.mpc(-1), mp.mpc(0, -1))[m % 4]
    assert imaginary_unit_power(m) == expected, m
report["exact_four_cycle_checks"] = len(exponents)
report["representative_phases"] = {
    str(m): str(imaginary_unit_power(m)) for m in [101, 102, 1001, 100001]}

# Verify every previously printed reference coefficient is unchanged, then
# refresh metadata to make the working precision and rho visible.
compared = ["v", "c", "tau", "alpha", "small_boundary_source"]
reference_replays = []
for k, digits, filename in [
        (2, 60, "coefficients_k2_order5.json"),
        (3, 60, "coefficients_k3_order5.json"),
        (4, 60, "coefficients_k4_order5.json"),
        (2, 90, "coefficients_k2_order5_90digits.json")]:
    old = json.loads((root / filename).read_text())
    new = generate(k, 5, digits)
    assert all(old[key] == new[key] for key in compared), (k, digits)
    (root / filename).write_text(json.dumps(new, indent=2) + "\n")
    reference_replays.append({"alphabet": k, "digits": digits,
                              "working_digits": new["working_digits"],
                              "all_displayed_coefficients_unchanged": True})
report["order5_reference_replays"] = reference_replays

low = generate(500, 1, 30)
high = generate(500, 1, 60, guard_digits=50)
mp.mp.dps = 400
rho = -mp.lambertw(-500 * mp.exp(-500)) / 500
v = 1 - rho
exact_first_formula = 500 * rho * v / (2 * (1 - 500 * rho))
for data in [low, high]:
    got = mp.mpf(data["c"][1])
    relative = abs(got / exact_first_formula - 1)
    assert got > 0
    assert relative < mp.mpf(10) ** (1 - data["digits"])
    data["regression_relative_error_against_direct_c1_formula"] = mp.nstr(relative, 30)
(root / "coefficients_k500_order1.json").write_text(json.dumps(low, indent=2) + "\n")
(root / "coefficients_k500_order1_60digits.json").write_text(json.dumps(high, indent=2) + "\n")
report["large_alphabet_replay"] = {
    "alphabet": 500, "order": 1,
    "low_working_digits": low["working_digits"],
    "high_working_digits": high["working_digits"],
    "c1_30digits": low["c"][1], "c1_60digits": high["c"][1],
    "reference_direct_formula": mp.nstr(exact_first_formula, 80),
    "relative_error_30digits": low["regression_relative_error_against_direct_c1_formula"],
    "relative_error_60digits": high["regression_relative_error_against_direct_c1_formula"]}
report["caveat"] = "Finite numerical replay is not an interval certificate; arbitrary high-order requested digits still require increased-precision stability checks."
(root / "numerical_precision_regressions.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
