"""Validate fixed-order generator against independent exact counts and precision replay."""
import json
from pathlib import Path
import mpmath as mp
from generate_coefficients import exact_counts

mp.mp.dps = 110
root = Path(__file__).resolve().parent.parent / "data"
report = {"status": "PASS", "numerical_checks": []}
for k in [2, 3, 4]:
    data = json.loads((root / f"coefficients_k{k}_order5.json").read_text())
    coeff = [mp.mpf(x) for x in data["c"]]
    a = exact_counts(k, 400)
    T = {}
    row = [1] + [0] * 400
    for m in range(1, k * 400 + 2):
        row = [0] + [j * row[j] + row[j - 1] for j in range(1, 401)]
        if m % k == 1 and (m - 1) // k in [100, 200, 400]:
            n = (m - 1) // k
            T[n] = row[n]
    for n, denominator in sorted(T.items()):
        b = mp.mpf(a[n]) / denominator
        errors = [abs(b - sum(coeff[j] / n ** j for j in range(J + 1)))
                  for J in range(6)]
        assert all(errors[J + 1] < errors[J] for J in range(5)), (k, n, errors)
        report["numerical_checks"].append({
            "k": k, "n": n,
            "absolute_errors_orders_0_through_5": [mp.nstr(x, 35) for x in errors],
            "order5_signed_error_times_n6": mp.nstr(
                (b - sum(coeff[j] / n ** j for j in range(6))) * n ** 6, 35)})

lo = json.loads((root / "coefficients_k2_order5.json").read_text())
hi = json.loads((root / "coefficients_k2_order5_90digits.json").read_text())
relative = [abs(mp.mpf(a) - mp.mpf(b)) / max(1, abs(mp.mpf(b)))
            for a, b in zip(lo["c"], hi["c"])]
assert max(relative) < mp.mpf("1e-59")
report["60_to_90_digit_replay_max_relative_difference"] = mp.nstr(max(relative), 30)
report["warning"] = "Numerical stability and finite replay are not interval certificates or asymptotic proofs."
(root / "generator_validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
