#!/usr/bin/env python3
"""Reevaluate stored numerical ordinates; this does not certify completeness."""
import json
from pathlib import Path
import mpmath as mp
import complex_spectra_demo as demo


def main():
    root = Path(__file__).resolve().parent
    data = json.loads((root / "zero_lists.json").read_text())
    mp.mp.dps = 80
    checks = {}
    for name, texts in data["ordinates"].items():
        values = [mp.mpf(t) for t in texts]
        residuals = [
            abs(demo.l_function(mp.mpf("0.5") + mp.j*t, name))
            for t in values
        ]
        checks[name] = {
            "count": len(values),
            "maximum_absolute_L_residual_at_saved_ordinates": mp.nstr(max(residuals), 16),
            "strictly_increasing": all(a < b for a, b in zip(values, values[1:])),
            "all_inside_requested_window": all(abs(t) <= data["height"] for t in values),
        }
        assert max(residuals) < mp.mpf("1e-49")
        assert checks[name]["strictly_increasing"]
        assert checks[name]["all_inside_requested_window"]
    report = {
        "status": "numerical_exploration_not_certified",
        "evaluation_decimal_digits": 80,
        "saved_ordinate_significant_digits": 52,
        "saved_data_evaluation": checks,
        "assignment_comparison": demo.check_edit_distance(),
    }
    (root / "verification_summary.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
