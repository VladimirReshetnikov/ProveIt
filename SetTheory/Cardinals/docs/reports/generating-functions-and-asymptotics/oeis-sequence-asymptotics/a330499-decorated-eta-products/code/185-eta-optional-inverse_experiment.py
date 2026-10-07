#!/usr/bin/env python3
"""Smooth inverse model roots at exact targets Y=a(n); no integer-threshold claim."""
import sys
sys.dont_write_bytecode = True
import mpmath as mp
from _common import BOUNDARY, emit_json, exact_inputs, parser, require
from _mp import decimal, harmonics, inverse_row, scaled_exact


def run(nmax=2000, dps=60, standalone=False):
    require(100 <= nmax <= 2000 and 50 <= dps <= 100, "bounded range: 100<=max-n<=2000, 50<=dps<=100")
    values, engine = exact_inputs(nmax, standalone)
    samples = sorted({n for n in (100, 200, 400, 800, 1000, 2000, nmax) if n <= nmax})
    rows = []
    with mp.workdps(dps):
        for n in samples:
            h, actual = harmonics(n, 19), scaled_exact(values[n], n)
            result = inverse_row(values[n], n, 19)
            result["three_term_scaled_residual"] = (actual - h[0] - h[1]/mp.sqrt(n) - h[2]/n) * mp.mpf(n)**mp.mpf("1.5")
            require(abs(result["three_term_scaled_residual"]) < 1,
                    f"three-term finite residual regression at n={n}")
            require(abs(result["core_inverse_error"]) < mp.mpf(".001"), f"core root regression n={n}")
            require(abs(result["first_inverse_error"]) < mp.mpf(".001"), f"shifted root regression n={n}")
            require(abs(result["three_term_inverse_error"]) < mp.mpf(".00001"), f"three-term root regression n={n}")
            require(max(abs(result[k]) for k in ("core_log_equation_residual", "three_term_log_equation_residual")) < mp.mpf("1e-40"),
                    f"root equation residual regression n={n}")
            rows.append({"n": n, **{k: decimal(v) for k, v in result.items()}})
    return {"schema_version": 1, "status": "PASS", "diagnostic": "smooth_inverse",
            "max_n": nmax, "precision_dps": dps, "eta_modes": 19,
            "exact_input_engine": engine, "rows": rows,
            "checks": {"absolute_three_term_scaled_residual_limit_exclusive": "1",
                       "absolute_core_and_first_inverse_error_limit_exclusive": "0.001",
                       "absolute_three_term_inverse_error_limit_exclusive": "0.00001",
                       "absolute_log_equation_residual_limit_exclusive": "1e-40"},
            "versions": {"mpmath": mp.__version__}, "boundary": BOUNDARY,
            "model_note": "Errors compare chosen smooth-model roots with n at exact Y=a(n). An integer sequence has no canonical continuous inverse; small root error does not certify a ceiling near jumps."}


def main():
    p = parser(__doc__)
    p.add_argument("--max-n", type=int, default=2000)
    p.add_argument("--dps", type=int, default=60)
    p.add_argument("--standalone", action="store_true")
    args = p.parse_args()
    emit_json(run(args.max_n, args.dps, args.standalone), args.output)


if __name__ == "__main__":
    main()
