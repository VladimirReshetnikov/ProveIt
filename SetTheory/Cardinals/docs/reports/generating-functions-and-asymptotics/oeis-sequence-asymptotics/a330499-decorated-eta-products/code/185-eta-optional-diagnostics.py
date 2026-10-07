#!/usr/bin/env python3
"""Optional 50/80-digit replay; the mandatory exact kernel needs no mpmath."""
import sys
sys.dont_write_bytecode = True
import mpmath as mp
from _common import BOUNDARY, emit_json, exact_inputs, parser, require
from _mp import constants, decimal, harmonics, inverse_row, scaled_exact


def evaluate(values, n, dps):
    with mp.workdps(dps):
        h = harmonics(n, 30)
        actual = scaled_exact(values[n], n)
        row = {"scaled_error": actual, "H0": h[0], "H1": h[1], "H2": h[2],
               "three_term_scaled_residual":
                   (actual - h[0] - h[1] / mp.sqrt(n) - h[2] / n) * mp.mpf(n)**mp.mpf("1.5")}
        row.update(inverse_row(values[n], n, 30))
        return row


def run(nmax=600, standalone=False):
    require(100 <= nmax <= 2000, "max-n must be in [100, 2000]")
    values, engine = exact_inputs(nmax, standalone)
    samples = sorted({n for n in (100, 200, 400, 600, nmax) if n <= nmax})
    rows = []
    maximum_delta = mp.mpf(0)
    with mp.workdps(100):
        for n in samples:
            low, high = evaluate(values, n, 50), evaluate(values, n, 80)
            deltas = {key: abs(low[key] - high[key]) for key in high}
            delta = max(deltas.values())
            maximum_delta = max(maximum_delta, delta)
            require(delta < mp.mpf("1e-35"), f"50/80 precision regression at n={n}")
            require(abs(high["three_term_scaled_residual"]) < 1,
                    f"three-term finite residual regression at n={n}")
            # Every compared field and both precisions are retained in the receipt.
            rows.append({"n": n, "dps_50": {k: decimal(v) for k, v in low.items()},
                         "dps_80": {k: decimal(v) for k, v in high.items()},
                         "maximum_absolute_precision_delta": decimal(delta)})
    return {"schema_version": 1, "status": "PASS", "diagnostic": "precision_replay",
            "max_n": nmax, "exact_input_engine": engine, "eta_modes": 30,
            "precision_dps": [50, 80], "rows": rows,
            "checks": {"maximum_absolute_precision_delta": decimal(maximum_delta),
                       "precision_delta_limit_exclusive": "1e-35",
                       "absolute_three_term_scaled_residual_limit_exclusive": "1"},
            "versions": {"mpmath": mp.__version__}, "boundary": BOUNDARY}


def main():
    p = parser(__doc__)
    p.add_argument("--max-n", type=int, default=600)
    p.add_argument("--standalone", action="store_true", help="use the self-contained exact recurrence")
    args = p.parse_args()
    emit_json(run(args.max_n, args.standalone), args.output)


if __name__ == "__main__":
    main()
