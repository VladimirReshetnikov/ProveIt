#!/usr/bin/env python3
"""Run all optional numerical diagnostics; never invoked by the exact kernel."""
import sys
sys.dont_write_bytecode = True
import diagnostics
import laguerre_check
import check_two_point_decoration
import fft_experiment
import inverse_experiment
from _common import BOUNDARY, emit_json, parser


def run(standalone=False):
    receipts = {
        "precision_replay": diagnostics.run(600, standalone),
        "laguerre_finite_jet": laguerre_check.run(2000, 60, standalone),
        "two_point_decoration": check_two_point_decoration.run(20000),
        "fft_eta_extraction": fft_experiment.run(standalone=standalone),
        "smooth_inverse": inverse_experiment.run(2000, 60, standalone),
    }
    return {"schema_version": 1, "status": "PASS", "diagnostic": "all_optional",
            "receipts": receipts, "boundary": BOUNDARY}


def main():
    p = parser(__doc__)
    p.add_argument("--standalone", action="store_true", help="use only the optional standalone exact recurrence")
    args = p.parse_args()
    emit_json(run(args.standalone), args.output)


if __name__ == "__main__":
    main()
