"""Deterministic, dependency-free default checks; writes only JSON to stdout."""
import argparse
import json
from fractions import Fraction
from pathlib import Path

from coefficient_certificates import Rational, check_coefficients
from exact_counts import board_count, require, transfer_count


def run(transfer_max=7, board_max=5):
    if not (0 <= transfer_max <= 10 and 0 <= board_max <= 7):
        raise ValueError("Supported fixture bounds: 0<=transfer-max<=10, 0<=board-max<=7")
    fixture = json.loads((Path(__file__).parent / "fixtures/a137432_selected.json").read_text())
    published = {int(n):int(value) for n,value in fixture["terms"].items()}
    published[0] = 1  # Separate empty-board convention, not a b-file observation.
    # Explicit exceptions are deliberately used: all checks survive python -O.
    try:
        require(False, "sentinel")
    except RuntimeError as error:
        if str(error) != "sentinel":
            raise
    else:
        raise RuntimeError("Check sentinel unexpectedly disappeared")
    require((Rational((0,1),1,0).D()-Rational((0,1),2,0)).p == (Fraction(0),),
            "Rational Euler derivative elementary identity failed")
    counts = {"transfer":{}, "direct_board":{}}
    for n in range(transfer_max+1):
        value = transfer_count(n)
        require(value == published[n], f"Transfer total mismatch at n={n}: {value}")
        counts["transfer"][str(n)] = str(value)
    for n in range(board_max+1):
        value = board_count(n)
        require(value == published[n], f"Actual-board total mismatch at n={n}: {value}")
        counts["direct_board"][str(n)] = str(value)
    certificates = check_coefficients()
    return {"status":"PASS", "transfer_max":transfer_max,"direct_board_max":board_max,
            "words_with_all_matrix_identities_checked":sum(2**n for n in range(1,transfer_max+1)),
            "counts":counts,"coefficient_certificates":certificates,
            "scope":"Finite exact checks and exact c0-c3 coefficient identities; the all-n asymptotic theorem is proved in the report."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extended",action="store_true",help="Use n<=10 transfer and n<=7 actual-board checks")
    parser.add_argument("--transfer-max",type=int)
    parser.add_argument("--board-max",type=int)
    args = parser.parse_args()
    transfer_max = args.transfer_max if args.transfer_max is not None else (10 if args.extended else 7)
    board_max = args.board_max if args.board_max is not None else (7 if args.extended else 5)
    print(json.dumps(run(transfer_max,board_max),sort_keys=True,indent=2))


if __name__ == "__main__":
    main()
