"""Compare new fused kernel with one-inversion baseline and exact oracle."""
import json
import sys
from pathlib import Path
from cauchy_kernel import Parameters, recurrent_tables
from cauchy_checks import rational_oracle, qreduce
from fused_cauchy import baseline_tables, fused_tables


def main():
    cases, exact_entries, comparisons, regressions = 0, 0, 0, 0
    for a in range(1, 6):
        for i in range(a):
            for t in (-(1 << i), 1 << i):
                for zeta in ((0, 0), (1, 0), (0, 1), (1, 1), (-1, 2), (2, 0)):
                    oracle = rational_oracle(Parameters(a, i, t, zeta, 32)) if a <= 4 else None
                    for p in (1, 2, 8, 4*(1 << (a-1))+16):
                        params = Parameters(a, i, t, zeta, p)
                        old, base, new = recurrent_tables(params), baseline_tables(params), fused_tables(params)
                        for key, exact in (("target", oracle[0] if oracle else None),
                                           ("source", oracle[1] if oracle else None)):
                            if old[key] != base[key] or base[key] != new[key]:
                                raise ArithmeticError("fused/baseline/prior output mismatch")
                            comparisons += len(new[key])**2
                            if exact is not None:
                                for b, row in enumerate(new[key]):
                                    for j, value in enumerate(row):
                                        if value != qreduce(exact[b][j], p):
                                            raise ArithmeticError("fused exact rational mismatch")
                                        exact_entries += 1
                        if base["counts"]["unit_inversions"] != 1 or new["counts"]["unit_inversions"] != 1:
                            raise ArithmeticError("single-inversion condition failed")
                        cases += 1
    # Explicit loss-and-recovery fixture from the late paper: source j=2
    # at p=1 becomes zero and subsequently a unit; fused state must survive.
    out = fused_tables(Parameters(3, 0, 1, (1, 0), 1))
    if out["source"][1][2] != (0, 0) or out["source"][2][2] == (0, 0):
        raise ArithmeticError("zero-output recovery fixture failed")
    regressions += 1
    result = {"status": "PASS", "configurations": cases,
              "table_entry_comparisons": comparisons, "exact_rational_entry_checks": exact_entries,
              "zero_output_recovery_regressions": regressions,
              "baseline": "self-authored reproduction of late one-inversion quadratic algorithm",
              "new_algorithm": "transition ratio fusion and common target prefactor absorption",
              "archive_code_execution": False}
    dest = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/"results"/"fused_cauchy_checks.json"
    dest.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
