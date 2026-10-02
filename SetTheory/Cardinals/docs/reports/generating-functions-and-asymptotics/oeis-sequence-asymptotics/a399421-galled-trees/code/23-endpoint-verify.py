"""Replay every packaged check without external paths or network access.

This regenerates all 161 exact rows and independently recalculates constants
at both U-series truncations. It checks numerical agreement rather than
claiming interval-certified digits. Symbolic residuals and integer identities
are exact. Outputs go under checks/ unless --output-dir is supplied.
"""
import argparse
import json
import platform
import time
from pathlib import Path
import mpmath as mp
import sympy as sp
from triangle import (generate_triangle, wedderburn_etherington,
                      endpoint_coefficient, check_transformed_equation)
from critical_jets import compute_constants
from all_orders import verify_symbolics
from ratios import ratio_table, as_csv
from inversion import check_inversion


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2)+"\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parents[1]
    parser.add_argument("--output-dir", type=Path, default=root/'checks')
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    rows = generate_triangle(160)
    stored = json.loads((root/'data/triangle-160.json').read_text())
    assert rows == stored['rows']
    assert [sum(row) for row in rows] == stored['totals']
    first = json.loads((root/'data/first-rows.json').read_text())
    assert rows[1:len(first['rows'])+1] == first['rows']
    u = wedderburn_etherington(160)
    assert all(rows[n][0] == u[n] for n in range(1, 161))
    assert all(len(rows[n]) == (n-1)//2+1 for n in range(1, 161))
    assert all(all(isinstance(value, int) and value > 0 for value in rows[n]) for n in range(1, 161))
    for n in range(1, 161):
        for d in range(-2, n+2):
            got = endpoint_coefficient(rows, n, d)
            if d < 0 or d > n-1 or (n-d) % 2 != 1:
                assert got == 0
            else:
                assert got == rows[n][(n-d-1)//2] > 0
        # H0(w)=U(w²)/w, including zero at even n.
        assert endpoint_coefficient(rows, n, 0) == (u[(n+1)//2] if n % 2 else 0)
    transformed = check_transformed_equation(rows, 16)
    triangle_checks = {
        "max_n": 160, "first_rows_checked": len(first['rows']),
        "stored_triangle_exact_match": True, "zero_gall_column_matches_U": True,
        "integer_nonnegative_support": True, "endpoint_identity": "H0(w)=U(w^2)/w through w^160",
        "parity_and_deficiency_checks": "all n<=160 and -2<=d<=n+1",
        "transformed_equation": transformed,
    }
    write_json(args.output_dir/'triangle-checks.json', triangle_checks)
    print("PASS exact triangle, endpoint identity, support/parity, and transformed equation", flush=True)
    runs = [compute_constants(n, 110) for n in (220, 320)]
    with mp.workdps(110):
        differences = {}
        reference_differences = {}
        audit_reference = json.loads((root/'data/audit-reference-constants.json').read_text())['runs']
        audit_differences = {}
        for result in runs:
            reference = json.loads((root/f"data/constants-{result['truncation']}.json").read_text())
            gaps = {key: abs(mp.mpf(value)-mp.mpf(reference['constants'][key]))
                    for key, value in result['constants'].items()}
            assert max(gaps.values()) < mp.mpf('1e-55')
            reference_differences[str(result['truncation'])] = mp.nstr(max(gaps.values()), 8)
            prior = audit_reference[str(result['truncation'])]
            audit_gaps = [abs(mp.mpf(value)-mp.mpf(prior[key]))
                          for key, value in result['constants'].items()]
            assert max(audit_gaps) < mp.mpf('1e-45')
            audit_differences[str(result['truncation'])] = mp.nstr(max(audit_gaps), 12)
            write_json(args.output_dir/f"recomputed-constants-{result['truncation']}.json", result)
        for key, value in runs[0]['constants'].items():
            gap = abs(mp.mpf(value)-mp.mpf(runs[1]['constants'][key]))
            differences[key] = mp.nstr(gap, 12)
            assert gap < mp.mpf('1e-35'), (key, gap)
        numeric = {
            "truncations": [220, 320], "working_decimal_precision": 110,
            "absolute_differences": differences,
            "replay_max_absolute_difference_from_references": reference_differences,
            "max_absolute_difference_from_prior_independent_audit": audit_differences,
            "test_tolerance": "1e-35 (truncation agreement), 1e-55 (same-truncation replay), 1e-45 (prior audit)",
            "interpretation": "numerical stability check, not an interval certificate; report at most 15 significant decimal digits",
        }
    write_json(args.output_dir/'constant-agreement.json', numeric)
    print("PASS independent U/critical-jet constants at truncations 220 and 320", flush=True)
    symbolic = verify_symbolics()
    write_json(args.output_dir/'symbolic.json', symbolic)
    print("PASS symbolic finite-order generator, C1/C2, transfer, and Puiseux tests", flush=True)
    table = ratio_table(rows, runs[1]['constants'])
    assert table == json.loads((root/'data/ratios.json').read_text())
    assert as_csv(table) == (root/'data/ratios.csv').read_text()
    write_json(args.output_dir/'recomputed-ratios.json', table)
    print("PASS 16 exact/leading/C1/C2 numerical comparisons", flush=True)
    inverse = check_inversion(rows, runs[1]['constants'])
    reference_inverse = json.loads((root/'data/inversion.json').read_text())
    assert inverse == reference_inverse
    write_json(args.output_dir/'inversion-checks.json', inverse)
    print("PASS K2 W0/Newton model, 6320 monotonicity pairs, and both equality cases", flush=True)
    summary = {
        "result": "PASS", "python": platform.python_version(),
        "mpmath": mp.__version__, "sympy": sp.__version__,
        "elapsed_seconds": round(time.monotonic()-started, 3),
        "network_or_external_workspace_dependencies": False,
        "checks": ["triangle through n=160", "13 first rows", "endpoint identity and parity",
                   "transformed equation through w^16", "220/320 critical jets",
                   "all-fixed-order symbolic generator and C1/C2", "16 C2-inclusive ratio cases",
                   "K2 W0/Newton inversion models", "6320 exact monotonicity pairs and both equality cases"],
    }
    write_json(args.output_dir/'summary.json', summary)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
