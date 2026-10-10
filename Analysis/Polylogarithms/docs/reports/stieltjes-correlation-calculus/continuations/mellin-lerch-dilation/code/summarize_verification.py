#!/usr/bin/env python3
"""Summarize complete recorded verification files without rerunning numerics."""
from pathlib import Path
from decimal import Decimal
import json

OUT=Path(__file__).resolve().parents[1]/"results"

def read(name):
    return json.loads((OUT/name).read_text())

def largest(rows,key):
    return str(max(Decimal(x[key]) for x in rows))

if __name__=="__main__":
    exact=read("exact_verification.json")
    assert exact["status"]=="passed" and exact["total_checks"]==742
    a=read("mellin_rows.json")["rows"]
    b=read("general_master_checks.json")["rows"]
    c=read("parity_checks.json")
    d=read("dilated_polygamma.json")["tests"]
    e=read("dilated_stieltjes.json")["tests"]
    f=read("jets_checks.json")["numerical"]
    g=read("pi_squared_check.json")
    assert [len(a),len(b),len(c["scalar_checks"]),len(c["bivariate_checks"]),
            len(c["mixed_derivative_checks"]),len(d),len(e),len(f)]==[17,4,25,3,3,9,3,11]
    assert all(x["passed"] for x in d+e+f) and g["passed"]
    assert Decimal(largest(a,"scaled_error"))<Decimal("1e-23")
    assert Decimal(largest(b,"scaled_error"))<Decimal("1e-22")
    assert Decimal(largest(c["scalar_checks"],"abs_error"))<Decimal("1e-52")
    shifted=c["bivariate_checks"]+c["mixed_derivative_checks"]+[c["quarter_shift"]]
    assert Decimal(largest(shifted,"absolute_error"))<Decimal("1e-115")
    families=[
        {"family":"integer_mellin_rows","count":17,"max_scaled_error":largest(a,"scaled_error")},
        {"family":"general_mellin_master","count":4,"max_scaled_error":largest(b,"scaled_error")},
        {"family":"harmonic_scalar","count":25,"max_absolute_error":largest(c["scalar_checks"],"abs_error")},
        {"family":"harmonic_shifted","count":7,"max_absolute_error":largest(shifted,"absolute_error")},
        {"family":"dilated_polygamma","count":9,"max_scaled_error":largest(d,"relative_error")},
        {"family":"dilated_stieltjes","count":3,"max_scaled_error":largest(e,"relative_error")},
        {"family":"anchored_primitives_jets","count":11,"max_absolute_error":largest(f,"absolute_error")},
        {"family":"pi_squared_example","count":1,"max_absolute_error":g["absolute_error"]}]
    summary={"status":"passed","main_exact_assertions":742,"numerical_comparisons":sum(x["count"] for x in families),
             "families":families,"qualification":"Recorded floating-point consistency checks, not certified enclosures. See analytic proofs."}
    assert summary["numerical_comparisons"]==77
    (OUT/"verification_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(json.dumps(summary,indent=2))
