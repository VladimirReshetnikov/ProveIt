#!/usr/bin/env python3
"""Generate all finite claims directly from the accepted certificate manifest."""
from pathlib import Path
import hashlib,json,sys
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parent
def need(b,s):
    if not b:raise ArithmeticError(s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=ROOT/"first_negative_manifest.json"
data=json.loads(manifest.read_text())
need(data["complete"],"batch incomplete")
rows=data["cases"]
need([x["m"] for x in rows]==list(range(2,129)),"coverage")
comparison=[]
for x in rows:
    for file,hashkey in [("production_file","production_sha256"),("audit_file","audit_sha256")]:
        need(sha(ROOT/x[file])==x[hashkey],"certificate hash")
        certificate=json.loads((ROOT/x[file]).read_text())
        need(certificate["first_negative_certified"] and certificate["first_negative_degree"]==x["first_negative_degree"],"certificate claim")
    predicted=2*((10*x["m"])//3-1)
    comparison.append({"m":x["m"],"actual":x["first_negative_degree"],"predicted":predicted,
                       "difference":x["first_negative_degree"]-predicted,
                       "production_sha256":x["production_sha256"],"independent_sha256":x["audit_sha256"]})
exceptions=[x for x in comparison if x["difference"]]
later=[x for x in exceptions if x["m"]>=16]
failures_66=[x for x in comparison if 5*x["actual"]<=33*x["m"]]
summary={"scope":"Exact finite first-negative degrees for m=2,...,128; no large-m asymptotic claim",
         "accepted_manifest_sha256":sha(manifest),"cases":127,
         "formula_tested":"2*(floor(10*m/3)-1)",
         "formula_comparison":comparison,"all_exceptions":exceptions,"exceptions_from_m16":later,
         "first_exception_from_m16":later[0] if later else None,
         "finite_failures_of_positivity_through_6_6m":failures_66,
         "largest_observed_failure_order_for_6_6m":max(x["m"] for x in failures_66),
         "producer_seconds_sum":sum(x["producer_seconds"] for x in rows),
         "independent_seconds_sum":sum(x["audit_seconds"] for x in rows),
         "accepted_precision_parameters":sorted(set(x["precision_bits"] for x in rows)),
         "cases_with_inconclusive_later_coefficients":[x["m"] for x in rows if not(x["production_all_signs"] and x["audit_all_signs"])],
         "batch_elapsed_seconds":data["elapsed_seconds"]}
(ROOT/"dataset_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps({"cases":127,"exceptions_from_m16":[[x["m"],x["actual"],x["predicted"]] for x in later]}))
