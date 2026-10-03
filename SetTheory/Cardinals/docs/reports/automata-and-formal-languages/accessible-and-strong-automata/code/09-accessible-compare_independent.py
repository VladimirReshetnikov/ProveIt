"""Compare the finite generator with independently derived separate coefficient derivations."""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps = 100
root = Path(__file__).resolve().parent.parent
first = json.loads((root / "checks/verification.json").read_text())["large_n"]
third = json.loads((root / "checks/third_order.json").read_text())
rows = []
for k in (2, 3, 4):
    generated = json.loads((root / f"data/coefficients_k{k}_order5.json").read_text())
    ref = first[str(k)]
    expected = [ref["c"], ref["d1"], ref["d2"], third[str(k)]["d3"]]
    errors = [abs(mp.mpf(a)-mp.mpf(b)) for a,b in zip(generated["c"],expected)]
    assert max(errors) < mp.mpf("1e-55"), (k,errors)
    for j in (1,2):
        assert abs(mp.mpf(generated["tau"][j])-mp.mpf(third[str(k)][f"tau{j}"])) < mp.mpf("1e-55")
    rows.append({"k": k, "max_absolute_difference_c0_through_c3":mp.nstr(max(errors),25)})
result = {"status":"PASS", "checks":rows,"tolerance":"1e-55", "warning":"Numerical cross-check, not interval certification."}
(root / "data/independent_comparison.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
