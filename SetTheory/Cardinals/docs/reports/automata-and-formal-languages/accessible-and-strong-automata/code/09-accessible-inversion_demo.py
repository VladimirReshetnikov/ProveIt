"""Finite model-inversion diagnostics; no certified integer threshold claim."""
from pathlib import Path
import json
import mpmath as mp
from generate_coefficients import exact_counts
mp.mp.dps = 100
root = Path(__file__).resolve().parent.parent
rows = []
for k in (2,3,4):
    saved=json.loads((root/f"data/coefficients_k{k}_order5.json").read_text())
    v=mp.mpf(saved["v"]);c=k*v-k+1;d=k-1
    beta=mp.exp(-d)/((1-v)*v**d);Ca=mp.sqrt(c)/(v*mp.sqrt(2*mp.pi))
    alpha=list(map(mp.mpf,saved["alpha"]))
    counts=exact_counts(k,200)
    def logmodel(u):
        return mp.log(Ca)+u*mp.log(beta)+(d*u+mp.mpf('.5'))*mp.log(u)+mp.log(sum(a*u**(-j) for j,a in enumerate(alpha)))
    def derivative(u):
        poly=sum(a*u**(-j) for j,a in enumerate(alpha))
        return mp.log(beta)+d*mp.log(u)+d+mp.mpf('.5')/u-sum(j*a*u**(-j-1) for j,a in enumerate(alpha))/poly
    for n in (50,100,200):
        y=mp.log(counts[n]);seed=y/(d*mp.lambertw(beta**(mp.mpf(1)/d)*y/d))
        u=seed
        for _ in range(5):u-=(logmodel(u)-y)/derivative(u)
        assert abs(logmodel(u)-y)<mp.mpf('1e-50')
        rows.append({"k":k,"exact_count_index":n,"Lambert_seed_minus_n":mp.nstr(seed-n,25),"order5_model_root_minus_n":mp.nstr(u-n,25),"scaled_model_error_n6_log_n":mp.nstr((u-n)*n**6*mp.log(n),25)})
result={"status":"PASS","rows":rows,"warning":"Roots invert F5, not a canonical interpolation of a_n. The article's bracket constants are existential."}
(root/"data/inversion_demo.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
