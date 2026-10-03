#!/usr/bin/env python3
"""Finite scalar-envelope diagnostics; no finite error claim."""
import math,json
from pathlib import Path
import numpy as np
from scipy.special import gammaln
from scipy.signal import lfilter
from scipy.optimize import brentq
rows=[]
for m in (128,512,2048,4096):
    ell=math.ceil(math.log(m)**.7)
    def logR(s):
        return (math.log((ell+2)/(ell+1))+1.5-math.log(2*ell)-.5*math.log(math.pi*m)
                +(ell-1)*math.log(1/s)+ell*math.log1p(s))
    tau=brentq(logR,1e-12,1,xtol=1e-14)
    targets=[("ordinary",.3),("ordinary",.7)]
    targets += [(f"transition_x{x}",tau*math.exp(x/(ell-1))) for x in (-2,0,2)]
    lengths=[(label,round(m*(ell-s))+1) for label,s in targets]
    k=np.arange(1,m+1,dtype=float)
    beta=np.exp(gammaln(2*k-1)-2*gammaln(k)-np.log(k)-k*math.log(4))
    impulse=np.zeros(max(n for _,n in lengths));impulse[0]=1
    renewal=lfilter([1.],np.r_[1.,-beta],impulse)
    if np.any(renewal<0):raise ArithmeticError("Positive renewal recurrence failed")
    for label,n in lengths:
        v=n-1;actual_ell=math.ceil(v/m);s=actual_ell-v/m
        if not 0<s<1:raise ArithmeticError("Rounded test hits an excluded integer")
        def G(j):
            deficit=j-v/m
            return math.exp(math.log(j+1)+1.5*deficit+(j-1)*math.log(deficit)
                -j*math.log(2*math.sqrt(math.pi*m))-gammaln(j))
        exact=float(renewal[:n]@renewal[:n][::-1])
        main=4/m*G(actual_ell)
        two=4/m*(G(actual_ell)+G(actual_ell+1))
        rows.append({"m":m,"n":n,"ell":actual_ell,"deficit":s,"case":label,
          "critical_scalar_coefficient":exact,"single_gamma_to_exact":main/exact,
          "two_gamma_to_exact":two/exact,"adjacent_gamma_ratio":G(actual_ell+1)/G(actual_ell)})
data={"scope":"Finite scalar diagnostics only. They neither count actual avoiders at these lengths nor assert a finite error bound.","rows":rows}
Path(__file__).with_name("scalar_diagnostics.json").write_text(json.dumps(data,indent=2)+"\n")
print(json.dumps({"rows":len(rows),"all_positive":all(x["critical_scalar_coefficient"]>0 for x in rows)}))

