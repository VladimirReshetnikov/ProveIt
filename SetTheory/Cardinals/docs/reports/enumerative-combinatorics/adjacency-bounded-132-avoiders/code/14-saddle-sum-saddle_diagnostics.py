#!/usr/bin/env python3
"""Numerical diagnostics only; exact scalar coefficients via positive renewal.
Requires NumPy and SciPy. No finite error bound or actual-class count is asserted.
"""
import json, math
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from scipy.signal import lfilter
from scipy.special import gammaln, logsumexp

rows=[]
for m in (128,256,512,1024):
    k=np.arange(1,m+1,dtype=float)
    logbeta=gammaln(2*k-1)-2*gammaln(k)-np.log(k)-k*math.log(4)
    t=brentq(lambda s:float(np.exp(logbeta+s*k/m).sum()-1),0,2*math.log(m),xtol=2e-13)
    p=np.exp(logbeta+t*k/m)
    root_residual=abs(float(p.sum())-1)
    w=m/t
    cutoff=max(1,m//64)
    small=k<=cutoff
    def params(h):
        z=p*np.exp(h*k/w)
        av=z[small];ak=k[small]
        bv=z[~small];bk=k[~small]
        A=float(av.sum());B=float(bv.sum())
        assert A<1
        a1=float(av@ak);a2=float(av@(ak*ak))
        b1=float(bv@bk);b2=float(bv@(bk*bk))
        mu=b1/B+a1/(1-A)
        var=b2/B-(b1/B)**2+a2/(1-A)+(a1/(1-A))**2
        return mu,var,math.log(B)-math.log1p(-A),-2*math.log1p(-A)
    hlo,hhi=-.8,1.
    mu_lo=params(hlo)[0];mu_hi=params(hhi)[0]
    mu,var,_,logD=params(0)
    l=math.log(m)
    lengths=[("lower_half",round(.5*m*l)),("lower",round(m*l)),
             ("cubic",round(m*l**1.5)),("theta",round(m*l*l)),
             ("upper_theta",round(2*m*l*l))]
    impulse=np.zeros(max(n for _,n in lengths))
    impulse[0]=1
    renewal=lfilter([1.],np.r_[1.,-p],impulse)
    assert np.min(renewal)>=0
    for label,n in lengths:
        v=n-1
        exact=float(renewal[:n]@renewal[:n][::-1])
        left=max(1,math.ceil(v/mu_hi));right=math.floor(v/mu_lo)
        terms=[]
        for ell in range(left,right+1):
            h=brentq(lambda z:params(z)[0]-v/ell,hlo,hhi,xtol=2e-13)
            _,variance,logQ,ld=params(h)
            logterm=math.log(ell+1)+ld+ell*logQ-h*v/w-.5*math.log(2*math.pi*ell*variance)
            terms.append((ell,logterm,h))
        saddle=math.exp(logsumexp([x[1] for x in terms]))
        L=v/mu;H=math.sqrt(var*L)/mu
        neighbors={math.floor(L),math.ceil(L)}
        selected=[x[1] for x in terms if x[0] in neighbors]
        two=math.exp(logsumexp(selected)) if selected else None
        rows.append({"m":m,"n":n,"label":label,"cutoff":cutoff,
                     "tilt_interval":[hlo,hhi],"root_residual":root_residual,
                     "L":L,"H":H,"scalar_normalized_coefficient":exact,
                     "saddle_to_exact_ratio":saddle/exact,
                     "neighbor_share_of_saddle":two/saddle if two else None,
                     "retained_counts":len(terms)})
out={"description":"Finite scalar diagnostics with chosen numerical interval and cutoff; convergence evidence is not a proof and no finite error tolerance is claimed.",
     "rows":rows}
Path(__file__).with_name("saddle_diagnostics.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"rows":len(rows),"min_ratio":min(x["saddle_to_exact_ratio"] for x in rows),
                 "max_ratio":max(x["saddle_to_exact_ratio"] for x in rows)}))

