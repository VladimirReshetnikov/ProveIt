from pathlib import Path
import json,math
import numpy as np
from scipy.optimize import minimize_scalar,brentq
from probe_singletons import SumUniform
from probe_masks import evaluate_uniform,nodes,weights

def tv_band(caps,mask,lower,upper):
    chosen=[caps[i] for i in mask];hidden=[a for i,a in enumerate(caps) if i not in mask]
    obs=SumUniform(chosen);rest=SumUniform(hidden);total=SumUniform(caps)
    norm=total.cdf(upper)-total.cdf(lower)
    laplace=math.prod(-math.expm1(-a)/a for a in chosen)
    def likelihood(x):return laplace*math.exp(x)*(rest.cdf(upper-x)-rest.cdf(lower-x))/norm
    lo=max(0.,lower-rest.total);hi=min(obs.total,upper)
    mode=minimize_scalar(lambda x:-likelihood(x),bounds=(lo,hi),method='bounded',options={'xatol':1e-11}).x
    mode=max((lo,mode,hi),key=likelihood)
    if likelihood(mode)<1-1e-6:raise ArithmeticError((caps,mask,lower,upper,likelihood(mode),norm))
    left=0. if likelihood(0)>=1 else brentq(lambda x:likelihood(x)-1,0,mode,xtol=1e-11)
    right=obs.total if likelihood(obs.total)>=1 else brentq(lambda x:likelihood(x)-1,mode,obs.total,xtol=1e-11)
    raw=[left,right]+[float(x) for x in obs.sub if left<x<right]
    for tau in (lower,upper):raw += [float(tau-x) for x in rest.sub if left<tau-x<right]
    breaks=np.array(sorted(set(raw)),dtype=np.longdouble)
    mids=(breaks[1:]+breaks[:-1])/2;halfs=(breaks[1:]-breaks[:-1])/2
    xs=mids[:,None]+halfs[:,None]*nodes[None,:];ws=halfs[:,None]*weights[None,:]
    pdf=evaluate_uniform(obs,xs,len(chosen)-1)
    cdf=evaluate_uniform(rest,upper-xs,len(hidden))-evaluate_uniform(rest,lower-xs,len(hidden))
    return float(np.sum(ws*pdf*(cdf/norm-np.exp(-xs)/laplace),dtype=np.longdouble))

rng=np.random.default_rng(54133);count=0;bad=[]
for n in range(2,8):
    for trial in range(300):
        caps=sorted(np.exp(rng.uniform(math.log(.3),math.log(10),n)).tolist(),reverse=True)
        i,j=sorted(rng.choice(n,2,replace=False).tolist());available=[k for k in range(n) if k not in(i,j)]
        common=rng.choice(available,int(rng.integers(0,n-1)),replace=False).tolist()
        e=sorted(common+[i]);l=sorted(common+[j]);total=sum(caps)
        lower=rng.uniform(.01,.9)*total;upper=lower+rng.uniform(.03,1)*(total-lower)
        te=tv_band(caps,e,lower,upper);tl=tv_band(caps,l,lower,upper)
        count+=1
        if te-tl < -1e-7:
            r=dict(n=n,caps=caps,lower=lower,upper=upper,earlier=e,later=l,tv_earlier=te,tv_later=tl,gap=te-tl)
            bad.append(r);print('COUNTERCANDIDATE',json.dumps(r),flush=True)
            if len(bad)>=5:break
    if len(bad)>=5:break
Path(__file__).with_name('bands_probe.json').write_text(json.dumps(dict(cases=count,countercandidates=bad),indent=2)+'\n')
print('DONE',count,'countercandidates',len(bad))
