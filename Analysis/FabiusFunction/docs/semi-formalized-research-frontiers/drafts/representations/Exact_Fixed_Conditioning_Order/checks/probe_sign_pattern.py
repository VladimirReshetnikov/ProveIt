from pathlib import Path
import json
import numpy as np
rng=np.random.default_rng(10323)
def positive_integral(a,b,knots,values):
    anti=np.concatenate(([0.],np.cumsum(np.diff(knots)*values)))
    def primitive(x):return np.interp(x,knots,anti)
    breaks=np.unique(np.concatenate(([0.,a],knots[(knots>0)&(knots<a)],(knots-b)[(knots-b>0)&(knots-b<a)])))
    f=primitive(breaks+b)-primitive(breaks);area=0.
    for length,left,right in zip(np.diff(breaks),f[:-1],f[1:]):
        if min(left,right)>=0:area+=length*(left+right)/2
        elif max(left,right)>0:area+=length*max(left,right)**2/(2*abs(right-left))
    return area
bad=[]
for trial in range(100000):
    a=float(rng.uniform(1.01,5));b=1.;n=30
    knots=np.linspace(0,a+b,n+1)
    l,u=sorted(rng.choice(n+1,2,replace=False).tolist())
    values=np.exp(rng.uniform(-2,2,n));values[:l]*=-1;values[u:]*=-1
    # Shift signed mass to zero by scaling the positive interval.
    mid=(knots[1:]+knots[:-1])/2
    lengths=np.minimum(a,mid)-np.maximum(0,mid-b)
    weights=np.diff(knots)*lengths
    pos=values>0;neg=~pos
    if not np.any(neg):continue
    values[pos]*=-np.sum(weights[neg]*values[neg])/np.sum(weights[pos]*values[pos])
    ra=positive_integral(a,b,knots,values);rb=positive_integral(b,a,knots,values)
    if ra<rb-1e-8:
        record=dict(a=a,b=b,knots=knots.tolist(),g=values.tolist(),positive_range=[l,u],source_positive_area=ra,target_positive_area=rb,gap=ra-rb)
        bad.append(record);print('COUNTER',json.dumps(record),flush=True);break
Path(__file__).with_name('sign_pattern_probe.json').write_text(json.dumps(dict(cases=trial+1,counterexamples=bad),indent=2)+'\n')
print('DONE',trial+1,len(bad))
