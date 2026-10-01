from pathlib import Path
import json, math
import numpy as np
from scipy.optimize import minimize_scalar, brentq
from probe_singletons import mean, SumUniform
nodes,weights=np.polynomial.legendre.leggauss(16)

def evaluate_uniform(obj,x,power):
    x=np.asarray(x,dtype=np.longdouble)
    v=np.maximum(x[...,None]-obj.sub,0)
    out=np.sum(obj.sign*v**power,axis=-1,dtype=np.longdouble)/(math.factorial(power)*obj.prod)
    if power==obj.n:
        out=np.where(x<=0,0,np.where(x>=obj.total,1,out))
    else:
        out=np.where((x<=0)|(x>=obj.total),0,out)
    return out

def tv_mask(caps,mask,threshold=None,cutoff=1.):
    chosen=[caps[i] for i in mask];hidden=[a for i,a in enumerate(caps) if i not in mask]
    obs=SumUniform(chosen);rest=SumUniform(hidden);total=SumUniform(caps)
    mu=sum(map(mean,caps)) if threshold is None else threshold;norm=total.cdf(mu)
    laplace=math.prod(-math.expm1(-a)/a for a in chosen)
    def likelihood(x):return laplace*math.exp(x)*rest.cdf(mu-x)/norm
    upper=min(obs.total,mu)
    mode=minimize_scalar(lambda x:-likelihood(x),bounds=(0,upper),method='bounded',options={'xatol':1e-12}).x
    mode=max((0.,mode,upper),key=likelihood)
    if likelihood(mode)<1-1e-7:raise ArithmeticError((caps,mask,likelihood(mode),norm))
    if likelihood(mode)<=cutoff:return 0.
    left=0. if likelihood(0)>=cutoff else brentq(lambda x:likelihood(x)-cutoff,0,mode,xtol=1e-12)
    right=obs.total if likelihood(obs.total)>=cutoff else brentq(lambda x:likelihood(x)-cutoff,mode,obs.total,xtol=1e-12)
    raw=[left,right]+[float(x) for x in obs.sub if left<x<right]+[float(mu-x) for x in rest.sub if left<mu-x<right]
    breaks=np.array(sorted(set(raw)),dtype=np.longdouble)
    mids=(breaks[1:]+breaks[:-1])/2;halfs=(breaks[1:]-breaks[:-1])/2
    xs=mids[:,None]+halfs[:,None]*nodes[None,:]
    ws=halfs[:,None]*weights[None,:]
    pdf=evaluate_uniform(obs,xs,len(chosen)-1)
    cdf=evaluate_uniform(rest,mu-xs,len(hidden))
    integrand=pdf*(cdf/norm-cutoff*np.exp(-xs)/laplace)
    return float(np.sum(ws*integrand,dtype=np.longdouble))

def main():
    rng=np.random.default_rng(21333);count=0;bad=[];closest=[]
    for n in range(3,10):
        for trial in range(300):
            if trial<150:
                q=rng.uniform(.28,.96);a=math.exp(rng.uniform(math.log(.2),math.log(18)))
                caps=[a*q**i for i in range(n)];kind='geometric'
            else:
                caps=sorted(np.exp(rng.uniform(math.log(.2),math.log(18),n)).tolist(),reverse=True)
                q=None;kind='arbitrary'
            i,j=sorted(rng.choice(n,2,replace=False).tolist())
            rest=[k for k in range(n) if k not in (i,j)]
            size=int(rng.integers(0,n-1))
            common=rng.choice(rest,size,replace=False).tolist()
            earlier=sorted(common+[i]);later=sorted(common+[j])
            te=tv_mask(caps,earlier);tl=tv_mask(caps,later);gap=te-tl
            record=dict(n=n,kind=kind,q=q,caps=caps,earlier=earlier,later=later,tv_earlier=te,tv_later=tl,gap=gap)
            count+=1
            if gap < -1e-7:
                bad.append(record);print('COUNTERCANDIDATE',json.dumps(record),flush=True)
                if len(bad)>=10:break
            closest.append(record)
        if len(bad)>=10:break
    out=dict(cases=count,countercandidates=bad,smallest_gaps=sorted(closest,key=lambda x:x['gap'])[:10])
    Path(__file__).with_name('mask_probe.json').write_text(json.dumps(out,indent=2)+'\n')
    print('DONE',count,'countercandidates',len(bad),flush=True)

if __name__=='__main__':main()
