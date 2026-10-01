from pathlib import Path
import json, math
import numpy as np
from scipy.optimize import minimize_scalar, brentq

def mean(a):
    if a<1e-3: return a/2-a*a/12+a**4/720-a**6/30240
    if a>700: return 1.
    return 1-a/math.expm1(a)

class SumUniform:
    def __init__(self,caps):
        self.caps=np.array(caps,dtype=np.longdouble)
        self.n=len(caps);self.total=sum(caps);self.average=self.total/2
        self.sub=np.array([0],dtype=np.longdouble)
        self.sign=np.array([1],dtype=np.longdouble)
        for a in self.caps:
            self.sub=np.concatenate((self.sub,self.sub+a))
            self.sign=np.concatenate((self.sign,-self.sign))
        self.prod=np.prod(self.caps)
    def cdf(self,x):
        if x<=0:return 0.
        if x>=self.total:return 1.
        v=np.maximum(np.longdouble(x)-self.sub,0)
        return float(np.sum(self.sign*v**self.n,dtype=np.longdouble)/(math.factorial(self.n)*self.prod))
    def primitive(self,x):
        if x<=0:return 0.
        if x>=self.total:return x-self.average
        v=np.maximum(np.longdouble(x)-self.sub,0)
        return float(np.sum(self.sign*v**(self.n+1),dtype=np.longdouble)/(math.factorial(self.n+1)*self.prod))

def tv_single(caps,index):
    a=caps[index];mu=sum(map(mean,caps));total=SumUniform(caps);norm=total.cdf(mu)
    rest=SumUniform(caps[:index]+caps[index+1:]);z=-math.expm1(-a)
    def likelihood(x): return z/a*math.exp(x)*rest.cdf(mu-x)/norm
    upper=min(a,mu)
    res=minimize_scalar(lambda x:-likelihood(x),bounds=(0,upper),method='bounded',options={'xatol':1e-12})
    mode=max((0.,res.x,upper),key=likelihood)
    if likelihood(mode)<1-1e-7:raise ArithmeticError((caps,index,likelihood(mode),norm))
    left=0. if likelihood(0)>=1 else brentq(lambda x:likelihood(x)-1,0,mode,xtol=1e-13)
    right=a if likelihood(a)>=1 else brentq(lambda x:likelihood(x)-1,mode,a,xtol=1e-13)
    def pcdf(x):return (rest.primitive(mu)-rest.primitive(mu-x))/(a*norm)
    def qcdf(x):return -math.expm1(-x)/z
    return (pcdf(right)-pcdf(left))-(qcdf(right)-qcdf(left))

def main():
    rng=np.random.default_rng(14311)
    count=0;bad=[];nearest=[]
    for n in range(2,9):
        for trial in range(150):
            if trial<75:
                q=rng.uniform(.18,.96);a=math.exp(rng.uniform(math.log(.1),math.log(25)))
                caps=[a*q**i for i in range(n)]
                kind='geometric'
            else:
                caps=sorted(np.exp(rng.uniform(math.log(.1),math.log(25),n)).tolist(),reverse=True)
                q=None;kind='arbitrary'
            tv=[tv_single(caps,i) for i in range(n)]
            gap=min(tv[i]-tv[i+1] for i in range(n-1))
            record=dict(n=n,kind=kind,q=q,caps=caps,tv=tv,min_gap=gap)
            count+=1
            if gap < -1e-7:
                bad.append(record)
                print('COUNTERCANDIDATE',json.dumps(record),flush=True)
                if len(bad)>=10:break
            nearest.append(record)
        if len(bad)>=10:break
    out=dict(cases=count,countercandidates=bad,smallest_gaps=sorted(nearest,key=lambda x:x['min_gap'])[:10])
    Path(__file__).with_name('singleton_probe.json').write_text(json.dumps(out,indent=2)+'\n')
    print('DONE',count,'countercandidates',len(bad),flush=True)

if __name__=='__main__':main()
