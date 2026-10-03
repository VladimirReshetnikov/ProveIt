#!/usr/bin/env python3
"""Independent floating-point diagnostics (not certificates)."""
from pathlib import Path
import json
import numpy as np
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=65

def extremal(k=None,q=None,c=None):
    q=mp.mpf(q)
    a=abs(1-q)
    if not 0<a<1: raise ValueError('Requires 0<q<2 and q != 1')
    if c is None:
        if k is None or k<2: raise ValueError('k must be at least 2')
        c=mp.log(k-1)
    else: c=mp.mpf(c)
    lo=c; hi=c+10
    def eq(t): return mp.tanh((t-c)/2)-a/mp.tanh(a*t/2)
    while eq(hi)<=0: hi=2*hi+1
    for _ in range(230):
        mid=(lo+hi)/2
        if eq(mid)<0: lo=mid
        else: hi=mid
    t=(lo+hi)/2
    r=mp.sinh(a*t/2)**2/mp.cosh((t-c)/2)**2
    R=1+r
    value=q*r/(R-q) if q<1 else q/(q-1)*r/R
    return t,R,value,1/(1+mp.exp(c-t))

def main():
    rng=np.random.default_rng(20260929)
    count=0; max_leverage_error=0.0; max_hessian_error=0.0
    for case in range(300):
        n=int(rng.integers(1,5))
        q=float(rng.uniform(.12,.90) if case%2 else rng.uniform(1.1,1.88))
        bs=[]; As=[]; Ds=[]; kappas=[]; sizes=[]
        for _ in range(n):
            k=int(rng.integers(2,7)); p=rng.dirichlet(np.ones(k)*2)
            B=np.vstack([np.eye(k-1),-np.ones((1,k-1))])
            f=np.sum(p**q)
            g=B.T@(q*p**(q-1)/f)
            A=(q*abs(1-q)/f)*(B.T@np.diag(p**(q-2))@B)
            R=np.sum(p**q)*np.sum(p**(2-q))
            K=q/abs(1-q)*(1-1/R)
            K_direct=float(g@np.linalg.solve(A,g))
            err=abs(K-K_direct)
            max_leverage_error=max(max_leverage_error,err)
            assert err<1e-9
            count+=1
            if q<1:
                D=A+np.outer(g,g)
                tau=float(g@np.linalg.solve(D,g))
                assert abs(tau-K/(1+K))<1e-9
                count+=1
            else: D=A-np.outer(g,g)
            bs.append(g); As.append(A); Ds.append(D);kappas.append(K);sizes.append(k-1)
        offsets=np.cumsum([0]+sizes); dim=sum(sizes)
        direct=np.zeros((dim,dim)); b=np.concatenate(bs)
        signed_block=np.zeros_like(direct)
        for i in range(n):
            sl=slice(offsets[i],offsets[i+1])
            direct[sl,sl]=As[i]*(1 if q>1 else -1)
            signed_block[sl,sl]=Ds[i]
            for j in range(i):
                sj=slice(offsets[j],offsets[j+1])
                direct[sl,sj]=np.outer(bs[i],bs[j]);direct[sj,sl]=direct[sl,sj].T
        target=np.outer(b,b)+signed_block*(1 if q>1 else -1)
        err=float(np.max(np.abs(direct-target)))
        max_hessian_error=max(max_hessian_error,err)
        assert err<1e-9
        count+=1
        if q<1:
            pred=sum(K/(1+K) for K in kappas)>1
            actual=np.linalg.eigvalsh(direct)[-1]>1e-8
            if abs(sum(K/(1+K) for K in kappas)-1)>1e-7:
                assert pred==actual;count+=1
        else:
            v=np.sqrt(kappas)
            M=np.diag(1-np.array(kappas))+np.outer(v,v)
            assert (np.linalg.eigvalsh(M)[0]<-1e-8)==(np.linalg.eigvalsh(direct)[0]<-1e-8)
            count+=1
    # Direct random distributions versus the proposed exact maximum.
    extremal_cases=0
    for k in [2,3,5,17,18,32]:
        for q in [.2,.5,.8,1.2,1.5,1.8]:
            _,rm,_,_=extremal(k=k,q=str(q))
            a=abs(1-q)
            for _ in range(80):
                p=rng.dirichlet(np.full(k,.5))
                R=np.sum(p**(1-a))*np.sum(p**(1+a))
                assert R <= float(rm)+1e-10
                extremal_cases+=1
    count+=extremal_cases
    scaling=[]
    for lam in [mp.mpf('.5'),mp.mpf(2),mp.mpf(4),mp.mpf(7)]:
        for c in [mp.mpf(20),mp.mpf(40),mp.mpf(80)]:
            q=1-lam/c**2
            _,_,theta,_=extremal(c=c,q=q)
            lead=lam/(4+lam)
            corr=(16*lam-4*lam**2-mp.mpf(2)/3*lam**3)/(lam+4)**2
            residual=(theta-lead-corr/c**2)*c**4
            scaling.append({'lambda':str(lam),'c':str(c),'theta':mp.nstr(theta,25),
                            'c4_scaled_remainder':mp.nstr(residual,15)})
    # Finite-dimensional quantum second derivative diagnostic.
    quantum_cases=0
    for q in [.4,.8,1.2,1.6]:
        for k in [2,3,5]:
            p=np.linspace(1,2,k);p=p/p.sum()
            z=rng.normal(size=(k,k))+1j*rng.normal(size=(k,k))
            H=(z+z.conj().T)/2; H-=np.trace(H)/k*np.eye(k);H/=np.linalg.norm(H)
            expected=q*(q-1)*sum(p**(q-2)*np.real(np.diag(H))**2)
            for i in range(k):
                for j in range(i):
                    expected+=2*q*(p[i]**(q-1)-p[j]**(q-1))/(p[i]-p[j])*abs(H[i,j])**2
            h=1e-4
            def f(s): return np.sum(np.linalg.eigvalsh(np.diag(p)+s*H)**q)
            got=(f(h)-2*f(0)+f(-h))/h**2
            assert abs(got-expected)<2e-5
            quantum_cases+=1
    count+=quantum_cases
    result={'status':'PASS: numerical diagnostics only','assertions':count,
            'seed':20260929,'max_leverage_absolute_error':max_leverage_error,
            'max_Hessian_entry_error':max_hessian_error,
            'random_extremal_inequalities':extremal_cases,'quantum_finite_differences':quantum_cases,
            'Shannon_window_diagnostics':scaling,
            'scope':'Floating-point checks do not certify global inequalities or asymptotic error bounds.'}
    out=ROOT/'verification'/'numerical_checks.json';out.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status']); print('Assertions:',count)
    print('Maximum leverage error:',max_leverage_error)
    print('Maximum Hessian identity entry error:',max_hessian_error)
    print('Random extremal comparisons:',extremal_cases)
    print('Quantum finite-difference checks:',quantum_cases)

if __name__=='__main__': main()
