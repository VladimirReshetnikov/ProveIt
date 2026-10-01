#!/usr/bin/env python3
"""Diagnostics for Critical Complements in Fabius Conditioning.

Floating-point calculations, not interval-certified proofs.  Boundary CDFs
are obtained by Fourier inversion.  Prefix densities use a signed Gamma
formula, treating caps >= 64 as infinite (the omitted coupling probability
is explicitly recorded).  Only NumPy and SciPy are required.
"""
from __future__ import annotations
import argparse, csv, json, math, platform
from pathlib import Path
import numpy as np
import scipy
from scipy.integrate import quad, simpson
from scipy.interpolate import CubicSpline
from scipy.optimize import brentq
from scipy.special import gammaln, lambertw

ROOT = Path(__file__).resolve().parents[1]

def log_mgf_one(a: float) -> float:
    if a < 1e-5:
        return a/2-a*a/24+a**4/2880
    return math.log(a / (-math.expm1(-a)))

def mean_truncexp(a: float) -> float:
    if a < 1e-4:
        return a/2-a*a/12+a**4/720
    if a > 700:
        return 1.0
    return 1-a/math.expm1(a)

def variance_truncexp(a: float) -> float:
    if a < 1e-3:
        return a*a/12-a**4/240+a**6/6048
    if a > 700:
        return 1.0
    return 1-(a/(2*math.sinh(a/2)))**2


def variance_constant(q: float, rho: float) -> float:
    result = 0.0
    a = rho/q
    while a < 745:
        result += variance_truncexp(a)-1
        a /= q
    a = rho
    while a > 1e-15:
        result += variance_truncexp(a)
        a *= q
    return result + a*a/(12*(1-q*q))


class Boundary:
    def __init__(self, q: float, rho: float, m: int, grid_power: int = 15):
        if not (0 < q < 1 and rho > 0 and m >= 0):
            raise ValueError('Require 0<q<1, rho>0, m>=0')
        self.q, self.rho, self.m = q,rho,m
        self.cap = rho*q**(-m)
        self.support = self.cap/(1-q)
        self.length = 2*self.support
        count = 2**grid_power
        x = np.arange(count)*self.length/count
        omega = 2*np.pi*np.fft.fftfreq(count, d=self.length/count)
        phi = np.exp(-1j*omega*self.support/2)
        self.K = 0.0
        self.mean = 0.0
        self.variance = 0.0
        a = self.cap
        while a > 1e-15:
            phi *= np.sinc(omega*a/(2*np.pi))
            self.K += log_mgf_one(a)
            self.mean += mean_truncexp(a)
            self.variance += variance_truncexp(a)
            a *= q
        # Leading terms for the omitted deterministic geometric tail.
        self.K += a/(2*(1-q)) - a*a/(24*(1-q*q))
        self.mean += a/(2*(1-q)) - a*a/(12*(1-q*q))
        self.variance += a*a/(12*(1-q*q))
        primitive_coeff = np.zeros(count, dtype=complex)
        primitive_coeff[1:] = phi[1:] / (1j*omega[1:])
        primitive = np.fft.ifft(primitive_coeff).real*count/self.length
        cdf = x/self.length + primitive-primitive[0]
        stop = count//2
        self.x = x[:stop+1]
        self.F = np.clip(cdf[:stop+1], 0, 1)
        self.F[0],self.F[-1] = 0,1
        self.spline = CubicSpline(self.x,self.F)
        self.M = math.exp(self.K)
        g = self.M*np.exp(-self.x)*self.F
        self.ggrid = g
        self.mass = float(simpson(g,x=self.x) + self.M*math.exp(-self.support))
        entr = np.zeros_like(g)
        positive=g>0
        entr[positive]=-g[positive]*np.log(g[positive])
        self.entropy=float(simpson(entr,x=self.x)+
            self.M*math.exp(-self.support)*(self.support+1-self.K))
        self.cdf_monotonicity_error = float(min(0,np.min(np.diff(self.F))))

    def entropy_coefficient(self) -> float:
        """Coefficient of 1/n in the fixed-m relative entropy expansion."""
        center=self.mean+1
        def integrand(u:float)->float:
            v=self.g(u)
            return (u-center)**2*v*math.log(v) if v>0 else 0.
        raw=(quad(integrand,0,self.support,epsabs=1e-11,limit=150)[0]+
             quad(integrand,self.support,self.support+80+self.K,
                  epsabs=1e-11,limit=150)[0])
        covariance=raw+(self.variance+1)*self.entropy
        return variance_constant(self.q,self.rho)/2+1/12-covariance/2

    def g(self,u: float) -> float:
        if u <= 0: return 0.0
        F = 1.0 if u >= self.support else float(np.clip(self.spline(u),0,1))
        return self.M*math.exp(-u)*F


def prefix_density(n: int,m: int,q: float,rho: float):
    k=n-m
    if k<2: raise ValueError('Need n-m>=2')
    caps=[]
    omitted=0.0
    mean=float(k)
    for r in range(m+1,n+1):
        if -r*math.log(q)+math.log(rho)> math.log(745):
            break
        a=rho*q**(-r)
        mean += mean_truncexp(a)-1
        if a<64:
            caps.append(a)
        else:
            omitted += math.exp(-a)
    shifts=np.array([0.0]); weights=np.array([1.0]); logZ=0.0
    for a in caps:
        shifts=np.r_[shifts,shifts+a]
        weights=np.r_[weights,-math.exp(-a)*weights]
        logZ+=math.log1p(-math.exp(-a))
    scale=math.exp(-logZ)
    lgamma=float(gammaln(k))
    def density(s:float)->float:
        z=s-shifts
        pos=z>0
        if not np.any(pos):return 0.0
        terms=np.exp((k-1)*np.log(z[pos])-z[pos]-lgamma)
        return max(0.0,float(scale*np.dot(weights[pos],terms)))
    return density,mean,omitted


def finite_metrics(n:int,m:int,b:Boundary)->dict:
    f,muB,omitted=prefix_density(n,m,b.q,b.rho)
    mu=muB+b.mean
    def weight(u:float)->float:return f(mu-u)
    A0=b.support
    # The prefix sum cannot be negative.  Split the exponential tail at
    # a finite cutoff; adaptive quadrature on [A0,mu] misses this tail
    # when mu is very large. Its omitted g-mass is explicitly recorded.
    upper=min(mu,A0+80+b.K)
    endpoint=min(upper,A0)
    normalizer=quad(lambda u:weight(u)*b.g(u),0,endpoint,
                    epsabs=1e-13,epsrel=1e-10,limit=150)[0]
    if upper>A0:
        normalizer+=quad(lambda u:weight(u)*b.g(u),A0,upper,
                         epsabs=1e-13,epsrel=1e-10,limit=150)[0]
    # Locate the two likelihood crossings to avoid missing the narrow edges.
    dense=np.linspace(0,min(mu,A0),2001)
    vals=np.array([b.g(float(u))-normalizer for u in dense])
    cuts=[0.0,endpoint]
    for i in range(len(dense)-1):
        if vals[i]*vals[i+1]<0:
            cuts.append(brentq(lambda u:b.g(u)-normalizer,
                              float(dense[i]),float(dense[i+1])))
    if upper>A0:
        cuts.extend([upper]+[A0+d for d in (1,2,4,8,16,32,64) if A0+d<upper])
        crossing=b.K-math.log(normalizer)
        if A0<crossing<upper:cuts.append(crossing)
    cuts=sorted(set(cuts))
    overlap=0.0; entropy_term=0.0
    for l,r in zip(cuts,cuts[1:]):
        overlap+=quad(lambda u:weight(u)*min(1,b.g(u)/normalizer),l,r,
                      epsabs=1e-12,epsrel=1e-9,limit=150)[0]
        def efun(u:float)->float:
            g=b.g(u)
            return weight(u)*g*math.log(g)/normalizer if g>0 else 0.0
        entropy_term+=quad(efun,l,r,epsabs=1e-11,epsrel=1e-9,limit=150)[0]
    eps=1/math.sqrt(2*math.pi*n)
    kl=entropy_term-math.log(normalizer)
    tv_prediction=eps*(math.log(1/eps)+1+b.K)
    kl_prediction=math.log(1/eps)-b.entropy
    # Exact compact boundary deficit, responsible for slow TV convergence.
    deficit=quad(lambda u:max(0.,1-b.g(u)/eps),0,b.support,
                  epsabs=1e-11,epsrel=1e-10,limit=150)[0]
    corrected_overlap=tv_prediction-eps*deficit
    entropy_coefficient=b.entropy_coefficient()
    return dict(n=n,m=m,q=b.q,rho=b.rho,A=normalizer,A_ratio=normalizer/eps,
                overlap=overlap,overlap_asymptotic=tv_prediction,
                scaled_overlap_residual=overlap/eps-math.log(1/eps)-1-b.K,
                kl=kl,kl_asymptotic=kl_prediction,kl_residual=kl-kl_prediction,
                boundary_deficit=deficit,corrected_overlap=corrected_overlap,
                corrected_overlap_residual=overlap-corrected_overlap,
                entropy_coefficient=entropy_coefficient,
                corrected_kl_residual=kl-kl_prediction-entropy_coefficient/n,
                omitted_cap_coupling_bound=omitted,
                omitted_profile_tail_mass=(math.exp(b.K-upper) if upper<mu else 0.0))


def roots(z:float)->tuple[float,float]:
    if z<=0:raise ValueError('z must be positive')
    arg=-math.exp(-1-z)
    low=-float(lambertw(arg,0).real)
    high=-float(lambertw(arg,-1).real)
    return low,high

def write_csv(name:str,rows:list[dict])->None:
    p=ROOT/'data'/name
    with p.open('w',newline='') as h:
        writer=csv.DictWriter(h,fieldnames=list(rows[0]))
        writer.writeheader();writer.writerows(rows)

def main()->None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--grid-power',type=int,default=15)
    args=parser.parse_args()
    (ROOT/'data').mkdir(exist_ok=True)
    boundary_rows=[]; checks={}
    for rho in [1.,1.25,1.5,1.75]:
        for m in [0,1,2]:
            b=Boundary(.5,rho,m,args.grid_power)
            b2=Boundary(.5,rho,m,args.grid_power+1)
            boundary_rows.append(dict(q=.5,rho=rho,m=m,K=b2.K,
               entropy=b2.entropy,information_gap=b2.entropy-1,
               entropy_coefficient=b2.entropy_coefficient(),
               mass=b2.mass,grid_entropy_difference=abs(b2.entropy-b.entropy)))
    write_csv('boundary_constants.csv',boundary_rows)
    b=Boundary(.5,1.,0,args.grid_power+1)
    rows=[finite_metrics(n,0,b) for n in [32,128,512,2048,8192,32768]]
    write_csv('finite_geometric_metrics.csv',rows)
    crossover=[]
    max_residual=0.0
    for c in [.02,.05,.1,.2,.5,1.,2.,5.,10.,50.]:
        lo,hi=roots(1/(2*c))
        residual=max(abs(lo-1-math.log(lo)-1/(2*c)),
                     abs(hi-1-math.log(hi)-1/(2*c)))
        max_residual=max(max_residual,residual)
        crossover.append(dict(c=c,y_minus=lo,y_plus=hi,C=c*(hi-lo),
                              gaussian_reference=2*math.sqrt(c)))
    write_csv('crossover.csv',crossover)
    checks['lambert_rate_identity_max_residual']=max_residual
    checks['boundary_mass_max_error']=max(abs(r['mass']-1) for r in boundary_rows)
    checks['boundary_entropy_grid_max_change']=max(r['grid_entropy_difference'] for r in boundary_rows)
    checks['all_information_gaps_nonnegative']=all(r['information_gap']>=-1e-10 for r in boundary_rows)
    checks['all_overlaps_in_unit_interval']=all(0<r['overlap']<1 for r in rows)
    checks['all_relative_entropies_nonnegative']=all(r['kl']>=0 for r in rows)
    checks['entropy_coefficient_last_scaled_error']=abs(rows[-1]['n']*rows[-1]['kl_residual']-rows[-1]['entropy_coefficient'])
    checks['normalizer_ratio_within_tolerance']=all(.97<r['A_ratio']<1.03 for r in rows)
    checks['kl_residual_decreases']=all(abs(rows[i+1]['kl_residual'])<abs(rows[i]['kl_residual']) for i in range(len(rows)-1))
    checks['tv_residual_decreases']=all(abs(rows[i+1]['scaled_overlap_residual'])<abs(rows[i]['scaled_overlap_residual']) for i in range(len(rows)-1))
    assert checks['normalizer_ratio_within_tolerance']
    assert checks['kl_residual_decreases']
    assert checks['tv_residual_decreases']
    checks['scope']='Floating-point diagnostics; no interval certification or Lean proof.'
    checks['environment']=dict(python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__)
    (ROOT/'data'/'verification.json').write_text(json.dumps(checks,indent=2)+'\n')
    print(json.dumps(checks,indent=2))
    print('\nFinite dyadic metrics:')
    for r in rows:
        print(r['n'], 'overlap=',r['overlap'],'TV residual=',r['scaled_overlap_residual'],
              'KL residual=',r['kl_residual'])

if __name__=='__main__':main()
