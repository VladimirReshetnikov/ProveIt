#!/usr/bin/env python3
"""Non-certified finite floating-point diagnostics for Report198 / A373273.

No numerical value produced by this file is a remainder bound, an effective
onset, an interval certificate, a proof of eventual monotonicity, or a certified
integer inverse. Exact counts are read from the pinned table after hash checks.
The complete builder independently regenerates that table before this step.
"""
from __future__ import annotations
import cmath
import math
from pathlib import Path
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
import build as builder
import verify

A=math.pi**2/6
GAMMA=0.577215664901532860606512090082402431
C=1.5-GAMMA/2
K=9607/20736-GAMMA/24
SAMPLES=(50,100,200,500,1000,2000,2500)


def display(value):
    if not math.isfinite(value):raise ValueError('non-finite diagnostic')
    return format(value,'.17g')


def logphi(x):
    k=math.sqrt(A);ell=math.log(x/k)
    bracket=x/k*(ell/2+C)-7*math.sqrt(math.pi)/(16*math.sqrt(k))*math.sqrt(x)+ell/24+K+1/(8*A)
    if bracket<=0:raise ValueError('smooth-template bracket is not positive')
    return 2*k*x-math.log(4*math.sqrt(3))-2*math.log(x)+math.log(bracket)


def approximate_root(logtarget,n):
    lo,hi=math.sqrt(n)/2,2*math.sqrt(n)
    if not logphi(lo)<logtarget<logphi(hi):
        raise ValueError('diagnostic root not bracketed')
    for _ in range(100):
        mid=(lo+hi)/2
        if logphi(mid)<logtarget:lo=mid
        else:hi=mid
    return (lo+hi)/2


def cexpm1(z):
    if abs(z)>=.25:return cmath.exp(z)-1
    term=total=z
    for k in range(2,50):
        term*=z/k
        new=total+term
        if new==total:break
        total=new
    return total


def clog1p(z):
    if abs(z)>=.25:return cmath.log(1+z)
    term=total=z
    for k in range(2,100):
        term*=-z
        new=total+term/k
        if new==total:break
        total=new
    return total


def truncated_boltzmann(t):
    # sum_m m*mu_m = sum_m B(tm). The finite cutoffs below are fixed
    # numerical choices; no rigorous truncation or rounding enclosure is made.
    max_linear=math.ceil(38/t.real)
    linear=sum((1/cexpm1(t*m) for m in range(1,max_linear+1)),0j)
    correction=0j
    max_collision=math.ceil(24/t.real)
    for m in range(1,max_collision+1):
        max_j=max(2,math.ceil(45/(t.real*m)))
        values=[-cexpm1(-t*j)*cmath.exp(-t*m*j) for j in range(1,max_j)]
        logq=sum((clog1p(-v) for v in values),0j)
        correction+=m*(-cexpm1(logq)-sum(values,0j))
    return linear+correction,max_linear,max_collision


def run():
    counts,partitions=verify.reference()
    rows=[]
    for n in SAMPLES:
        tau=math.sqrt(A/(n-1/24));ell=math.log(1/tau)
        prediction=(ell/2+C)/tau-7*math.sqrt(math.pi)/(16*math.sqrt(tau))+(1/24+1/(4*A))*ell+K+(7/8-GAMMA/4)/A
        mean=counts[n]/partitions[n]
        root=approximate_root(math.log(counts[n]),n)
        index_error=root*root+1/24-n
        rows.append({'n':n,'tau':display(tau),'exact_integer_ratio_float':display(mean),
                     'canonical_template':display(prediction),
                     'canonical_error_over_sqrt_tau':display((mean-prediction)/math.sqrt(tau)),
                     'smooth_template_root':display(root),
                     'smooth_inverse_real_index_error':display(index_error),
                     'smooth_inverse_scaled_error':display(index_error*math.sqrt(root)*math.log(root))})
    sectors=[]
    for r in (.01,.003,.001):
        for arg in (-.2,0,.2):
            t=r*cmath.exp(1j*arg)
            value,linear,collision=truncated_boltzmann(t)
            ell=cmath.log(1/t)
            prediction=(ell/2+C)/t-7*math.sqrt(math.pi)/(16*cmath.sqrt(t))+ell/24+K
            residual=(value-prediction)/cmath.sqrt(t)
            sectors.append({'abs_t':display(r),'arg_t_radians':display(arg),
                            'linear_cutoff_m':linear,'collision_cutoff_m':collision,
                            'j_cutoff_rule':'1 <= j < max(2,ceil(45/(Re(t)*m)))',
                            'scaled_remainder_real':display(residual.real),
                            'scaled_remainder_imaginary':display(residual.imag)})
    return {'schema':'report198-noncertified-diagnostics-v1','report':198,'sequence':'A373273',
            'arithmetic':'Python binary64 float/complex and system math/cmath',
            'exact_input_sha256':verify.REFERENCE_SHA256,
            'certifies_remainder':False,'certifies_inverse_ceiling':False,
            'certifies_effective_onset':False,'certifies_truncation_or_rounding':False,
            'scope':'Finite numerical diagnostics only. No bounded error constant, effective onset, exact integer crossing, or analytic theorem is inferred.',
            'canonical_and_smooth_inverse':rows,'sector_boltzmann':sectors}


if __name__=='__main__':
    sys.stdout.buffer.write(builder.canonical(run()))
