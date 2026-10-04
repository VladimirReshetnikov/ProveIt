#!/usr/bin/env python3
"""Bounded independent checks of the complex-disk proof inequalities.
Complex floating computations corroborate, not certify, the analytic proof.
Tiny conjugates are handled by explicit q0^4 upper bounds, not by pretending
floating underflow computes their actual values. No upstream execution.
"""
import cmath
from fractions import Fraction
import json
import math

COUNT=0

def need(ok,message):
    global COUNT
    COUNT+=1
    if not ok:raise ValueError(message)

def branch_data(name):
    if name=='A+':return Fraction(2,3),Fraction(1),1
    if name=='A-':return Fraction(2,3),Fraction(1),-1
    return Fraction(5,7),Fraction(5,4),1

def Nprime(name,r):
    if name=='A+':return (12*r*r+8*r-7)/3
    if name=='A-':return (12*r*r-24*r+9)/3
    return (75*r*r+50*r-39)/14

def Nsecond(name,r):
    if name=='A+':return 8*r+Fraction(8,3)
    if name=='A-':return 8*r-8
    return (150*r+50)/14

def exact_bounds():
    cases=0
    for num in range(400,4001):
        r=Fraction(num,4)
        need(Fraction(2,3)*(r*r-Fraction(5,2)*r+Fraction(7,16))>=Fraction(3,5)*r*r,'Re pL lower')
        difference=Fraction(1,4)*(3*r*r+4*r+1)+Fraction(1,16)*(3*r+2)+Fraction(1,64)
        need(difference<r*r,'cubic perturbation')
        need(Fraction(2,3)*r*(r-1)**2-r*r>=Fraction(3,5)*r**3,'Re rpL lower')
        need(3*r*r-Fraction(3,2)*r-Fraction(1,8)>2*r*r,'D lower')
        need(6*r+3<r*r,'tail coefficient budget')
        for name in ['A+','A-','B']:
            alpha,lam,eps=branch_data(name)
            need(alpha*(r+Fraction(5,4))<r,'complex p bound')
            need(Nprime(name,r)>3*r*r,'N prime')
            need(0<Nsecond(name,r)<12*r,'N second')
        cases+=1
    return cases

def log1p_small(z):
    return sum((1 if j%2 else -1)*z**j/j for j in range(1,9))

def g_small(z):
    return -sum(math.comb(2*j,j)*z**j/(2*j*4**j) for j in range(1,9))

def complex_cases():
    records=[]
    ln2=math.log(2)
    for name in ['A+','A-','B']:
        al,la,eps=branch_data(name);alpha=float(al);lam=float(la)
        for r0 in [100.0,101.5,128.0,160.0,200.0]:
            p0=alpha*(r0+eps);y0=(lam-alpha)*(r0+eps)-1
            q0=2**(-p0);eps0=16*q0
            max_ratio=0.0;count=0
            for radius in [0.0,0.125,0.25]:
                for j in range(64):
                    h=radius*cmath.exp(2j*math.pi*j/64)
                    r=r0+h;p=alpha*(r+eps);L=lam*(r+eps);y=L-p-1
                    d=cmath.exp(-p*ln2)+2*cmath.exp(-(p+y)*ln2)
                    a=cmath.exp(-2*(p+y)*ln2)/(1+d)**2
                    Phi=log1p_small(d)+g_small(a)
                    ellA=L*ln2+Phi
                    need(abs(d)<2*q0,'d disk bound')
                    need(abs(a)<q0*q0,'a disk bound')
                    need(abs(Phi)<5*q0,'Phi disk bound')
                    need((p*L).real>=0.6*r0*r0,'sample Re pL')
                    need((p*ellA).real>0.5*r0*r0*ln2,'ellA logarithmic lower')
                    # This verifies |u|<q0^4 without exponentiating to underflow.
                    need(-2*(p*ellA).real<4*math.log(q0),'u log bound')
                    ellS_without_conjugates=2*p*ellA-ln2
                    lower_Re_r_ellS=(r*ellS_without_conjugates).real-abs(r)*5*q0**4
                    need(lower_Re_r_ellS>r0**3*ln2,'ellS logarithmic lower')
                    need(-2*lower_Re_r_ellS<4*math.log(q0),'v log bound')
                    B=2*p*(r-1)
                    # Analytic proven bound covers all omitted tiny conjugates.
                    E_upper=(abs(B*Phi)+(6*r0+3)*q0**4)/ln2
                    gamma=4/3 if name.startswith('A') else 25/14
                    denom=complex(float(Nprime(name,Fraction(r0))))+float(Nsecond(name,Fraction(r0)))*h/2+gamma*h*h
                    need(abs(denom)>2*r0*r0,'sample D bound')
                    need(E_upper<18*r0*r0*q0,'sample E upper')
                    ratio=E_upper/abs(denom)/eps0
                    need(ratio<1,'f versus epsilon0')
                    max_ratio=max(max_ratio,ratio);count+=1
            records.append({'branch':name,'r0':r0,'complex_samples':count,'max_f_upper_over_epsilon0':format(max_ratio,'.12g')})
    return records

def run():
    exact=exact_bounds();samples=complex_cases()
    return {'status':'PASS','scope':'Exact rational polynomial bounds plus bounded complex floating corroboration. Not interval certification and not a proof by sampling. No principal logS or arcoshS used.','active_checks':COUNT,'exact_r0_grid_cases':exact,'complex_records':samples,'total_complex_samples':sum(x['complex_samples'] for x in samples)}

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
