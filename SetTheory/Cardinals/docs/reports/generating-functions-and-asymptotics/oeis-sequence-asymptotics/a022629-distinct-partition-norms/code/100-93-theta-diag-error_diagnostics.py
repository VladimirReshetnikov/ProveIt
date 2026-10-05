#!/usr/bin/env python3
"""Integrate a mathematically pointwise modulus envelope for omitted arcs.
The bound on the characteristic function is rigorous algebraically; integrals
are numerical (QUADPACK error estimates), not interval-certified enclosures.
"""
import json,sys,math
import numpy as np
from scipy.integrate import quad
from diagnostics import select_case,LD,PI

def omitted_arc_diagnostics(s,J,Y=11,H=15,bins_per_W=64):
    K=float(s['K']);W=float(s['W']);a=s['a'];t=float(s['t']);V=float(s['V']);rootV=math.sqrt(V)
    k=s['k'];f=a*np.log(k)-s['t']*k
    good=k[(k>K/2)&(abs(f)<=H)]
    low=int(min(good));high=int(max(good));step=max(1,int(W/bins_per_W))
    starts=np.arange(low,high+1,step);ends=np.minimum(starts+step-1,high)
    def variance(k):
        q=1/(1+np.exp(np.abs(a*np.log(k)-t*k)));return q*(1-q)
    weights=np.minimum(variance(starts),variance(ends))
    M=ends-starts+1.;centers=(starts+ends)/2.;Ulower=float(sum(weights*M));vmax=float(max(weights))
    centers-=K
    def fourier(th):
        # Sum of constant lower weights over each consecutive integer block,
        # after removing exp(i K theta), which does not change modulus.
        sums=M*np.sinc(M*th/(2*math.pi))/np.sinc(th/(2*math.pi))
        return np.sum(weights*sums*np.exp(1j*centers*th))
    def envelope(th):
        E=Ulower-(np.exp(1j*math.remainder(K*th,2*math.pi))*fourier(th)).real
        return math.exp(-max(0.,E))
    def phasefree(r):
        return math.exp(-max(0.,Ulower-abs(fourier(r/W))))/W
    boundary=2*math.pi*(J+.5)/K;theta0=min(math.pi,10/W)
    pfree,pfreeerr=quad(phasefree,boundary*W,theta0*W,epsabs=1e-50,epsrel=5e-10,limit=400) if boundary<theta0 else (0.,0.)
    far=(math.pi-theta0)*math.exp(-Ulower+vmax/math.sin(theta0/2))
    # Integrate every omitted gap through the last selected Fourier cell.
    theta_centers=[2*math.pi*j*float(s['C'])/V for j in range(J+1)]
    cuts=[]
    for j,c in enumerate(theta_centers):
        left=max(0.,2*math.pi*(j-.5)/K);right=min(boundary,2*math.pi*(j+.5)/K)
        lwin=c-Y/rootV;rwin=c+Y/rootV
        if lwin>left:cuts.append((left,min(lwin,right)))
        if rwin<right:cuts.append((max(rwin,left),right))
    gap=0.;gaperr=0.
    for l,r in cuts:
        # Shift and rescale to avoid missing a narrow boundary contribution.
        lscaled=l*rootV;rscaled=r*rootV
        v,e=quad(lambda x:envelope(x/rootV),lscaled,rscaled,epsabs=1e-50,epsrel=5e-9,limit=400)
        gap+=v/rootV;gaperr+=e/rootV
    norm=math.sqrt(2*math.pi*V)/math.pi
    return dict(J=J,Y=Y,block_count=len(M),block_width=step,U_lower=Ulower,U_actual=float(s['U']),variance_max_lower=vmax,outer_boundary_theta=boundary,global_far_theta=theta0,omitted_normalized_envelope_integral=norm*(gap+pfree+far),gap_normalized=norm*gap,satellite_tail_normalized=norm*pfree,global_far_normalized=norm*far,quadrature_reported_error=norm*(gaperr+pfreeerr),warning='Pointwise modulus bound is rigorous; envelope integrals are numerical, not interval-certified.')

if __name__=='__main__':
    path=sys.argv[1];d=json.load(open(path))
    for r in d['rows']:
        s=select_case(r['a'],r['lam_target'],r['phase_target'])
        out=omitted_arc_diagnostics(s,8 if r['lam_target']==4 else 10)
        r['omitted_arcs']=out
        print(r['a'],r['lam_target'],r['phase_target'],out['omitted_normalized_envelope_integral'],out['quadrature_reported_error'],flush=True)
    json.dump(d,open(path,'w'),indent=2)
