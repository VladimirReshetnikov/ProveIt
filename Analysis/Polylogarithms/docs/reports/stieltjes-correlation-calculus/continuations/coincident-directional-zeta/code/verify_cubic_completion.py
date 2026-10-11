#!/usr/bin/env python3
"""Targeted independent multivariate check of the cubic holomorphic completion.

Global side: classical Hurwitz Fourier/Tornheim formula, using the
spectral agent's Jonquiere + incomplete-Gamma Mellin evaluator.
Direct side: an ordinary, absolutely convergent Hurwitz-product integral
with stable Taylor differences near the lower endpoint. No Tornheim,
Fourier or global spectral formula enters the direct side.

These are floating-point diagnostics, not interval certificates.
"""
from pathlib import Path
import json
import time
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
# The independent Mellin evaluator is copied from agent_spectral/verify_rays.py
# so the delivered check remains self-contained after packaging.
mp.mp.dps=65
K=62
N=155

def tornheim(a, b, c):
    ga, gb = mp.gamma(1-a), mp.gamma(1-b)
    za = [(-1)**k*mp.zeta(a-k)/mp.factorial(k) for k in range(K+1)]
    zb = [(-1)**k*mp.zeta(b-k)/mp.factorial(k) for k in range(K+1)]
    terms = [ga*gb/(a+b+c-2)]
    terms.extend(ga*zb[k]/(a+c-1+k) for k in range(K+1))
    terms.extend(gb*za[k]/(b+c-1+k) for k in range(K+1))
    terms.extend(za[j]*zb[k]/(c+j+k) for j in range(K+1)
                 for k in range(K+1))
    small = mp.fsum(terms)
    head = [mp.power(j, -a) for j in range(1,N)]
    other = [mp.power(j, -b) for j in range(1,N)]
    large = mp.fsum(
        mp.gammainc(c,k,mp.inf)/mp.power(k,c)
        * mp.fsum(head[j-1]*other[k-j-1] for j in range(1,k))
        for k in range(2,N+1)
    )
    return (small+large)/mp.gamma(c)



def hz(lam):
    return mp.zeta(1-lam)+1/lam


def stable_coeffs(lam,terms):
    coeff=[hz(lam)]
    for k in range(1,terms+1):
        coeff.append((-1)**k*mp.rf(1-lam,k)*mp.zeta(1+k-lam)/mp.factorial(k))
    return coeff


def direct_completion(ls,taylor_terms=80,split='0.125'):
    cs=[stable_coeffs(lam,taylor_terms) for lam in ls]
    split=mp.mpf(split)
    def local_values(i,x):
        lam=ls[i]
        row=cs[i]
        if x<split:
            d1=x*mp.polyval(list(reversed(row[1:])),x)
            d2=x*x*mp.polyval(list(reversed(row[2:])),x)
            return row[0]+d1,d1,d2
        h=mp.zeta(1-lam,1+x)+1/lam
        d1=h-row[0]
        return h,d1,d1-x*row[1]
    def remainder(x):
        if x==0:return mp.mpf(0)
        hv=[local_values(i,x) for i in range(3)]
        result=mp.fprod(v[0] for v in hv)
        for i in range(3):
            j,k=[v for v in range(3) if v!=i]
            smooth_difference=(cs[j][0]*hv[k][1]+cs[k][0]*hv[j][1]
                               +hv[j][1]*hv[k][1])
            result+=mp.power(x,ls[i]-1)*smooth_difference
        for k in range(3):
            i,j=[v for v in range(3) if v!=k]
            result+=mp.power(x,ls[i]+ls[j]-2)*hv[k][2]
        return result
    integral=mp.quad(remainder,[0,split,mp.mpf('.5'),1])
    exact_terms=1/(sum(ls)-2)
    for k in range(3):
        i,j=[v for v in range(3) if v!=k]
        exact_terms+=cs[k][0]/(ls[i]+ls[j]-1)
    return integral+exact_terms,integral,exact_terms


def global_completion(ls):
    K2=lambda a,b:2*mp.gamma(a)*mp.gamma(b)*mp.cos(mp.pi*(a-b)/2)*mp.zeta(a+b)/(2*mp.pi)**(a+b)
    tornheim_values=[]
    phase_sum=mp.mpc(0)
    for k in range(3):
        i,j=[v for v in range(3) if v!=k]
        val=tornheim(ls[i],ls[j],ls[k])
        tornheim_values.append(val)
        phase_sum+=mp.cos(mp.pi*(ls[i]+ls[j]-ls[k])/2)*val
    K3=2*mp.fprod(mp.gamma(lam) for lam in ls)*phase_sum/(2*mp.pi)**sum(ls)
    result=K3+1/mp.fprod(ls)
    for k in range(3):
        i,j=[v for v in range(3) if v!=k]
        result+=K2(ls[i],ls[j])/ls[k]
        result-=hz(ls[i])*hz(ls[j])/ls[k]
        result+=(1-ls[k])*mp.zeta(2-ls[k])/(ls[i]+ls[j])
    return result,tornheim_values


def enc(z,n=55):
    return {'real':mp.nstr(mp.re(z),n),'imag':mp.nstr(mp.im(z),n)}


def main():
    global K,N
    triples=[(mp.mpf('.03'),mp.mpf('.07'),mp.mpf('.11')),
             (mp.mpc('.04','.03'),mp.mpc('-.02','.01'),mp.mpc('.06','-.02'))]
    rows=[]
    originals=[]
    for idx,ls in enumerate(triples):
        start=time.time()
        direct,integral,finite=direct_completion(ls)
        glob,tvals=global_completion(ls)
        err=abs(glob-direct)
        row={'lambda':[enc(v) for v in ls],'direct':enc(direct),'global':enc(glob),
             'integral_remainder':enc(integral),'explicit_finite_terms':enc(finite),
             'tornheim_values':[enc(v) for v in tvals],'absolute_error':mp.nstr(err,10),
             'elapsed_seconds':time.time()-start}
        rows.append(row)
        originals.append((direct,glob))
        print('case',idx+1,'error',mp.nstr(err,10),'seconds',round(row['elapsed_seconds'],2),flush=True)
        assert err<mp.mpf('1e-35')
    # A larger local Taylor truncation and longer independent Mellin tails.
    ls=triples[-1]
    K=72;N=180
    direct_repeat,_,_=direct_completion(ls,taylor_terms=92,split='0.1')
    global_repeat,_=global_completion(ls)
    repetition={'direct_change':mp.nstr(abs(direct_repeat-originals[-1][0]),10),
                'global_change':mp.nstr(abs(global_repeat-originals[-1][1]),10),
                'repeat_cross_error':mp.nstr(abs(global_repeat-direct_repeat),10),
                'jonquiere_terms':K+1,'incomplete_gamma_tail_index':N,
                'direct_taylor_terms':93,'direct_taylor_split':'0.1'}
    out={'precision_decimal':mp.mp.dps,'mpmath_version':mp.__version__,
         'method':'Direct subtracted Hurwitz-product quadrature vs Jonquiere Mellin Tornheim completion',
         'rigorous_certificate':False,'convergence_scope':'Re lambda_i > -1 and Re(lambda_i+lambda_j)>-1; explicit denominators away from zero',
         'initial_jonquiere_terms':63,'initial_incomplete_gamma_tail_index':155,
         'initial_direct_taylor_terms':81,'initial_direct_taylor_split':'0.125',
         'cases':rows,'repeat':repetition}
    (ROOT/'results'/'cubic_completion_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('repeat',json.dumps(repetition),flush=True)

if __name__=='__main__':main()
