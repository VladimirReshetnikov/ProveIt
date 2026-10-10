#!/usr/bin/env python3
"""Regenerate or replay exact certificates accompanying the article.

Default: replay frozen certificates and run exact algebraic tests.
--regenerate: generate certificates using floating point ONLY to propose root
brackets. Every accepted endpoint sign is then decided with rational arithmetic.

No proof-assistant formalization is claimed. The unbounded analytic theorems
are proved in article.tex; these checks test their finite interfaces.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from itertools import product, combinations
from math import comb, factorial
from pathlib import Path
import json, sys, time
from exact_evaluator import (QC, coefficients, centered_moments, enclosure,
                             half_circle, as_record)
if hasattr(sys, 'set_int_max_str_digits'): sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
GAUSS = [(2,1),(1,1,1),(2,1,2),(1,2,1,1),(2,1,1,2),
         (1,1,1,1,1),(2,1,2,1,1),(1,1,1,1,1,1)]
ANGULAR = [(1,1)] + GAUSS[1:]
COUNTS = {}

def tick(name, n=1): COUNTS[name] = COUNTS.get(name,0)+n

def brute_coeff(index,n):
    out = Q(0)
    for tail in combinations(range(1,n),len(index)-1):
        ns = (n,)+tuple(reversed(tail))
        den = 1
        for k,s in zip(ns,index): den *= k**s
        out += Q(1,den)
    return out

def exact_tests():
    for depth in range(1,5):
        for ind in product((1,2,3),repeat=depth):
            c = coefficients(ind,24)
            for n in range(1,10):
                assert c[n] == brute_coeff(ind,n)
                tick('strict_coefficients_vs_brute_force')
            assert all(c[n]==0 for n in range(1,depth))
            lead = 1
            for j,s in enumerate(ind): lead *= (depth-j)**s
            assert c[depth]==Q(1,lead)
            tick('initial_moments_and_leading_coefficient')
            nums,den = centered_moments(ind,24)
            for k in range(24):
                direct = sum(((-1)**(k-j)*comb(k,j)*2**j*c[j+1]
                              for j in range(k+1)),Q(0))
                assert Q(nums[k],den)==direct
                assert abs(direct)<=2**(depth-1)
                tick('centered_moments_binomial_and_norm')
            # Compensator algebra for an arbitrary monic P: positivity is
            # deliberately NOT asserted for these artificial roots.
            roots = [Q(j+1,depth+2) for j in range(depth-1)]
            p,d = [Q(1)],[Q(1)]
            for r in roots:
                pn=[Q(0)]*(len(p)+1)
                dn=[Q(0)]*(len(d)+1)
                for j,v in enumerate(p): pn[j]-=r*v; pn[j+1]+=v
                for j,v in enumerate(d): dn[j]+=v; dn[j+1]-=r*v
                p,d=pn,dn
            for k in range(10):
                lhs=sum((d[j]*c[k+depth-j] for j in range(len(d))),Q(0))
                rhs=sum((p[j]*c[k+j+1] for j in range(len(p))),Q(0))
                assert lhs==rhs
                tick('compensation_moment_identity')
    # Independent unsigned Stirling recurrence.
    stir=[[0]*32 for _ in range(32)]; stir[0][0]=1
    for n in range(1,32):
        for k in range(1,n+1): stir[n][k]=stir[n-1][k-1]+(n-1)*stir[n-1][k]
    for depth in range(1,9):
        c=coefficients((1,)*depth,30)
        for n in range(1,31):
            assert c[n]==Q(stir[n][depth],factorial(n))
            tick('all_ones_stirling_moments')
    import sympy as s
    x,t,z=s.symbols('x t z', real=True)
    ks={d:sum((-1)**j*s.pi**(2*j)*x**(d-1-2*j)/
              (s.factorial(2*j+1)*s.factorial(d-1-2*j))
              for j in range((d-1)//2+1)) for d in range(1,13)}
    for d in range(2,13):
        assert s.expand(s.diff(ks[d],x)-ks[d-1])==0
        tick('logistic_kernel_derivatives')
    assert s.expand(ks[3]-(x*x-s.pi**2/3)/2)==0
    assert s.expand(ks[4]-(x**3-s.pi**2*x)/6)==0
    tick('explicit_depth_three_four_kernels',2)
    badz=1-s.sqrt(2)/2+s.I*s.sqrt(2)/2
    assert s.simplify((1-badz)**4+1)==0
    assert s.simplify(s.expand_complex(badz*s.conjugate(badz))-(2-s.sqrt(2)))==0
    tick('generalized_positive_kernel_counterexample',2)
    # Negative controls: a weak prefix is not a strict prefix, and a
    # deliberately perturbed centered moment must not pass equality.
    assert coefficients((1,1),3)[1] != Q(1)
    nums,den=centered_moments((2,1,2),10)
    assert Q(nums[7]+den,den) != Q(nums[7],den)
    tick('rejected_negative_controls',2)
    # Positive rational atomic Stieltjes transforms: independently test the
    # radial-argument derivative appearing in the radial-argument lemma of the article.
    configurations = [([Q(1,4)],[1]), ([Q(1,5),Q(4,5)],[2,1]),
                      ([Q(1,10),Q(1,2),Q(9,10)],[1,2,3]),
                      ([Q(1,3),Q(2,3)],[1,1])]
    for rho in (Q(1,4),Q(1,2),Q(3,4),Q(1)):
        for t in (Q(1,10),Q(1,2),Q(1),Q(2),Q(10)):
            unit=2*half_circle(t); z=rho*unit
            for nodes,weights in configurations:
                H,Hp=QC(),QC()
                for u,w in zip(nodes,weights):
                    den=1-u*z
                    H += QC(Q(w))/den
                    Hp += QC(Q(w)*u)/(den*den)
                assert (unit*Hp/H).im > 0
                tick('rational_atomic_radial_argument_signs')

# Small independent rational interval implementation for log and pi controls.
def ia(a,b): return (a[0]+b[0],a[1]+b[1])
def ine(a): return (-a[1],-a[0])
def imul(a,b):
    vals=[x*y for x in a for y in b]
    return (min(vals),max(vals))
def iscale(a,q): return imul(a,(q,q))
def cmul(a,b):
    return (ia(imul(a[0],b[0]),ine(imul(a[1],b[1]))),
            ia(imul(a[0],b[1]),imul(a[1],b[0])))
def atan_interval(x,n):
    v=sum(((-1)**j*x**(2*j+1)/Q(2*j+1) for j in range(n)),Q(0))
    e=x**(2*n+1)/Q(2*n+1)
    return (v,v+e) if n%2==0 else (v-e,v)
def log2_interval(n=160):
    x=Q(1,3)
    v=2*sum((x**(2*j+1)/Q(2*j+1) for j in range(n)),Q(0))
    e=2*x**(2*n+1)/Q(2*n+1)/(1-x*x)
    return (v,v+e)
def pi_interval():
    return ia(iscale(atan_interval(Q(1,5),120),Q(16)),
              iscale(atan_interval(Q(1,239),40),Q(-4)))
def gaussian_allones_reference(depth):
    base=(iscale(log2_interval(),Q(-1,2)),iscale(pi_interval(),Q(1,4)))
    out=((Q(1),Q(1)),(Q(0),Q(0)))
    for _ in range(depth): out=cmul(out,base)
    return (iscale(out[0],Q(1,factorial(depth))),
            iscale(out[1],Q(1,factorial(depth))))
def test_allones_gaussian():
    for depth in range(1,9):
        v,e=enclosure((1,)*depth,QC(Q(0),Q(1)),240)
        ref=gaussian_allones_reference(depth)
        assert v.re-e <= ref[0][0] <= ref[0][1] <= v.re+e
        assert v.im-e <= ref[1][0] <= ref[1][1] <= v.im+e
        tick('independent_exact_gaussian_log_controls')

def gaussian_records():
    import mpmath as mp
    mp.mp.dps=100
    out=[]
    for ind in GAUSS:
        v,e=enclosure(ind,QC(Q(0),Q(1)),240)
        out.append({'index':ind,'terms':240,**as_record(v,e),
                    'real_midpoint_diagnostic':mp.nstr(mp.mpf(v.re.numerator)/v.re.denominator,45),
                    'imag_midpoint_diagnostic':mp.nstr(mp.mpf(v.im.numerator)/v.im.denominator,45)})
    return out

def proposed_brackets(ind):
    """Floating point proposes endpoints; exact arithmetic accepts or rejects."""
    import mpmath as mp
    import numpy as np
    mp.mp.dps=70
    c=coefficients(ind,200)
    fl=np.array([float(v) for v in c])
    ts=np.linspace(0.0001,np.pi-0.0001,1601)
    vals=np.polynomial.polynomial.polyval(.5*np.exp(1j*ts),fl).imag
    intervals=[(float(ts[j]),float(ts[j+1])) for j in range(len(ts)-1)
               if vals[j]*vals[j+1]<0]
    assert len(intervals)==len(ind)-1, (ind,len(intervals))
    mc=[mp.mpf(v.numerator)/v.denominator for v in c]
    def f(theta):
        z=mp.exp(1j*theta)/2
        val=mp.mpc(0)
        for v in reversed(mc): val=val*z+v
        return val.imag
    ans=[]
    for left,right in intervals:
        l,r=mp.mpf(left),mp.mpf(right); fl0=f(l)
        for _ in range(65):
            mid=(l+r)/2
            if f(mid)*fl0>0: l=mid
            else: r=mid
        tt=mp.tan((l+r)/4)
        scale=10**12
        lo=int(mp.floor(tt*scale))
        ans.append((Q(lo,scale),Q(lo+1,scale)))
    return ans

def angular_records():
    out=[]; terms=104
    for ind in ANGULAR:
        moments=centered_moments(ind,terms)
        for k,(l,r) in enumerate(proposed_brackets(ind),1):
            vl,el=enclosure(ind,half_circle(l),terms,moments)
            vr,er=enclosure(ind,half_circle(r),terms,moments)
            sign_left=(-1)**(k-1); sign_right=-sign_left
            assert sign_left*vl.im>el and sign_right*vr.im>er
            out.append({'index':ind,'root_number':k,'radius':'1/2',
                        't_left':str(l),'t_right':str(r),'terms':terms,
                        'left_sign':sign_left,'right_sign':sign_right,
                        'left_imag_lower':str(vl.im-el),'left_imag_upper':str(vl.im+el),
                        'right_imag_lower':str(vr.im-er),'right_imag_upper':str(vr.im+er),
                        'error_bound':str(el)})
    return out

def replay_records():
    gauss=json.loads((DATA/'gaussian_enclosures.json').read_text())
    for row in gauss:
        v,e=enclosure(row['index'],QC(Q(0),Q(1)),row['terms'])
        rec=as_record(v,e)
        assert all(row[k]==v for k,v in rec.items())
        assert e<Q(1,10**81)
        tick('replayed_gaussian_enclosures')
    cache={}
    roots=json.loads((DATA/'angular_brackets.json').read_text())
    for row in roots:
        ind=tuple(row['index']); n=row['terms']; key=(ind,n)
        if key not in cache: cache[key]=centered_moments(ind,n)
        l,r=Q(row['t_left']),Q(row['t_right'])
        assert 0<l<r and r-l<=Q(1,10**12)
        vl,el=enclosure(ind,half_circle(l),n,cache[key])
        vr,er=enclosure(ind,half_circle(r),n,cache[key])
        assert str(el)==row['error_bound']
        for name,v,e in [('left',vl,el),('right',vr,er)]:
            assert str(v.im-e)==row[name+'_imag_lower']
            assert str(v.im+e)==row[name+'_imag_upper']
            assert row[name+'_sign']*v.im>e
            tick('replayed_exact_angular_endpoint_signs')
        tick('replayed_angular_root_brackets')
    for ind in ANGULAR:
        rr=[r for r in roots if tuple(r['index'])==ind]
        assert len(rr)==len(ind)-1
        assert [r['root_number'] for r in rr]==list(range(1,len(ind)))
        assert all(Q(rr[j]['t_right'])<Q(rr[j+1]['t_left']) for j in range(len(rr)-1))
        tick('complete_angular_bracket_families')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--regenerate',action='store_true')
    args=ap.parse_args()
    start=time.perf_counter()
    exact_tests(); test_allones_gaussian()
    if args.regenerate:
        DATA.mkdir(exist_ok=True)
        (DATA/'gaussian_enclosures.json').write_text(json.dumps(gaussian_records(),indent=2)+'\n')
        (DATA/'angular_brackets.json').write_text(json.dumps(angular_records(),indent=2)+'\n')
    replay_records()
    result={'status':'PASS','counts':COUNTS,'total_checked_assertion_groups':sum(COUNTS.values()),
            'scope':'Finite exact checks, not a proof-assistant formalization or a numerical proof of the unbounded theorems.',
            'runtime_seconds_diagnostic':round(time.perf_counter()-start,3),
            'python':sys.version.split()[0]}
    (DATA/'verification_report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__': main()
