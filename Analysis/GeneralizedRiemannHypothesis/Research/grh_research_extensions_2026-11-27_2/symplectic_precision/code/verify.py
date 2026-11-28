#!/usr/bin/env python3
"""Exact finite-ring corroboration for the symplectic precision theorem.

NumPy is used only for enumerating integer arrays. Every probability, sum,
comparison, and reported result is a fractions.Fraction. No floating-point
Fourier transform and no random sampling is used.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import numpy as np


def eta(q, n):
    out = F(1)
    for j in range(1, n + 1):
        out *= 1 - F(1, q ** (2*j))
    return out


def theta(q, n):
    out = F(1)
    for j in range(1, n + 1):
        out *= 1 - F(1, q ** (2*j-1))
    return out


def beta(q, c, r):
    return eta(q, c) / eta(q, c-r)


def qbin(n, k, q):
    if k < 0 or k > n:
        return F(0)
    out = F(1)
    for j in range(k):
        out *= F(q**(n-j)-1, q**(k-j)-1)
    return out


def nonsingular_residual(q, a, r):
    return sum((eta(q,r)/(eta(q,s)*eta(q,r-s)) * theta(q,r-s)
                * F(1,q**((2*a+1)*s)) for s in range(r+1)), F(0))


def partitions_inside(lam, index=0, maximum=None):
    if index == len(lam):
        yield ()
        return
    bound = lam[index] if maximum is None else min(lam[index],maximum)
    for v in range(bound+1):
        for tail in partitions_inside(lam,index+1,v):
            yield (v,)+tail


def subgroup_polynomial(lam, Q, x):
    # Standard finite-module subgroup count by conjugate partitions.
    maxpart = max(lam, default=0)
    lc = [sum(v>=i for v in lam) for i in range(1,maxpart+2)]
    ans = F(0)
    for mu in partitions_inside(lam):
        mc = [sum(v>=i for v in mu) for i in range(1,maxpart+2)]
        count = F(1)
        for i in range(maxpart):
            count *= Q**(mc[i+1]*(lc[i]-mc[i]))
            count *= qbin(lc[i]-mc[i+1],mc[i]-mc[i+1],Q)
        assert count.denominator == 1
        ans += count*x**sum(mu)
    return ans


def val_array(x,p,cap):
    out = np.full(x.shape,cap,dtype=np.int16)
    for j in range(cap-1,-1,-1):
        out[x % (p**(j+1)) != 0] = j
    return out


def alternating_type(coords,p,e):
    aa,bb,cc,dd,ee,ff = coords
    lo = np.minimum.reduce([val_array(x,p,e) for x in coords])
    pf = aa*ff-bb*ee+cc*dd
    hi = np.minimum(e,val_array(pf,p,2*e)-lo)
    assert np.all(hi>=lo)
    return lo,hi


def histogram(coords,p,e):
    lo,hi = alternating_type(coords,p,e)
    keys,counts = np.unique(lo*(e+1)+hi,return_counts=True)
    return {(int(k)//(e+1),int(k)%(e+1)):int(v)
            for k,v in zip(keys,counts)}


def gram_checks(p,e,c):
    n = p**e
    coords = np.indices((n,)*6,dtype=np.int64).reshape(6,-1)
    lo,hi = alternating_type(coords,p,e)
    # Character expectation is p^(-2c(2e-lo-hi)). Integer numerator below.
    exponent = 2*c*(lo+hi)
    weights = np.array([p**int(z) for z in exponent],dtype=np.int64)
    denominator = p**(4*c*e)
    assert denominator < 2**61
    H = {}
    resolved = 0
    for al in range(e+1):
        for be in range(al,e+1):
            pairing = (p**al*coords[0]+p**be*coords[5]) % n
            zero = int(weights[pairing==0].sum())
            near = int(weights[(pairing!=0)&(pairing%(p**(e-1))==0)].sum())
            # Average characters over multiplication by every ring unit:
            # the normalized Ramanujan sum is 1 at 0, -1/(p-1) on
            # the nonzero socle, and 0 elsewhere.
            h = (F(zero)-F(near,p-1))/denominator
            H[(al,be)] = h
            if be < e:
                expected = beta(p,c,2)*subgroup_polynomial((be,al),p*p,F(1,p**(2*c-3)))
                assert h==expected, (p,e,c,al,be,h,expected)
                resolved += 1
            assert (h < 1) if be==0 else (h > 1)
    hist = histogram(coords,p,e)
    mass = sum((count*H[k] for k,count in hist.items()),F(0))/n**6
    distance = sum((count*abs(H[k]-1) for k,count in hist.items()),F(0))/(2*n**6)
    assert mass==1
    assert distance==(1-beta(p,c,2))*theta(p,2)
    return H, {
        'p':p,'precision':e,'complement_pairs':c,
        'enumerated_characters':n**6,'invariant_classes':len(H),
        'resolved_classes_compared_with_density':resolved,
        'mass':str(mass),'gram_total_variation':str(distance),
        'minimum_singular_likelihood':str(min(h for (al,be),h in H.items() if be>0)),
        'nonsingular_likelihood':str(H[(0,0)]),
        'all_signs_passed':True,
    }


def compression_checks(p,e,a,c,H):
    n = p**e
    A = np.indices((n,)*(8*a),dtype=np.int64).reshape(2*a,4,-1)
    pairs = [(i,j) for i in range(4) for j in range(i+1,4)]
    coords=[]
    for i,j in pairs:
        z = np.full(A.shape[-1],int((i,j) in ((0,1),(2,3))),dtype=np.int64)
        for k in range(a):
            z -= A[2*k,i]*A[2*k+1,j]-A[2*k,j]*A[2*k+1,i]
        coords.append(z%n)
    hist=histogram(np.array(coords),p,e)
    den=beta(p,a+c,2)
    mass=sum((count*H[k]/den for k,count in hist.items()),F(0))/A.shape[-1]
    distance=sum((count*abs(H[k]/den-1) for k,count in hist.items()),F(0))/(2*A.shape[-1])
    non=F(hist.get((0,0),0),A.shape[-1])
    expected_non=nonsingular_residual(p,a,2)
    expected_tv=(1-beta(p,c,2)/den)*expected_non
    assert mass==1
    assert non==expected_non
    assert distance==expected_tv
    for k in hist:
        assert (H[k]/den<1) if k==(0,0) else (H[k]/den>1)
    return {'p':p,'precision':e,'target_pairs':a,'source_pairs':2,
            'complement_pairs':c,'enumerated_blocks':int(A.shape[-1]),
            'mass':str(mass),'nonsingular_residual_probability':str(non),
            'total_variation':str(distance),'theorem_formula_passed':True,
            'optimal_event_passed':True}


def main():
    out={'method':'Exact rational Fourier inversion using Ramanujan sums; integer enumeration only.',
         'gram_checks':[],'compression_checks':[]}
    params=[(2,e,c) for e in (1,2,3) for c in (2,3,4)]
    params += [(3,e,c) for e in (1,2) for c in (2,3)]
    for p,e,c in params:
        H,record=gram_checks(p,e,c)
        out['gram_checks'].append(record)
        if (p,e) in ((2,1),(2,2),(3,1)):
            for a in ((1,2) if (p,e)==(2,1) else (1,)):
                out['compression_checks'].append(compression_checks(p,e,a,c,H))
    out['totals']={'gram_parameter_sets':len(out['gram_checks']),
        'compression_parameter_sets':len(out['compression_checks']),
        'fourier_characters_enumerated':sum(x['enumerated_characters'] for x in out['gram_checks']),
        'blocks_enumerated':sum(x['enumerated_blocks'] for x in out['compression_checks'])}
    out['example_q2_a2_r2_c2']={'probability':str(nonsingular_residual(2,2,2)),
        'total_variation':str((1-beta(2,2,2)/beta(2,4,2))*nonsingular_residual(2,2,2)),
        'decimal':float((1-beta(2,2,2)/beta(2,4,2))*nonsingular_residual(2,2,2))}
    path=Path(__file__).resolve().parents[1]/'results'/'verification.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS',**out['totals'],'example':out['example_q2_a2_r2_c2']},indent=2))

if __name__=='__main__':
    main()
