"""Independent exhaustive checks of the finite-ring and field statements.

Run: python3 code/verify_exact.py
No numerical sampling, network access, or third-party dependencies are used.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product, combinations_with_replacement
from pathlib import Path
import json
from symplectic_laws import C, R, u, qpower, orientation_support, full_tv, smith_tv


def rank_binary(rows, width):
    rows = rows[:]
    r = 0
    for j in range(width):
        pivot = next((i for i in range(r,len(rows)) if (rows[i]>>j)&1), None)
        if pivot is None:
            continue
        rows[r],rows[pivot] = rows[pivot],rows[r]
        for i in range(len(rows)):
            if i != r and ((rows[i]>>j)&1):
                rows[i] ^= rows[r]
        r += 1
    return r


def kernel_binary(rows, width):
    rows = rows[:]
    pivots=[]
    r=0
    for j in range(width):
        p=next((i for i in range(r,len(rows)) if (rows[i]>>j)&1),None)
        if p is None:
            continue
        rows[r],rows[p]=rows[p],rows[r]
        for i in range(len(rows)):
            if i != r and ((rows[i]>>j)&1):
                rows[i] ^= rows[r]
        pivots.append(j)
        r+=1
    basis=[]
    for j in range(width):
        if j in pivots:
            continue
        x=1<<j
        for i,p in enumerate(pivots):
            if (rows[i]>>j)&1:
                x |= 1<<p
        basis.append(x)
    return basis


def alternating_pair(x,y,n):
    m=n//2
    mask=(1<<m)-1
    return (((x&mask)&(y>>m)).bit_count()+((x>>m)&(y&mask)).bit_count())%2


def verify_binary_four():
    n=4
    totals=Counter()
    frame_total=0
    support=0
    for packed in range(1<<(n*n)):
        A=[(packed>>(n*i))&((1<<n)-1) for i in range(n)]
        rows=[]
        augmented=[]
        for i in range(n):
            for j in range(i+1,n):
                eq=0
                for z in range(n):
                    if (A[z]>>i)&1:
                        eq ^= 1<<(z*n+j)
                    if (A[z]>>j)&1:
                        eq ^= 1<<(z*n+i)
                rhs=int(j==i+n//2)
                rows.append(eq)
                augmented.append(eq|(rhs<<(n*n)))
        rank=rank_binary(rows,n*n)
        consistent=rank_binary(augmented,n*n+1)==rank
        K=kernel_binary(A,n)
        k=len(K)
        isotropic=all(alternating_pair(x,y,n)==0 for x in K for y in K)
        assert consistent==isotropic
        assert rank==n*(n-1)//2-k*(k-1)//2
        fibre=(1<<(n*n-rank)) if consistent else 0
        expected=(1<<(n*(n+1)//2+k*(k-1)//2)) if isotropic else 0
        assert fibre==expected
        totals[k]+=fibre
        frame_total+=fibre
        support+=int(consistent)
    expected_total=qpower(2,n*(3*n+1)//2)*C(2,n)
    assert frame_total==expected_total
    for k in range(n+1):
        assert F(totals[k],frame_total)==u(2,n,k)*R(2,n,k)/C(2,n)
    assert 1-F(support,2**(n*n))==full_tv(2,n,1)
    return {'matrices_checked':2**16,'frame_count':frame_total,
            'supported_matrices':support,'nullity_frame_counts':dict(totals)}


def vp(x,p,cap):
    if x==0:
        return cap
    v=0
    while x%p==0 and v<cap:
        v+=1
        x//=p
    return v


def smith_two(A,p,h):
    a=min(vp(x,p,h) for x in A)
    if a==h:
        return (h,h)
    det=A[0]*A[3]-A[1]*A[2]
    return (a,min(h,vp(det,p,2*h)-a))


def verify_two_ring(p,h):
    modulus=p**h
    arrays=list(product(range(modulus),repeat=4))
    iid=Counter()
    frames=Counter()
    total=0
    for A in arrays:
        typ=smith_two(A,p,h)
        iid[typ]+=1
        fibre=0
        for B in arrays:
            value=A[0]*B[1]+A[2]*B[3]-B[0]*A[1]-B[2]*A[3]
            if value%modulus==1:
                fibre+=1
        expected=modulus**3 if any(x%p for x in A) else 0
        assert fibre==expected
        frames[typ]+=fibre
        total+=fibre
    assert total==qpower(p,7*h)*C(p,2)
    tv=F(0)
    for typ,count in iid.items():
        probability=F(count,len(arrays))
        k=sum(x>=1 for x in typ)
        assert F(frames[typ],total)==probability*R(p,2,k)/C(p,2)
        tv+=abs(F(frames[typ],total)-probability)/2
    assert tv==smith_tv(p,2)
    return {'residue_q':p,'precision':h,'pairs_checked':len(arrays)**2,
            'frame_count':total,'smith_tv':str(tv),'smith_types':len(iid)}


def verify_orientations_mod_four():
    pairs=[(i,j) for i in range(4) for j in range(i+1,4)]
    # Every invertible alternating form is T^t H T.  Counting the forms
    # independently of the fibre formula tests the cancellation of deep digits.
    forms=[]
    for values in product(range(4),repeat=6):
        b01,b02,b03,b12,b13,b23=values
        pfaffian=b01*b23-b02*b13+b03*b12
        if pfaffian%2:
            forms.append(values)
    types=list(combinations_with_replacement(range(3),4))
    checked=[]
    for typ in types:
        allowed=sum(all(value%(2**min(typ[i],typ[j]))==0
                        for (i,j),value in zip(pairs,values)) for values in forms)
        expected=orientation_support(2,4,typ)
        assert F(allowed,len(forms))==expected
        checked.append({'exponents':list(typ),'supported_forms':allowed,
                        'probability':str(expected)})
    return {'forms_enumerated':4**6,'invertible_forms':len(forms),
            'smith_types_checked':len(types),'details':checked}


def verify_probability_formulas():
    comparisons=0
    for q in (2,3,4,5,7,8,9):
        for n in range(2,22,2):
            assert sum(u(q,n,k) for k in range(n+1))==1
            law=[u(q,n,k)*R(q,n,k)/C(q,n) for k in range(n+1)]
            assert sum(law)==1
            tv=sum(abs(law[k]-u(q,n,k))/2 for k in range(n+1))
            assert tv==smith_tv(q,n)
            vals=[full_tv(q,n,h) for h in (1,2,3,None)]
            assert vals==sorted(vals)
            assert vals[0]>=tv
            comparisons+=1
    return {'parameter_pairs_checked':comparisons}


def main():
    result={
        'binary_four_fibre_enumeration':verify_binary_four(),
        'small_ring_pair_enumerations':[verify_two_ring(2,2),verify_two_ring(3,1)],
        'alternating_orientations_mod_four':verify_orientations_mod_four(),
        'normalizations_and_total_variation':verify_probability_formulas(),
        'status':'ALL EXACT CHECKS PASSED'}
    out=Path(__file__).resolve().parents[1]/'results'/'exact_verification.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='alternating_orientations_mod_four'},indent=2))
    print('All 15 Smith-type orientation probabilities over Z/4Z matched exactly.')


if __name__=='__main__':
    main()
