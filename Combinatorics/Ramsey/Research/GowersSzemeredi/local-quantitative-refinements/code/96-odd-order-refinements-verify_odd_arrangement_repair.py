#!/usr/bin/env python3
"""Exact checks for the odd-target arrangement profile and prime construction."""
from fractions import Fraction as F
from itertools import product
from math import comb, isqrt
from pathlib import Path
import json
from verify_arrangement_erasures import counts, best_model_profile


def pointwise_checks():
    total = 0
    for q,s in [(3,4),(3,6),(5,4),(7,4)]:
        signs=[1]*(s//2)+[-1]*(s//2)
        for zs in product(range(q),repeat=s):
            L=sum(z!=0 for z in zs)
            C=sum(zs[i]!=0 and zs[j]!=0 and
                  (signs[i]*zs[i]+signs[j]*zs[j])%q==0
                  for i in range(s) for j in range(i))
            failure=int(sum(a*z for a,z in zip(signs,zs))%q!=0)
            approximation=L-comb(L,2)-C
            assert failure>=approximation
            if L<=2:
                assert failure==approximation
            assert abs(failure-approximation)<=s*s+1
            total+=1
    return total


def exhaustive_full():
    results=[]
    for n,m in [(2,2),(2,3),(3,2)]:
        num=0
        for table in product(range(3),repeat=n*m):
            lam,eps=counts(table,n,m,q=3,s=4)
            d,tau,_,_=best_model_profile(table,n,m,q=3)
            assert lam==1 and tau==0
            assert eps>=4*d-20*d*d
            num+=1
        results.append({"n":n,"m":m,"target_order":3,"maps":num})
    return results


def moment_checks():
    rows=[]
    for p in [3,5,7,11,17,31,101]:
        a=(p-1)//2
        qs=[F(2*min(h,p-h),p) for h in range(p)]
        assert sum(qs,F(0))/p==(1-F(1,p*p))/2
        assert sum((v*v for v in qs),F(0))/p==(1-F(1,p*p))/3
        rows.append({"prime":p,"interval_size":a})
    return rows


def prime_examples():
    rows=[]
    for p in [7,11,17,31,53,101]:
        k=isqrt(p)
        a=(p-1)//2
        table=[int(x<k and y<a) for x in range(p) for y in range(p)]
        lam,eps=counts(table,p,p,q=p,s=4)
        d=F(k*a,p*p)
        assert lam==1
        assert eps>=4*d-20*d*d
        if p<=11:
            dd,_,_,_=best_model_profile(table,p,p,q=p)
            assert dd==d
        center=4*d*(1+F(1,p))-12*d*d*F(p+1,p-1)
        nu=F(k,p)
        bound=(4*4+1)*comb(4,3)*nu**3
        assert abs(eps-center)<=bound
        rows.append({"p":p,"bad_rows":k,"distance":str(d),
            "defect":str(eps),
            "normalized_quadratic_deficit":float((4*d-eps)/(d*d)),
            "limiting_quadratic_deficit":12})
    return rows


def scalar_constants():
    rows=[]
    for s in [4,6,8,16,32]:
        old_lower=F(3*s-2,4*s*s)
        new_lower=F(s-1,s*s)
        old_upper=F(2*(s-1),s*s)
        new_upper=F(3*s-2,2*s*s)
        assert old_lower<new_lower<new_upper<old_upper
        threshold=F(1,240*(s-1))
        assert 2*threshold/s < F(1,3*s-2)
        assert 2*(3*s-2)*threshold/s<1
        rows.append({"s":s,"old_lower":str(old_lower),"new_lower":str(new_lower),
                     "new_upper":str(new_upper),"old_upper":str(old_upper)})
    return rows


def main():
    output={"scope":"Exact finite validation; the theorems rest on the written proofs",
        "pointwise_patterns":pointwise_checks(),
        "exhaustive_full_maps":exhaustive_full(),
        "interval_moment_checks":moment_checks(),
        "prime_examples":prime_examples(),
        "coefficient_comparisons":scalar_constants(),
        "all_checks_passed":True}
    path=Path(__file__).resolve().parent.parent / "data" / "odd_arrangement_validation.json"
    path.write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps(output,indent=2))


if __name__=="__main__":
    main()
