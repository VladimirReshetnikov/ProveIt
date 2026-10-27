#!/usr/bin/env python3
"""New strict 9 -> 13 -> 9 -> 6 schedule for the certified affine/cyclic menus.
Run alongside certify_affine_cyclic.py. Standard library only; rational checks.
"""
from fractions import Fraction as F
from certify_affine_cyclic import (require,plans9,plans13,supports,certify,add,mul,div,
                                  exact,root,pi_bounds,ln2_bounds,interval_decimal)
import json


def sub_positive(a,b):
    require(a[0]>b[1],"Nonpositive interval subtraction")
    return a[0]-b[1],a[1]-b[0]


def schedule():
    eta0=F(15773,10**6);eta1=F(9,800);eta2=F(4477,10**6)
    tail_total=F(71,10000);q=F(12,25);eta3=tail_total*(1-q)
    require(eta0+eta1==F(27023,10**6),"Prefix sum")
    require(eta0+eta1+eta2==F(63,2000),"Depth-two sum")
    require(eta0+eta1+eta2+tail_total==F(193,5000),"Final cumulative capacity")
    require(eta3==F(923,250000),"First geometric taper")
    require(9**20000<2**63399,"Root log9 upper bound")
    require(13**2000<2**7401,"Log13 upper bound")
    require(9**100<2**317,"Depth-two log9 upper bound")
    require(6**200<2**517,"Tail log6 upper bound")
    gaps=[F(1,10)-2*eta0*F(63399,20000),
          F(1,10)-(eta0+eta1)*F(7401,2000),
          F(1,10)-(eta0+eta1+eta2)*F(317,100),
          F(1,10)-(eta0+eta1+eta2+tail_total)*F(517,200)]
    require(all(g>0 for g in gaps),"Strict padding gates")
    fresh_bound=F(193,5000)*(2*F(7401,2000)+1)
    require(fresh_bound<1,"Fresh-side and rounding exponent")
    require(F(25,12)**3<16,"Taper divergence at hypothetical active depth")
    return {"group_counts":[9,13,9,6],"prefix_tapers":[str(eta0),str(eta1),str(eta2)],
            "first_tail_taper":str(eta3),"tail_ratio":str(q),"tail_total_taper":str(tail_total),
            "total_taper":str(F(193,5000)),"strict_packing_gaps":[str(g) for g in gaps],
            "fresh_side_exponent_upper":str(fresh_bound)}


def constants():
    kap=mul(div(pi_bounds(),ln2_bounds()),root(2))
    K0=mul(kap,root(F(10**6,15773)))
    K1=mul(mul(kap,exact(F(2,9))),root(F(800,9)))
    K2=mul(mul(kap,exact(F(4,117))),root(F(10**6,4477)))
    K3=mul(mul(kap,exact(F(8,1053))),root(F(250000,923)))
    aa=[exact(F(4,9)),root(F(24,169)),exact(F(4,9)),root(F(5,18))]
    bb=[root(F(1,3)),root(F(56,169)),root(F(1,3)),root(F(12,25))]
    KK=[K0,K1,K2,K3]
    gamma=div(exact(F(1,3)),root(F(12,25)))
    tailratio=div(aa[3],sub_positive(exact(1),gamma))
    require(tailratio[0]>bb[3][1],"Tail matrix branch exceeds full paid child path")
    Cs=[];prefix=exact(0)
    for d in range(3):
        Cs.append(add(prefix,mul(bb[d],KK[d])))
        prefix=add(prefix,mul(aa[d],KK[d]))
    Cs.append(add(prefix,mul(tailratio,K3)))
    CT=Cs[1];CS=Cs[0]
    for d in (0,2,3):require(Cs[d][1]<CT[0],"Depth-one time branch does not dominate")
    for d in (1,2,3):require(mul(bb[d],KK[d])[1]<CS[0],"Root storage does not dominate")
    require(CT[1]<F(30414,1000),"Time threshold")
    require(CS[1]<F(29467,1000),"Space threshold")
    return {"root_C0":interval_decimal(Cs[0]),"depth_one_CT":interval_decimal(Cs[1]),
            "depth_two_C2":interval_decimal(Cs[2]),"full_child_path_Cinf":interval_decimal(Cs[3]),
            "gamma":interval_decimal(gamma),"eventual_time":30.414,"eventual_space":29.467,
            "local_storage":[interval_decimal(mul(bb[d],KK[d])) for d in range(4)]}


def main():
    c9=certify(9,plans9());c13=certify(13,plans13())
    c6=certify(6,[[[0,1],[2,3],[4,5]]])
    require(c9['total']==5400 and c9['b_squared']=='1/3',"Affine certificate")
    require(c13['total']==118300 and c13['b_squared']=='56/169',"Cyclic certificate")
    require(c6['total']==216 and c6['b_squared']=='12/25',"Six-group tail certificate")
    result={"status":"PASS","scope":"Finite menu and strict schedule certificates; imported contraction interfaces remain assumptions", 
            "certificates":[c9,c13,c6],"schedule":schedule(),"constants":constants()}
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__=='__main__':main()
