#!/usr/bin/env python3
"""Independent exact audit of partial affine doubling, r=15 -> 10 -> 7 -> 4.

Standard library only. It reconstructs the new finite certificate without
importing the search code, then checks all schedule and coefficient inequalities.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import isqrt
from pathlib import Path
import json

DEN=1_400_000
TRIPLES=sorted(set(permutations((1_400_007,1_400_007,0))) |
               set(permutations((1_400_000,1_175_014,750_000))))

def require(condition,message):
    if not condition:raise RuntimeError(message)

def plans15():
    plans=[[[3*x+y for y in range(3)] for x in range(3)]]
    plans += [[[3*x+(slope*x+c)%3 for x in range(3)] for c in range(3)]
              for slope in range(3)]
    for plan in plans:
        for point in range(6):
            next(block for block in plan if point in block).append(point+9)
    return plans

def supports(plan):
    r=15;edges=list(combinations(range(r),2));universe=set(range(r));out=[]
    def operation(parts):
        labels={v:j for j,part in enumerate(parts) for v in part}
        require(len(labels)==r,"operation does not cover all vertices")
        require(sum(map(len,parts))==r,"operation parts overlap")
        classes={(0,1):0,(0,2):1,(1,2):2}
        kinds=[None if labels[a]==labels[b] else
               classes[tuple(sorted((labels[a],labels[b])))] for a,b in edges]
        for weights in TRIPLES:
            out.append(tuple(0 if kind is None else weights[kind] for kind in kinds))
    def visit(block):
        if len(block)<2:return
        cut=len(block)//2;a,b=block[:cut],block[cut:]
        visit(a);visit(b);operation((a,b,universe-set(block)))
    for block in plan:visit(block)
    operation(plan)
    require(len(out)==117,"wrong support count")
    return out

def dot(a,b):return sum(x*y for x,y in zip(a,b))

def certificate():
    arrays=[supports(plan) for plan in plans15()]
    norms=[[dot(v,v) for v in family] for family in arrays]
    maxima=[]
    for i,j in combinations(range(4),2):
        maxima.append(max(norms[i][a]+norms[j][b]+6*dot(v,w)
                          for a,v in enumerate(arrays[i])
                          for b,w in enumerate(arrays[j])))
    expected=[580173494513132]*3+[572279799215680]*3
    require(maxima==expected,"coupled pair maxima differ")
    b2=F(2*sum(maxima),3*16*DEN**2*15**2)
    require(b2==F(32012591492467,98000000000000),"wrong local coefficient")
    return b2,maxima

def rt(x):
    x=F(x);scale=10**50;j=isqrt(x.numerator*scale**2//x.denominator)
    return F(j,scale),F(j+1,scale)
def plus(a,b):return a[0]+b[0],a[1]+b[1]
def times(a,b):return a[0]*b[0],a[1]*b[1]
def div(a,b):
    require(b[0]>0,"nonpositive divisor interval")
    return a[0]/b[1],a[1]/b[0]
def constant(x):return F(x),F(x)

def pi_ln2():
    def atan(q):
        N=80
        x=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(N)),F(0))
        y=x+F((-1)**N,(2*N+1)*q**(2*N+1))
        return min(x,y),max(x,y)
    a,b=atan(5),atan(239)
    piv=(16*a[0]-4*b[1],16*a[1]-4*b[0])
    N=100
    lo=sum((F(2,(2*j+1)*3**(2*j+1)) for j in range(N)),F(0))
    tail=F(2,(2*N+1)*3**(2*N+1))*F(9,8)
    return piv,(lo,lo+tail)

def decimals(interval,digits=14):
    scale=10**digits
    lo=interval[0].numerator*scale//interval[0].denominator
    hi=(interval[1].numerator*scale+interval[1].denominator-1)//interval[1].denominator
    def fmt(v):return str(v//scale)+'.'+str(v%scale).zfill(digits)
    return [fmt(lo),fmt(hi)]

def main():
    b15,maxima=certificate()
    rs=[15,10,7,4]
    etas=[F(567,5000),F(87,5000),F(407,20000),F(1443,80000)]
    q=F(63,100)
    beta2=[b15,F(15952347164548384057,49000000000000000000),F(891,2450),F(13,25)]
    require(sum(etas[:2])==F(327,2500),"stage1 capacity")
    require(sum(etas[:3])==F(3023,20000),"stage2 capacity")
    require(sum(etas[:3])+etas[3]/(1-q)==F(1999,10000),"total capacity")
    require(450**567<2**5000,"root packing")
    require(200**327<2**2500,"stage1 packing")
    require(98**3023<2**20000,"stage2 packing")
    require(5*F(1999,10000)<1,"tail packing")
    require(F(1,12)<etas[0],"root degree is below initial packet exponent")
    require(F(1,2)<F(11,20),"coarse child ratio")
    require(F(100,63)<F(20,11),"positive taper power for leaf threshold s/log2(s)")
    prefix=constant(0);mass=F(1);costs=[];local=[];scales=[]
    for d,(r,e,b2) in enumerate(zip(rs,etas,beta2)):
        kd=rt(mass*mass/e);alpha=rt(F(2*(r-1),r*r))
        scales.append(kd);local.append(times(rt(b2),kd))
        if d<3:costs.append(plus(prefix,local[-1]))
        else:
            gamma=div(constant(F(1,2)),rt(q))
            tail=div(alpha,(1-gamma[1],1-gamma[0]))
            require(tail[0]>rt(b2)[1],"tail local work dominates path unexpectedly")
            costs.append(plus(prefix,times(tail,kd)))
        prefix=plus(prefix,times(alpha,kd));mass*=F(2,r)
    require(all(costs[0][0]>x[1] for x in costs[1:]),"root does not dominate paid recurrence")
    # The separate independent mixed-support checker proves joint selection
    # with rho^2=231/200 at the root. Tail storage can use its full local
    # time coefficient: the array-size branch covers every cached table.
    sigma2=b15/F(231,200)
    require(sigma2==F(32012591492467,113190000000000),"wrong joint space coefficient")
    root_space=times(rt(sigma2),scales[0])
    require(all(root_space[0]>x[1] for x in local[1:]),"joint root does not dominate tail storage")
    piv,ln2=pi_ln2();kappa=times(div(piv,ln2),rt(2))
    actual=[times(kappa,x) for x in costs]
    actual_space=times(kappa,root_space)
    actual_local=[times(kappa,x) for x in local]
    require(actual[0][1]<F(10879,1000),"safe time coefficient 10.879 failed")
    require(actual_space[1]<F(10123,1000),"safe space coefficient 10.123 failed")
    factor=2*b15/etas[0]
    require(factor==F(32012591492467,5556600000000),"root radical identity")
    result={
      "status":"passed","plans":plans15(),"supports_per_plan":117,
      "pairwise_support_comparisons":6*117**2,
      "coupled_pair_maxima":maxima,"beta15_squared":str(b15),
      "groups":rs,"etas":list(map(str,etas)),"tail_ratio":str(q),
      "total_capacity":"1999/10000","root_radical_factor":str(factor),
      "leaf_threshold":"ceil(s/ceil(log2(s)))",
      "precision_ratio_bound":"O(lambda^4 * 2^(-ceil(6*log2(lambda)))) = o(1)",
      "paid_branch_enclosures":[decimals(x) for x in actual],
      "time_enclosure":decimals(actual[0]),
      "space_enclosure":decimals(actual_space),
      "joint_root_sigma_squared":str(sigma2),
      "local_time_enclosures":[decimals(x) for x in actual_local],
      "safe_eventual_time_coefficient":"10.879",
      "safe_eventual_space_coefficient":"10.123",
      "joint_space_dependency":"code/check_partial_affine_joint.py",
      "scope":"Exact local and schedule certificate relative to imported contraction and matrix interfaces; no full SAT solver."
    }
    (Path(__file__).resolve().parents[1] / "results" / "round5_new15_audit.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
