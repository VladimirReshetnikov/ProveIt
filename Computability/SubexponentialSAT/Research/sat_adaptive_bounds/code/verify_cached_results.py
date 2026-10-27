#!/usr/bin/env python3
"""Exact finite certificates for cached_results.tex (standard library only).

All correctness gates use explicit exceptions and remain active under python -O.
These checks certify finite arithmetic, profiles, schedules and averaging; they
are not an independent proof of the imported ETH/contraction interfaces.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb, log, log2, pi, sqrt
from pathlib import Path
import argparse
import json
import random


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sqrt_sum_less_one(a2, b2):
    # For nonnegative a,b: sqrt(a)+sqrt(b)<1 iff the following positive
    # rational difference and its square satisfy these strict inequalities.
    d = 1-a2-b2
    return a2 >= 0 and b2 >= 0 and d > 0 and d*d > 4*a2*b2


def balanced_partitions(r):
    require(r % 3 == 0, "three equal blocks required")
    k = r//3
    vertices = tuple(range(r))
    for rest_a in combinations(vertices[1:], k-1):
        a = (0,)+rest_a
        rem = tuple(x for x in vertices if x not in a)
        for rest_b in combinations(rem[1:], k-1):
            b = (rem[0],)+rest_b
            c = tuple(x for x in rem if x not in b)
            yield (a,b,c)


def partition_classes(partition):
    a,b,c = partition
    return (tuple((min(x,y),max(x,y)) for x in a for y in b),
            tuple((min(x,y),max(x,y)) for x in a for y in c),
            tuple((min(x,y),max(x,y)) for x in b for y in c))


def profile(r):
    k=r//3
    require(r == 3*k, "equal blocks required")
    merges=[]; boundaries=[]
    def build(size):
        boundaries.append(2*size*(r-size))
        if size == 1:
            return
        a=size//2;b=size-a
        axes=(2*a*(r-size),2*a*b,2*b*(r-size))
        score=sum(axes)-F(21,25)*min(axes)
        merges.append({'size':size,'split':[a,b],'axes':axes,'score':str(score)})
        build(a);build(b)
    build(k)
    triangle_axes=(2*k*k,)*3
    E=r*(r-1);C=sum(triangle_axes);m=min(triangle_axes);v=max(triangle_axes)
    centered=F((C-F(3,5)*m)**2,E)+F(9,25)*v
    largest_merge=max(F(x['score']) for x in merges)
    require(centered < largest_merge, "triangle must not dominate")
    return dict(r=r,blocks=[k,k,k],merges=merges,
                cache=2*(r-1),largest_merge=str(largest_merge),
                centered_triangle=str(centered),largest_boundary=max(boundaries),
                alpha2=str(F(2*(r-1),r*r)),beta2=str(largest_merge/(r*r)),
                storage2=str(F(max(boundaries),r*r)))


def verify_averaging(r):
    edges=tuple(combinations(range(r),2));counts={e:0 for e in edges}
    number=0
    for p in balanced_partitions(r):
        number+=1
        classes=partition_classes(p)
        flat=[e for c in classes for e in c]
        require(len(flat)==r*r//3,"wrong crossing count")
        require(len(set(flat))==len(flat),"repeated edge")
        for e in flat:counts[e]+=1
    k=r//3
    expected_number=comb(r-1,k-1)*comb(2*k-1,k-1)
    expected_cross=F(2*r,3*(r-1))
    require(number==expected_number,"wrong partition count")
    require(set(counts.values())=={number*expected_cross},"nonuniform edge averaging")
    return dict(r=r,partitions=number,undirected_edges=len(edges),
                crossing_fraction=str(expected_cross),
                each_edge_crossings=min(counts.values()))


def check_centered_instances():
    # This is an independent finite consistency check on the lemma's selection
    # rule. Both directed weights of an undirected pair enter its class sum.
    r=9;E=r*(r-1)
    directed=tuple((i,j) for i in range(r) for j in range(r) if i != j)
    parts=[partition_classes(p) for p in balanced_partitions(r)]
    instances=[[0]*E,[1]*E,[1000]+[0]*(E-1)]
    rng=random.Random(20261026)
    for _ in range(61):
        instances.append([rng.randrange(100) for _ in directed])
    bound=F(162,5)
    for values in instances:
        h=dict(zip(directed,values))
        weights={(i,j):h[i,j]+h[j,i] for i,j in combinations(range(r),2)}
        sums=[tuple(sum(weights[e] for e in cls) for cls in p) for p in parts]
        chosen=min(sums,key=lambda x:(sum(x),x))
        require(sum(chosen) <= F(3,4)*sum(values),"averaging selection failed")
        cost=sum(chosen)-F(3,5)*min(chosen)
        require(cost*cost <= bound*sum(x*x for x in values),"centered bound failed")
    return dict(r=r,instances=len(instances),partitions_per_instance=len(parts),
                exact_arithmetic=True)


def log_interval(x, n=64):
    # log(x)=2 atanh((x-1)/(x+1)); all x here are positive rationals >1.
    t=(x-1)/(x+1)
    value=sum((2*t**(2*k+1)/F(2*k+1) for k in range(n)), F(0))
    tail=2*t**(2*n+1)/(F(2*n+1)*(1-t*t))
    return value,value+tail


def atan_interval(x, n=40):
    partial=sum(((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
    next_term=(-1)**n*x**(2*n+1)/F(2*n+1)
    return min(partial,partial+next_term),max(partial,partial+next_term)


def coefficient_intervals():
    a,b=atan_interval(F(1,5));c,d=atan_interval(F(1,239))
    plo,phi=16*a-4*d,16*b-4*c
    l2lo,l2hi=log_interval(F(2));l3lo,l3hi=log_interval(F(3))
    l9lo,l9hi=2*l3lo,2*l3hi
    lg9lo,lg9hi=l9lo/l2hi,l9hi/l2lo
    def interval(c_lo,c_hi):
        return plo*plo*c_lo/(l2hi*l2hi),phi*phi*c_hi/(l2lo*l2lo)
    vals={
        'generic_time':interval(F(7328,405)*lg9lo,F(7328,405)*lg9hi),
        'generic_space':interval(F(160,9)*lg9lo,F(160,9)*lg9hi),
        'low_time':interval(F(203840,23391),F(203840,23391)),
        'low_space':interval(F(200000,23391),F(200000,23391)),
    }
    safe={'generic_time':F(3433,100),'generic_space':F(3403,100),
          'low_time':F(1338,100),'low_space':F(1326,100)}
    for key,(_,hi) in vals.items():
        require(hi<safe[key]**2,f"safe rounded coefficient failed: {key}")
    # Strongest displayed source certificates, with their separate premises.
    require(F(7328,405)*lg9hi < F(24339,400),"generic time did not improve")
    require(F(160,9)*lg9hi < F(915,16),"generic memory did not improve")
    lg162lo=1+2*lg9lo
    require(F(203840,23391)<F(1400,891)*lg162lo,"low time did not improve")
    require(F(200000,23391)<F(400,297)*lg162lo,"low memory did not improve")
    return {key:{'approximate':sqrt(float((lo+hi)/2)),
                 'safe_eventual':str(safe[key]),
                 'squared_interval_width_upper':float(hi-lo)}
            for key,(lo,hi) in vals.items()}


def schedule_checks():
    # Generic r=9: tail geometric ratio=4/9. The total taper budget is 2u0.
    a2=F(16,81);b2=F(916,2025);j2=F(4,9);gamma=F(4,9)
    require(a2/(1-gamma)**2 == F(16,25),"generic tail formula")
    require(b2 < F(16,25),"generic tail maximum")
    require(F(17,10)**2 < 3,"sqrt3 lower bound")
    require(F(4,9)+F(160,765)==F(100,153),"generic tail rational envelope")
    require(F(100,153)**2 < b2,"generic root dominance")
    require(F(1,5)+F(1,30)<F(1,4),"generic fresh-side packing bound")
    require(F(2,9)<F(1,4),"generic child shrink")
    require(F(3,4)>F(1,2),"generic leaf exponent")
    # Low degree r=15: rational budgets, actual cache ratio and child shrink.
    A=F(113,1000);q=F(2,25);root=A*(1-q)
    require(root==F(2599,25000),"low root fraction")
    require(root/(1-q)==A,"low total budget")
    require(450**113 < 2**1000,"low packing gap")
    require(F(1,12)<A,"low inherited degree gap")
    require(F(2,15)<F(1,7),"low coarse child shrink")
    require(F(25,2)**2 < 7**3,"low taper grows at stopping depth")
    gamma2=F(2,9);ratio2=F(25,91)
    require(sqrt_sum_less_one(gamma2,ratio2),"low recursive dominance")
    require(gamma2<F(472,1000)**2,"low gamma rational upper")
    require(ratio2<F(525,1000)**2,"low cache ratio rational upper")
    require(F(472+525,1000)<1,"low dominance via rational upper bounds")
    require(F(28,225)/F(2548,5625)==ratio2,"low cache coefficient ratio")
    require(2*F(2548,5625)/root==F(203840,23391),"low time constant")
    require(2*j2/root==F(200000,23391),"low memory constant")
    return dict(generic=dict(groups=9,root_taper='floor((J_lambda-ceil(sqrt(lambda)))/20)',
                             tail_taper='floor(3*u0/4^d)',leaf_power='3/4',
                             child_ratio='2/9',tail_K_ratio='4/9'),
                low=dict(groups=15,total_budget=str(A),taper_ratio=str(q),
                         root_budget=str(root),leaf_power='2/3',child_ratio='2/15',
                         squared_K_ratio=str(gamma2)))


def run():
    p9,p15=profile(9),profile(15)
    require(p9['largest_merge']=='916/25' and p15['largest_merge']=='2548/25',
            "profile maxima")
    require(p9['centered_triangle']=='162/5' and p15['centered_triangle']=='606/7',
            "centered triangle scores")
    return dict(status='passed',profiles=[p9,p15],
                averaging=[verify_averaging(9),verify_averaging(15)],
                centered_finite_checks=check_centered_instances(),
                schedules=schedule_checks(),coefficients=coefficient_intervals(),
                scope='Finite exact certificates; imported contraction identities and the asymptotic proof are separate.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=run();encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(encoded)
    print(encoded,end='')
