#!/usr/bin/env python3
"""Exact rational validation for the 9 -> 13 -> 7 adaptive contraction schedule.

The adaptive local coefficients b_9^2 and b_13^2 are inputs to this
schedule certificate; they must separately be certified by enumerating the
three supplied contraction-tree portfolios. No floating point is used in
any assertion. Decimal rendering is only for human inspection.
"""
from fractions import Fraction as F
from math import isqrt
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
import json

V0=F(63,4000)
V1=F(9,800)
V2=F(77,16200)
RHO=F(4,9)
A9SQ=F(16,81)
A13SQ=F(24,169)
A7SQ=F(12,49)
B9SQ=F(6608,18225)
B13SQ=F(1572,4225)
# Safe fixed tree at r=7: blocks (3,2,2); its triangle dominates.
B7SQ=F(632,1225)


CHECKS=[]

def require(condition,message):
    if not condition:
        raise ValueError(message)
    CHECKS.append(message)


def atan_interval(x,n):
    """Alternating series enclosure for arctan(x), 0<x<1."""
    s=sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
    t=(-1)**n*x**(2*n+1)/F(2*n+1)
    return min(s,s+t),max(s,s+t)


def pi_interval():
    a,b=atan_interval(F(1,5),50)
    c,d=atan_interval(F(1,239),15)
    # Machin's exact identity: pi=16 arctan(1/5)-4 arctan(1/239).
    return 16*a-4*d,16*b-4*c


def ln2_interval():
    # ln 2=2 atanh(1/3). Tail bounded by dropping its increasing denominator.
    n=50;x=F(1,3)
    lo=2*sum((x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
    tail=2*x**(2*n+1)/(F(2*n+1)*(1-x*x))
    return lo,lo+tail


def sqrt_interval(q,digits=50):
    scale=10**digits
    v=isqrt(q.numerator*scale*scale//q.denominator)
    lo,hi=F(v,scale),F(v+1,scale)
    require(lo*lo<=q<=hi*hi,'lo*lo<=q<=hi*hi')
    return lo,hi


def render(q,rounding):
    with localcontext() as ctx:
        ctx.prec=60
        ctx.rounding=rounding
        return str(Decimal(q.numerator)/Decimal(q.denominator))


def render_interval(interval):
    lo,hi=interval
    return [render(lo,ROUND_FLOOR),render(hi,ROUND_CEILING)]


def coefficient_interval(radicals):
    p0,p1=pi_interval();l0,l1=ln2_interval()
    lows,highs=zip(*(sqrt_interval(q) for q in radicals))
    return p0*sum(lows)/l1,p1*sum(highs)/l0


def main():
    require(B9SQ==F(2*3304,25*9*9**2),"r=9 squared norm input")
    require(B13SQ==F(2*7074,25*9*13**2),"r=13 squared norm input")
    require(B7SQ==(F(32)-(F(21,25)*8))/49,"r=7 fixed-tree triangle cost")
    require(A9SQ<B9SQ and A13SQ<B13SQ and A7SQ<B7SQ,"singleton caches fit local operation bounds")
    require(V0+V1==F(27,1000),'V0+V1==F(27,1000)')
    require(V0+V1+V2/(1-RHO)==F(8,225),'V0+V1+V2/(1-RHO)==F(8,225)')
    # Exact integer certificates for the logarithm upper bounds.
    require(9**100<2**317,'9**100<2**317')
    require(13**1000<2**3701,'13**1000<2**3701')
    require(7**100<2**281,'7**100<2**281')
    root_gap=1-(F(9,10)+2*V0*F(317,100))
    first_gap=1-(F(9,10)+(V0+V1)*F(3701,1000))
    tail_gap=1-(F(9,10)+F(8,225)*F(281,100))
    require(min(root_gap,first_gap,tail_gap)>0,'min(root_gap,first_gap,tail_gap)>0')
    # All secondary asymmetric/packet capacity terms have exponent below 1.
    require(F(8,225)*(2*F(3701,1000)+1)<1,'F(8,225)*(2*F(3701,1000)+1)<1')
    # At r=7, m decays by 2/7 and u by 4/9, so K decays by 3/7.
    gamma=F(3,7)
    tail_eff_sq=A7SQ/(1-gamma)**2
    require(tail_eff_sq==F(3,4)>B7SQ,'tail_eff_sq==F(3,4)>B7SQ')
    root=[2*B9SQ/V0]
    first=[2*A9SQ/V0,2*F(2,9)**2*B13SQ/V1]
    tail=[2*A9SQ/V0,2*F(2,9)**2*A13SQ/V1,
          2*F(4,117)**2*tail_eff_sq/V2]
    intervals={k:coefficient_interval(v) for k,v in
               [('root',root),('first_tail_stage',first),('infinite_tail',tail)]}
    c0,c1,ct=intervals.values()
    require(c1[0]>max(c0[1],ct[1]),'c1[0]>max(c0[1],ct[1])')
    require(c1[1]<F(30892,1000),'c1[1]<F(30892,1000)')
    require(c0[1]<F(30754,1000),'c0[1]<F(30754,1000)')
    first_space=coefficient_interval([2*F(2,9)**2*B13SQ/V1])
    tail_space=coefficient_interval([2*F(4,117)**2*B7SQ/V2])
    require(c0[0]>max(first_space[1],tail_space[1]),'c0[0]>max(first_space[1],tail_space[1])')
    result={
      'description':'Exact rational schedule certificate; local adaptive norms supplied separately',
      'radii':[9,13,7], 'v':[str(V0),str(V1),str(V2)], 'tail_decay':str(RHO),
      'capacity_gaps':[str(root_gap),str(first_gap),str(tail_gap)],
      'coefficient_intervals':{k:render_interval(v) for k,v in intervals.items()},
      'radical_arguments':{'root':list(map(str,root)),'first_tail_stage':list(map(str,first)),
                          'infinite_tail':list(map(str,tail))},
      'space_by_depth':{'root':render_interval(c0),
                        'depth_1':render_interval(first_space),
                        'depth_2_and_beyond':render_interval(tail_space)},
      'certified_time_upper':'30.892', 'certified_space_upper':'30.754',
      'all_checks_passed':True,
      'arithmetic':'Exact Fraction checks; outward-rounded 60-significant-digit decimals',
      'checks':CHECKS,
    }
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
