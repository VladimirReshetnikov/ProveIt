#!/usr/bin/env python3
"""Exact rational certificate for the 9,12,8,7,4 contraction schedule.

Every inequality below is checked with integers or outward rational intervals.
No external packages or floating-point arithmetic enter the certificate.
This does not verify the imported tensor deformation/recovery interfaces.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
import argparse
import json
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


@dataclass(frozen=True)
class I:
    lo: F
    hi: F
    def __post_init__(self):
        require(self.lo <= self.hi, 'Reversed interval')
    @staticmethod
    def exact(x):
        return x if isinstance(x,I) else I(F(x),F(x))
    def __add__(self,other):
        b=I.exact(other);return I(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self):
        return I(-self.hi,-self.lo)
    def __sub__(self,other):return self+-I.exact(other)
    def __rsub__(self,other):return I.exact(other)+-self
    def __mul__(self,other):
        b=I.exact(other)
        xs=[a*c for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        return I(min(xs),max(xs))
    __rmul__=__mul__
    def reciprocal(self):
        require(self.lo>0 or self.hi<0,'Interval contains zero')
        return I(1/self.hi,1/self.lo)
    def __truediv__(self,other):return self*I.exact(other).reciprocal()
    def __rtruediv__(self,other):return I.exact(other)*self.reciprocal()
    def sqrt(self):
        require(self.lo>=0,'Negative square root')
        scale=10**45
        a=isqrt(self.lo.numerator*scale*scale//self.lo.denominator)
        b=isqrt(self.hi.numerator*scale*scale//self.hi.denominator)
        return I(F(a,scale),F(b+1,scale))
    def decimals(self,digits=15):
        scale=10**digits
        low=self.lo.numerator*scale//self.lo.denominator
        high=-((-self.hi.numerator*scale)//self.hi.denominator)
        def render(x):
            sign='-' if x<0 else '';x=abs(x)
            return f'{sign}{x//scale}.{x%scale:0{digits}d}'
        return [render(low),render(high)]


def sqrt(x):return I.exact(x).sqrt()


def atan_reciprocal(q,terms):
    """Alternating-series enclosure for atan(1/q)."""
    total=sum((F(1,(2*k+1)*q**(2*k+1)) if k%2==0 else
               -F(1,(2*k+1)*q**(2*k+1))) for k in range(terms))
    next_term=F((-1)**terms,(2*terms+1)*q**(2*terms+1))
    return I(min(total,total+next_term),max(total,total+next_term))


def constants():
    # Machin identity pi = 16 atan(1/5) - 4 atan(1/239).
    pi=16*atan_reciprocal(5,40)-4*atan_reciprocal(239,12)
    # ln2 = 2 atanh(1/3), positive series and a geometric tail bound.
    n=55
    lower=2*sum(F(1,(2*k+1)*3**(2*k+1)) for k in range(n))
    tail=F(2,(2*n+1)*3**(2*n+1))*F(9,8)
    ln2=I(lower,lower+tail)
    return pi,ln2


def verify(log_bounds,etas,tail_total):
    root_log=log_bounds[9]
    root_gap=1-(F(9,10)+2*etas[0]*root_log)
    require(root_gap>0,'Root Q^2 Delta gate fails')
    cumulative=F(0);gaps=[]
    for r,eta in zip([9,12,8,7],etas):
        cumulative+=eta
        if r!=9:
            gap=1-(F(9,10)+cumulative*log_bounds[r])
            require(gap>0,'Retained-side Q Delta gate fails')
            gaps.append(gap)
    total=cumulative+tail_total
    tail_gap=1-(F(9,10)+2*total)
    require(tail_gap>0,'Tail retained-side gate fails')
    # Uniform upper bound for both Q^2 C and L Q^2, across all stages.
    fresh_packet_gap=1-total*(1+2*max(log_bounds.values()))
    require(fresh_packet_gap>0,'Fresh-side or packet gate fails')
    require(total<F(9,10),'Fresh degrees exceed retained degree cap')
    return {'root_gap':str(root_gap),
            'retained_gaps':[str(x) for x in gaps],
            'tail_gap':str(tail_gap),
            'fresh_and_packet_gap':str(fresh_packet_gap),
            'total_retention':str(total)}


def certificate():
    log_bounds={9:F(317,100),12:F(717,200),8:F(3),7:F(14037,5000),4:F(2)}
    log_checks=[]
    for base,bound in log_bounds.items():
        lhs=base**bound.denominator;rhs=2**bound.numerator
        require(lhs<=rhs,'Invalid rational logarithm upper bound')
        log_checks.append({'base':base,'upper':str(bound),'strict':lhs<rhs})
    etas=[F(63,4000),F(97,8000),F(21,4000),F(31,12500)]
    tail_total=F(2877,200000);q=F(63,100)
    eta4=tail_total*(1-q)
    require(eta4==F(106449,20000000),'Wrong first tail taper')
    gates=verify(log_bounds,etas,tail_total)
    require(q>F(11,20),'Minimum taper bootstrap fails')
    # At depth <= (3/4) log_(20/11)(lambda)+O(1), q^d >= c lambda^-3/4.
    # This gives u_d=Omega(lambda^1/4), while B=ceil(6log2 lambda).
    pi,ln2=constants();kappa=pi*sqrt(2)/ln2
    rs=[9,12,8,7,4]
    beta2=[F(1,3),F(137,400),F(279,800),F(891,2450),F(13,25)]
    betas=[sqrt(x) for x in beta2]
    alpha=[sqrt(2*(r-1))/r for r in rs]
    masses=[F(1),F(2,9),F(1,27),F(1,108),F(1,378)]
    for j in range(4):
        require(masses[j+1]==masses[j]*F(2,rs[j]),'Wrong child-size mass')
    Ks=[kappa*m/sqrt(e) for m,e in zip(masses,etas+[eta4])]
    cum=I.exact(0);branches=[];space=[]
    for i in range(4):
        branches.append(cum+betas[i]*Ks[i]);space.append(betas[i]*Ks[i])
        cum+=alpha[i]*Ks[i]
    gamma=F(1,2)/sqrt(q)
    tail_factor=alpha[4]/(1-gamma)
    require(tail_factor.lo>betas[4].hi,'Tail leaf route not dominant')
    branches.append(cum+Ks[4]*tail_factor);space.append(betas[4]*Ks[4])
    headline=pi/ln2*(sqrt(F(128000,5103))+sqrt(F(21920,7857)))
    memory=pi/ln2*sqrt(F(8000,189))
    require(headline.lo<=branches[1].hi and branches[1].lo<=headline.hi,
            'Closed-form time constant disagrees')
    require(memory.lo<=space[0].hi and space[0].lo<=memory.hi,
            'Closed-form space constant disagrees')
    for j,c in enumerate(branches):
        if j!=1:require(c.hi<branches[1].lo,'Another time branch dominates')
    for c in space[1:]:require(c.hi<space[0].lo,'Another memory branch dominates')
    require(headline.hi<F(3027,100),'Time does not certify <30.27')
    require(memory.hi<F(3686,125),'Space does not certify <29.488')
    require(headline.lo>F(1513,50),'Negative control 30.26 was accepted')
    # Deliberately malformed schedules must be rejected by exact gates.
    controls={}
    bad_eta=etas.copy();bad_eta[1]=F(1,80)
    for name,e,t in [('larger_second_taper',bad_eta,tail_total),
                     ('excessive_tail',etas,F(1,40))]:
        rejected=False
        try:verify(log_bounds,e,t)
        except ValueError:rejected=True
        require(rejected,'Failed negative control: '+name)
        controls[name]='REJECTED'
    controls['unsupported_time_bound_30_26']='REJECTED'
    return {'status':'PASS','arithmetic':'exact rational outward intervals',
            'logarithm_certificates':log_checks,'packing_gates':gates,
            'groups':rs,'prefix_etas':[str(x) for x in etas],
            'first_tail_eta':str(eta4),'tail_ratio':str(q),
            'beta_squared':[str(x) for x in beta2],
            'child_masses':[str(x) for x in masses],
            'pi_interval':pi.decimals(20),'ln2_interval':ln2.decimals(20),
            'time_branches':[x.decimals() for x in branches],
            'local_memory_branches':[x.decimals() for x in space],
            'time_coefficient':headline.decimals(),
            'space_coefficient':memory.decimals(),
            'eventual_time_coefficient':'30.27',
            'eventual_space_coefficient':'29.488',
            'negative_controls':controls}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    text=json.dumps(certificate(),indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text,encoding='utf-8')
    else:print(text,end='')
