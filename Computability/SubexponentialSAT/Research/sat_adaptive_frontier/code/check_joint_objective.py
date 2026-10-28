#!/usr/bin/env python3
"""Exact checks for the joint six-cost adaptive contraction certificate.

Standard library only.  All theorem-related assertions use Fraction or integer
arithmetic.  Finite graph checks validate rearrangement of the mode sum; they
are not tests of a complete SAT engine or of the imported fast-MM backend.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial, isqrt
from pathlib import Path
import json
import random


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def falling(a, b):
    answer = 1
    for j in range(b):
        answer *= a-j
    return answer


def edge_vector(c, d):
    incident = [F(int(j in (c, d))) for j in range(3)]
    if c == d:
        return incident+[F(0)]*3
    cls = {(0, 1): 0, (0, 2): 1, (1, 2): 2}[tuple(sorted((c, d)))]
    return incident+[F(2,5) if j == cls else F(1) for j in range(3)]


def centered(v):
    mean = sum(v)/6
    return [a-mean for a in v]


def color_covariance(k, endpoints):
    r = 3*k
    total = F(0)
    total_probability = F(0)
    for colors in product(range(3), repeat=endpoints):
        counts = [colors.count(c) for c in range(3)]
        weight = F(falling(k,counts[0])*falling(k,counts[1])*falling(k,counts[2]),
                   falling(r,endpoints))
        total_probability += weight
        a = centered(edge_vector(colors[0],colors[1]))
        if endpoints == 2:
            b = a
        elif endpoints == 3:
            b = centered(edge_vector(colors[0],colors[2]))
        else:
            b = centered(edge_vector(colors[2],colors[3]))
        total += weight*sum(x*y for x,y in zip(a,b))
    require(total_probability == 1, 'endpoint-color probabilities')
    return total


def covariance_certificate(r):
    k = r//3
    c0,c1,c2 = [color_covariance(k,v) for v in (2,3,4)]
    expected = {9:(F(109,120),F(869,4200),-F(379,2100)),
                12:(F(299,330),F(181,750),-F(3151,24750))}[r]
    require((c0,c1,c2) == expected, 'covariance ledger')
    p = F(2*k,r-1)
    require(c0 == (1-p)*F(5,6)+p*F(14,15), 'diagonal covariance')
    A = (1+F(17,5)*p)/6
    L0 = c0+2*(r-2)*c1+F((r-2)*(r-3),2)*c2
    L1 = c0+(r-4)*c1-(r-3)*c2
    L2 = c0-2*c1+c2
    require(c1 >= c2 and 0 <= L0 < L1 and 0 <= L2 <= L1,
            'covariance comparison gates')
    q = 1-L0/L1
    beta2 = (A*A*r*(r-1)/q+F(5,3)*L1)/(r*r)
    require(beta2 == {9:F(2489356,6638625),12:F(4786024,13540725)}[r],
            'joint coefficient simplification')
    return {'r':r,'endpoint_colorings':{'equal':9,'shared':27,'disjoint':81},
            'covariances':[str(x) for x in (c0,c1,c2)],
            'eigenvalues':[str(x) for x in (L0,L1,L2)],
            'mean_coefficient':str(A),'beta_squared':str(beta2)}


def equipartitions(r):
    k = r//3
    vertices = tuple(range(r))
    # Order blocks by their smallest elements: each unlabelled partition once.
    for aa in combinations(vertices[1:],k-1):
        a = (0,)+aa
        ar = set(a)
        rest = tuple(v for v in vertices if v not in ar)
        for bb in combinations(rest[1:],k-1):
            b = (rest[0],)+bb
            br = set(b)
            c = tuple(v for v in rest if v not in br)
            colors = [0]*r
            for v in b:
                colors[v] = 1
            for v in c:
                colors[v] = 2
            yield tuple(colors)


def six_costs(edges, weights, colors):
    answer = [F(0)]*6
    for e,w in zip(edges,weights):
        v = edge_vector(colors[e[0]],colors[e[1]])
        answer = [a+w*b for a,b in zip(answer,v)]
    return answer


def finite_objective_checks():
    r=9
    parts=list(equipartitions(r))
    require(len(parts)==280,'canonical equipartition count')
    edges=list(combinations(range(r),2))
    rng=random.Random(927618)
    cases=[[1]*len(edges),[int(0 in e) for e in edges],
           [int(e[1]<3) for e in edges],[int(i==0) for i in range(len(edges))]]
    cases += [[rng.randrange(23) for _ in edges] for _ in range(24)]
    L0,L1=F(3,200),F(1059,350)
    beta2=F(2489356,6638625)
    A=F(71,120)
    for x in cases:
        best=None; ev=F(0); mean_total=F(0)
        for p in parts:
            costs=six_costs(edges,x,p)
            mean=sum(costs)/6
            ev+=sum((z-mean)**2 for z in costs)
            mean_total+=mean
            best=max(costs) if best is None else min(best,max(costs))
        ev/=len(parts)
        require(mean_total/len(parts)==A*sum(x),'six-cost expected mean')
        norm2=sum(z*z for z in x);m=len(edges);H=sum(x)
        require(ev<=L1*(norm2-F(H*H,m))+L0*F(H*H,m),
                'six-cost quadratic bound on fixture')
        require(best*best<=F(r*r,2)*beta2*norm2,
                'joint adaptive coefficient on fixture')
    return {'r':r,'unlabelled_partitions':len(parts),'integer_entropy_fixtures':len(cases)}


def finite_graph_checks():
    """Literal small mode graphs versus selected-block contraction mod 2^11."""
    r=9;mod=2**11;rng=random.Random(726347)
    pairs=[(g,h) for g in range(r) for h in range(r) if g!=h]
    parts=list(equipartitions(r));run=0
    for active_count in range(9):
        for repetition in range(3):
            edges=rng.sample(pairs,active_count)
            h=[1]*active_count
            part=min(parts,key=lambda p:max(six_costs(edges,h,p)))
            best=max(six_costs(edges,h,part))
            require(best*best<=r*r*F(2489356,6638625)*active_count,
                    'directed fixture entropy bound')
            incident=[[i for i,e in enumerate(edges) if g in e] for g in range(r)]
            factors=[]
            for g in range(r):
                factors.append({bits:rng.randrange(mod)
                                for bits in product((0,1),repeat=len(incident[g]))})
            direct=0
            for bits in product((0,1),repeat=active_count):
                term=1
                for g in range(r):
                    term=term*factors[g][tuple(bits[i] for i in incident[g])]%mod
                direct=(direct+term)%mod
            tables=[];boundary=[]
            for block in range(3):
                group=[g for g in range(r) if part[g]==block]
                inc=[i for i,e in enumerate(edges) if any(part[g]==block for g in e)]
                cut=[i for i in inc if part[edges[i][0]]!=part[edges[i][1]]]
                result={}
                for values in product((0,1),repeat=len(inc)):
                    bits=dict(zip(inc,values));term=1
                    for g in group:
                        term=term*factors[g][tuple(bits[i] for i in incident[g])]%mod
                    key=tuple(bits[i] for i in cut)
                    result[key]=(result.get(key,0)+term)%mod
                tables.append(result);boundary.append(cut)
            cross=[i for i,e in enumerate(edges) if part[e[0]]!=part[e[1]]]
            contracted=0
            for vals in product((0,1),repeat=len(cross)):
                bits=dict(zip(cross,vals));term=1
                for block in range(3):
                    term=term*tables[block][tuple(bits[i] for i in boundary[block])]%mod
                contracted=(contracted+term)%mod
            require(contracted==direct,'selected-block contraction mismatch')
            run+=1
    return {'r':r,'cases':run,'maximum_nontrivial_directed_indices':8,
            'coefficient_modulus':mod,
            'scope':'Literal graph sum and cached block sum agree; no fast-MM backend tested.'}


class Interval:
    """Closed intervals with Fraction endpoints and outward sqrt rounding."""
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        require(self.lo <= self.hi, "reversed interval")
    def __add__(self, other):
        other = interval(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)
    __radd__ = __add__
    def __neg__(self):
        return Interval(-self.hi, -self.lo)
    def __sub__(self, other):
        return self + -interval(other)
    def __rsub__(self, other):
        return interval(other) + -self
    def __mul__(self, other):
        other = interval(other)
        vals = [a*b for a in (self.lo,self.hi)
                for b in (other.lo,other.hi)]
        return Interval(min(vals),max(vals))
    __rmul__ = __mul__
    def __truediv__(self, other):
        other = interval(other)
        require(not (other.lo <= 0 <= other.hi), "interval division by zero")
        return self * Interval(1/other.hi,1/other.lo)
    def __rtruediv__(self, other):
        return interval(other) / self
    def sqrt(self):
        require(self.lo >= 0, "negative sqrt")
        q = 10**65
        low = isqrt(self.lo.numerator*q*q//self.lo.denominator)
        high = isqrt(self.hi.numerator*q*q//self.hi.denominator)+1
        return Interval(F(low,q),F(high,q))
    def decimal_bounds(self, digits=15):
        q = 10**digits
        low = self.lo.numerator*q//self.lo.denominator
        high = -((-self.hi.numerator*q)//self.hi.denominator)
        def show(n):
            return f"{n//q}.{n%q:0{digits}d}"
        return [show(low),show(high)]


def interval(x):
    return x if isinstance(x, Interval) else Interval(x)


def arctan_interval(inv, terms=120):
    x = F(1,inv)
    total = sum(((-1)**j)*x**(2*j+1)/F(2*j+1) for j in range(terms))
    next_term = ((-1)**terms)*x**(2*terms+1)/F(2*terms+1)
    return Interval(min(total,total+next_term),max(total,total+next_term))


def log_from_atanh(x, terms=150):
    x = F(x)
    total = 2*sum(x**(2*j+1)/F(2*j+1) for j in range(terms))
    remainder = 2*x**(2*terms+1)/(F(2*terms+1)*(1-x*x))
    return Interval(total,total+remainder)


def schedule_certificate():
    pi=16*arctan_interval(5)-4*arctan_interval(239)
    ln2=log_from_atanh(F(1,3));ln3=log_from_atanh(F(1,2))
    kap=pi*interval(2).sqrt()/ln2
    A=1/(20*(2*ln3/ln2))
    K=[kap/A.sqrt(),2*kap/(9*(F(1,36)-A).sqrt()),
       kap*interval(288).sqrt()/27,
       2*kap*interval(F(864,5)).sqrt()/243,
       2*kap*interval(189).sqrt()/729]
    a=[interval(F(4,9)),interval(22).sqrt()/12,interval(F(4,9)),
       interval(10).sqrt()/6,interval(6).sqrt()/4]
    b9=interval(F(2489356,6638625)).sqrt()
    b12=interval(F(4786024,13540725)).sqrt()
    b=[b9,b12,b9,interval(30).sqrt()/6,interval(12).sqrt()/4]
    prefix=interval(0);competitors=[]
    for i in range(4):
        competitors.append(prefix+b[i]*K[i])
        prefix+=a[i]*K[i]
    tail_factor=a[4]/(1-1/interval(2).sqrt())
    require(tail_factor.lo>b[4].hi,'constant-four tail comparison')
    competitors.append(prefix+tail_factor*K[4])
    headline=competitors[0]
    for x in competitors[1:]:
        require(x.hi<headline.lo,'competing depth exceeds root')
    space=[b9*K[0],b12*K[1],b9*K[2],a[3]*K[3],a[4]*K[4]]
    for x in space[1:]:
        require(x.hi<headline.lo,'space coefficient exceeds root')
    require(headline.hi<F(31253,1000),'safe eventual coefficient')
    oldtime=pi*interval(24339).sqrt()/(20*ln2)
    oldspace=pi*interval(915).sqrt()/(4*ln2)
    require(headline.hi<oldtime.lo and headline.hi<oldspace.lo,
            'incoming coefficient comparison')
    require(F(1,36)+F(1,288)==F(1,32),'second cumulative cap')
    require(F(1,32)+F(5,864)==F(1,27),'third cumulative cap')
    require(F(1,27)+F(2,189)==F(1,21),'tail cumulative cap')
    require(12**100<2**359 and 9**40<2**127 and 6**5<2**13,
            'rational logarithm bounds')
    margins=[1-(F(9,10)+F(359,100)/36),
             1-(F(9,10)+F(127,40)/32),
             1-(F(9,10)+F(13,5)/27),
             1-(F(9,10)+F(2,21))]
    require(margins==[F(1,3600),F(1,1280),F(1,270),F(1,210)],
            'retained-side exact margins')
    for logcap,cap in [(F(359,100),F(1,36)),(F(127,40),F(1,32)),
                       (F(13,5),F(1,27)),(F(2),F(1,21))]:
        require((2*logcap+1)*cap<1,'fresh side and padding exponent')
    require(F(2)**3<F(9,5)**4,'positive tail retained-range exponent')
    return {'time_competitors':[x.decimal_bounds() for x in competitors],
            'space_competitors':[x.decimal_bounds() for x in space],
            'headline_time_and_space':headline.decimal_bounds(),
            'safe_eventual_coefficient':'31.253',
            'K_coefficients':[x.decimal_bounds() for x in K],
            'incoming_time':oldtime.decimal_bounds(),
            'incoming_space':oldspace.decimal_bounds(),
            'retained_side_exponent_margins':[str(x) for x in margins],
            'tail_coarse_shrinkage':'5/9',
            'tail_geometric_K_ratio':'1/sqrt(2)'}


def main():
    result={'status':'passed',
            'covariance':[covariance_certificate(9),covariance_certificate(12)],
            'finite_objective_checks':finite_objective_checks(),
            'finite_graph_checks':finite_graph_checks(),
            'exact_interval_schedule_certificate':schedule_certificate(),
            'limitations':['No complete SAT engine or formal proof-assistant check.',
                           'The exact quotient-ring fast matrix multiplication bridge is imported.',
                           'Finite examples supplement the stated all-size mathematical proof.']}
    path=(Path(__file__).resolve().parents[1] / "results" / 'joint_objective_checks.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
