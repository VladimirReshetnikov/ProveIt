#!/usr/bin/env python3
"""Original exact checks for composing late streamed separators with our schedules.
No incoming code is executed/imported. Polynomial-space arithmetic certificate only.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt, log, log2, pi, sqrt
from pathlib import Path
import json
import sys

def demand(condition, message):
    if not condition:
        raise ArithmeticError(message)

@lru_cache(None)
def path_pairs(r):
    demand(isinstance(r,int) and r>=1,'invalid alphabet')
    if r==1:
        return 0
    lo,hi=r//2,r-r//2
    return 2*lo*hi+max(path_pairs(lo),path_pairs(hi))

# Independent explicit path enumeration, not the recurrence under test.
def path_sets(groups):
    if len(groups)==1:
        return [set()]
    k=len(groups)//2
    left,right=groups[:k],groups[k:]
    cut={(a,b) for a in left for b in right}|{(b,a) for a in left for b in right}
    return [cut|p for side in (left,right) for p in path_sets(side)]
for r in range(1,65):
    paths=path_sets(tuple(range(r)))
    demand(len(paths)==r,'wrong leaf count')
    demand(max(map(len,paths))==path_pairs(r),'path enumeration disagrees')
    demand(all(len(p)<=r*(r-1) for p in paths),'path exceeds pair graph')
for power in range(0,7):
    r=2**power
    demand(path_pairs(r)==2*(r*r-1)//3,'power-of-two formula disagrees')

S=10**6
def sqrt_lo(x):
    ans=F(isqrt(x.numerator*S*S//x.denominator),S)
    demand(ans*ans<=x,'invalid sqrt lower bound')
    return ans

def sqrt_hi(x):
    ans=F(isqrt(x.numerator*S*S//x.denominator)+1,S)
    demand(ans*ans>x,'invalid sqrt upper bound')
    return ans

atan5_upper=sum(((-1)**j*F(1,(2*j+1)*5**(2*j+1)) for j in range(9)),F())
atan5_lower=sum(((-1)**j*F(1,(2*j+1)*5**(2*j+1)) for j in range(10)),F())
atan239_lower=F(1,239)-F(1,3*239**3)
atan239_upper=atan239_lower+F(1,5*239**5)
demand(16*atan5_upper-4*atan239_lower<F(355,113),'pi upper certificate')
demand(16*atan5_lower-4*atan239_upper>F(314159,100000),'pi lower certificate')
ln2_partial=2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(8)),F())
ln2_tail_upper=2*F(1,17*3**17)/(1-F(1,9))
demand(ln2_partial>F(693,1000),'ln2 lower certificate')
demand(ln2_partial+ln2_tail_upper<F(693148,1000000),'ln2 upper certificate')
P=F(355,113)/F(693,1000)
ratio_upper=F(4,3)/sqrt_lo(F(3))
demand(ratio_upper<1,'tail ratio must converge')

specs=[
 ('generic',F(9,10),[13,14,8,6,5,4,4],list(map(F,['27/2000','21/800','333/10000','1933/50000','861/20000','1183/25000','4999/100000'])),F(63,1000),F(1107,20)),
 ('degree_51',F(51,100),[15,15,8,6,5,4,4],list(map(F,['627/10000','2269/20000','357/2500','81/500','1771/10000','1911/10000','1999/10000'])),F(239,1000),F(126,5))]
results=[]
for name,gamma,rs,cumul,limit,target in specs:
    mass=F(1);prev=F();raw=F();terms=[];guards=[]
    for d,(r,a) in enumerate(zip(rs,cumul)):
        x=a-prev
        demand(x>0,'nonpositive retained budget')
        factor=2 if d==0 else 1
        for kind,logbound in [('degree',(1-gamma)/(factor*a)),('rounding',(1-a)/(2*a))]:
            demand(r**logbound.denominator<2**logbound.numerator,'packing '+kind+' failed')
            guards.append({'depth':d,'kind':kind,'integer_guard':f'{r}^{logbound.denominator}<2^{logbound.numerator}'})
        v=path_pairs(r)
        # kappa_separator(r) = (pi/ln2) sqrt(2 v(r)/r^2).
        raw+=mass*sqrt_hi(F(2*v,r*r)/x)
        terms.append(pi/log(2)*float(mass)*sqrt(float(F(2*v,r*r)/x)))
        mass*=F(2,r);prev=a
    demand(limit>prev and limit<gamma,'invalid tail degree budget')
    for kind,logbound in [('degree',(1-gamma)/limit),('rounding',(1-limit)/(2*limit))]:
        demand(3**logbound.denominator<2**logbound.numerator,'tail packing failed')
        guards.append({'depth':'tail','kind':kind,'integer_guard':f'3^{logbound.denominator}<2^{logbound.numerator}'})
    first_tail=(limit-prev)/4
    raw+=mass*sqrt_hi(F(2*path_pairs(3),9)/first_tail)/(1-ratio_upper)
    upper=P*raw
    demand(upper<target,'new streamed coefficient exceeds target')
    tail=pi/log(2)*float(mass)*sqrt(float(F(2*path_pairs(3),9)/first_tail))/(1-(2/3)/sqrt(.75))
    results.append({'name':name,'gamma':str(gamma),'alphabets':rs,
                    'cumulative_budgets':[str(a) for a in cumul],
                    'path_pair_counts':[path_pairs(r) for r in rs],
                    'guards':guards,'prefix_coefficient_displays':terms,
                    'tail_coefficient_display':tail,'coefficient_display':sum(terms)+tail,
                    'certified_rational_upper':str(upper),'certified_upper_display':float(upper),
                    'simple_eventual_target':str(target)})

# Late fixed-r16 theorem is separated from our upper bound using exact intervals.
baseline_lower=F(5,2)*F(314159,100000)/F(693148,1000000)*sqrt_lo(F(17))*(1+1/(3*sqrt_hi(F(3))))
demand(baseline_lower>F(557,10),'late baseline lower enclosure failed')
demand(F(results[0]['certified_rational_upper'])<baseline_lower,'no certified improvement')
# Stronger comparisons compose the same late separator with both late adaptive schedules.
late_adaptive_comparisons=[]
for label,xs in [
    ('subexponential_sat_frontier',list(map(F,['27/2000','51/4000','141/20000','107/20000']))),
    ('sat_frontier_improvements',list(map(F,['27/2000','159/12500','71/10000','533/100000'])))]:
    mass=F(1); lower_raw=F(); shown=0.0
    for r,x in zip([13,14,8,6],xs):
        z=F(2*path_pairs(r),r*r)/x
        lower_raw+=mass*sqrt_lo(z)
        shown+=pi/log(2)*float(mass)*sqrt(float(z))
        mass*=F(2,r)
    z=F(2*path_pairs(4),16)/F(27,6400)
    lower_raw+=mass*sqrt_lo(z)/(1-sqrt_lo(F(2,5)))
    shown+=pi/log(2)*float(mass)*sqrt(float(z))/(1-sqrt(.4))
    low=F(314159,100000)/F(693148,1000000)*lower_raw
    demand(low>F(277,5),'late adaptive composition lower enclosure failed')
    demand(F(results[0]['certified_rational_upper'])<low,'no improvement over adaptive combination')
    late_adaptive_comparisons.append({'name':label,'coefficient_display':shown,
        'certified_rational_lower':str(low),'certified_lower_display':float(low)})
if '--negative-control=constant' in sys.argv:
    demand(F(results[0]['certified_rational_upper'])<1,'deliberate wrong constant bound rejected')
if '--negative-control=guard' in sys.argv:
    demand(path_pairs(16)==169,'deliberate wrong cut-profile guard rejected')
output={'status':'PASS','scope':'Streamed separator/schedule composition; no SAT benchmark.',
        'path_profile_cases':64,'power_of_two_cases':7,'schedules':results,
        'late_fixed16_baseline_lower':str(baseline_lower),
        'late_fixed16_baseline_lower_display':float(baseline_lower),
        'late_adaptive_separator_comparisons':late_adaptive_comparisons}
Path(next((arg.split('=',1)[1] for arg in sys.argv[1:] if arg.startswith('--output=')), str(Path(__file__).with_name('streamed_composition_checks.json')))).write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
