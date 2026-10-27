#!/usr/bin/env python3
"""Original exact audit of the fixed-alphabet combined certificate frontier.
Does not import or execute supplied proposal code. These lower bounds concern
explicit worst-case upper-certificate expressions, never algorithm runtimes.
"""
from fractions import Fraction as F
from pathlib import Path
import json
from math import isqrt

def require(condition, message):
    if not condition:
        raise ArithmeticError(message)

def cube_lower(x, scale=10**8):
    lo, hi = 0, scale
    while hi-lo > 1:
        mid=(lo+hi)//2
        if mid**3*x.denominator <= x.numerator*scale**3:
            lo=mid
        else:
            hi=mid
    q=F(lo,scale)
    require(q**3 <= x < F(hi,scale)**3, 'cube-root bracket')
    return q

# Certify the conservative transcendental bounds, rather than trusting floats.
def atan_interval(x, pairs=16):
    lo=sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(2*pairs)),F(0))
    return lo,lo+x**(4*pairs+1)/F(4*pairs+1)
al,ah=atan_interval(F(1,5));bl,bh=atan_interval(F(1,239))
pi_lo,pi_hi=16*al-4*bh,16*ah-4*bl
N=30
ln_lo=2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(N)),F(0))
ln_hi=ln_lo+F(2,2*N+1)*F(1,3**(2*N+1))/F(8,9)
require(pi_lo>F(314,100) and pi_hi<F(31416,10000),'Machin pi bounds')
require(ln_lo>F(693147,1000000) and ln_hi<F(694,1000),'atanh log2 bounds')
# pi>3.14 and ln2<.694 are used only conservatively.
kappa_squared_lower = 2*F(314,100)**2/F(694,1000)**2
log_lower={3:F(158,100),4:F(2),5:F(232,100),6:F(258,100),7:F(280,100),
           8:F(3),9:F(316,100),10:F(332,100),11:F(345,100)}
for r,L in log_lower.items():
    require(r**L.denominator >= 2**L.numerator, 'log2 lower witness')

rows=[]
# Relax the root cap, giving a weaker but simpler lower bound valid for every
# positive taper allocation with sum u_d/lambda <= .1/log2 r. Holder gives
# min sum c^d/sqrt(u_d/lambda) = [A(1-c^(2/3))^3]^-1/2.
for r in range(3,8):
    z=cube_lower(F(4,r*r))
    lower=kappa_squared_lower*F(2*(r-1),r*r)*10*log_lower[r]/(1-z)**3
    require(lower>38**2, 'fixed alphabet cache-chain exclusion')
    rows.append({'r':r,'mechanism':'relaxed full cache-chain Holder bound',
                 'coefficient_squared_lower':str(lower),
                 'coefficient_lower_display':float(lower)**.5,
                 'all_tapers_excluded_below_38':True})

# Every three-block partition. Since log2(7)>14/5, tau=log2(7)-2>4/5.
require(7**5>2**14,'Strassen exponent lower witness')
partitions=[]
for r in range(8,12):
    local=[]
    for a in range(1,r//3+1):
        for b in range(a,(r-a)//2+1):
            c=r-a-b
            require(a<=b<=c,'partition order')
            build=max(F(2*r*z-z*z-z,r*r) for z in (a,b,c))
            counts=(2*a*b,2*a*c,2*b*c)
            matrix=F(sum(counts),r*r)-F(9,25)*F(min(counts),r*r)
            beta2=max(build,matrix)
            lower=kappa_squared_lower*20*log_lower[r]*beta2
            require(lower>38**2,'fixed alphabet root-table exclusion')
            local.append({'blocks':[a,b,c],'beta_squared_lower':str(beta2),
                          'coefficient_squared_lower':str(lower)})
    require(bool(local),'nonempty partition enumeration')
    smallest=min(F(x['coefficient_squared_lower']) for x in local)
    rows.append({'r':r,'mechanism':'root table, every three-block partition',
                 'partitions':len(local),'coefficient_squared_lower':str(smallest),
                 'coefficient_lower_display':float(smallest)**.5,
                 'all_tapers_excluded_below_38':True})
    partitions.append({'r':r,'partitions':local})

# For r>=12, some block k>=r/3. Its build coefficient squared is at least
# 5/9-1/(3r)>=19/36; log2 r>=log2 12>7/2. This handles all larger integers.
require(12**2>2**7,'large-r logarithm lower witness')
large=kappa_squared_lower*20*F(7,2)*F(19,36)
require(large>38**2,'all r>=12 root-build exclusion')

def sqrt_upper(x,scale=10**14):
    n=isqrt((x.numerator*scale*scale)//x.denominator)
    require(F(n,scale)**2<=x<F(n+1,scale)**2,'square root bracket')
    return F(n+1,scale)

# A feasible old-family comparator, not merely an excluded-boundary infimum.
require(7**125<2**351,'Strassen exponent upper witness')
alpha2=F(14,64); beta2=(30+12*F(101,125)**2)/64; J2=F(30,64)
x0=F(333,20000);v1=F(999,100000);q=F(2,5);c=F(1,4)
require(x0+v1/(1-q)==F(333,10000),'comparator total taper budget')
require(6*x0<F(1,10) and 3*F(333,10000)<F(1,10),'comparator root/old-side capacities')
require(7*F(333,10000)<1 and q>F(1,3),'comparator fresh-degree and depth guards')
kappa2_upper=2*F(31416,10000)**2/F(693147,1000000)**2
K0=sqrt_upper(kappa2_upper/x0);K1=sqrt_upper(c*c*kappa2_upper/v1)
alpha=sqrt_upper(alpha2);beta=sqrt_upper(beta2);J=sqrt_upper(J2)
gamma=sqrt_upper(c*c/q)
time_upper=max(beta*K0,alpha*K0+K1*max(beta,alpha/(1-gamma)))
space_upper=max(J*K0,J*K1)
require(time_upper<F(191,5),'valid previous family time below38.2')
require(space_upper<F(341,10),'valid previous family space below34.1')
comparator={'alphabet':8,'blocks':[2,3,3],'root_u_fraction':str(x0),
            'tail_first_u_fraction':str(v1),'tail_ratio':str(q),
            'time_upper':str(time_upper),'space_upper':str(space_upper),
            'time_upper_display':float(time_upper),'space_upper_display':float(space_upper),
            'certified_time':38.2,'certified_space':34.1}
result={'status':'pass','scope':'Lower bounds on specified fixed-alphabet three-block cached upper-certificate family, not algorithm runtime lower bounds.',
        'root_degree_exponent':'9/10','root_budget':'(1/20)/log2(r)',
        'total_budget':'(1/10)/log2(r)','r3_to_11':rows,'partitions':partitions,
        'r_ge_12':{'coefficient_squared_lower':str(large),
                   'coefficient_lower_display':float(large)**.5,'all_excluded_below_38':True},
        'valid_previous_comparator':comparator,
        'conclusion':'Every fixed r>=3 and every three-block partition, with any admissible taper allocation in the stated family, has certificate coefficient strictly greater than38.'}
path=Path(__file__).with_name('fixed_alphabet_frontier_checks.json')
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'pass','minimum_certified_lower':min([x['coefficient_lower_display'] for x in rows]+[float(large)**.5]),'output':str(path)},indent=2))
