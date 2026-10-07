#!/usr/bin/env python3
"""Bounded fixed-prime-support diagnostics for Report283, offline and read-only.

The arbitrary-parameter proof is in article.tex. This program never evaluates
its genuine threshold, q, Q13, N0, k0 or witness N. Surrogate numerical constants
are labelled explicitly. Runtime guards survive Python -O.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256, sha1
from math import comb, gcd
from pathlib import Path
import json
import re

ROOT = Path(__file__).absolute().parents[1]
COMMIT = '5c9a442d263632fdcd4e9690154c12c2dcc70b53'
SOURCE_HASHES = {
 'Definitions.lean':'17241a9ffa53e2c6b335eb326920952a7f3da25e5e5a601a7aca5606462f5e4b',
 'Sections12_13.lean':'6e6318bcce96a0e2023f6743d9c52cc1f9bd6b416beeeec6c3841916334743d8',
 'Section10.lean':'8b63d784485ba8291b614a9153399cae216d2adaf37c9770344521083523cb2d',
 'Proofs13BilinearExtraction.lean':'9ce5b98fa823afda968e31ddbdfc76d684e34a3a566d4499d195cab6ccd4547f',
 'Proofs13CompleteRowExtraction.lean':'f0bcfc7913e27d811d8c001d396e828ccde24a11f8cb0c6831c8f6300e9664d5',
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def integer(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(name + ' outside bounded integer domain')
    return value


def prime(value):
    integer(value, 'prime', 2, 19)
    if any(value % d == 0 for d in range(2, value)):
        raise ValueError('prime required')
    return value


def centered(value, modulus):
    integer(modulus, 'modulus', 2, 4096)
    if type(value) is not int:
        raise ValueError('integer residue required')
    return min(value % modulus, (-value) % modulus)


def models():
    answer = []
    for p in (2,3,5,7,11,13,17,19):
        n, k = p, 1
        while n <= 256:
            answer.append((p,k,n))
            n, k = n*p, k+1
    return tuple(answer)


def prime_support(n):
    integer(n, 'factorization argument', 2, 4096)
    primes = []; divisor = 2
    while divisor*divisor <= n:
        if n % divisor == 0:
            primes.append(divisor)
            while n % divisor == 0:
                n //= divisor
        divisor += 1
    if n > 1:
        primes.append(n)
    return tuple(primes)


def fixed_r_domain(r, n, cap=1024, support=True):
    integer(cap, 'modulus cap', 2, 4096)
    if type(support) is not bool:
        raise ValueError('boolean support flag required')
    integer(r, 'fixed step', 2, 32); integer(n, 'modulus', 2, cap)
    if n % r:
        raise ValueError('r must divide N')
    if support and not set(prime_support(n)) <= set(prime_support(r)):
        raise ValueError('every prime divisor of N must divide r')
    return r, n


def mixed_models():
    # Algebra-only cases need r|N and rad(N)|r, not a density exponent s.
    # Several exponent pairs vary independently: 72=2^3*3^2, 108=2^2*3^3;
    # 200=2^3*5^2, 400=2^4*5^2, 1000=2^3*5^3.
    return ((4,32),(4,128),(6,36),(6,72),(6,108),(6,216),(6,432),(6,648),
            (10,100),(10,200),(10,400),(10,1000),(12,144),(12,288),
            (12,432),(15,225))


def fixed_support_affine(r, n):
    """Exhaust slopes/points; forced-intercept histograms cover all N^2 maps."""
    fixed_r_domain(r,n)
    global_max = class_max = 0
    for slope in range(n):
        require(gcd(r*slope-1,n) == 1, 'fixed-support multiplier is not a unit')
        inverse = pow(1-r*slope,-1,n)
        by_class = Counter(); by_intercept = Counter()
        for x in range(n):
            j,residue = divmod(x,r)
            offset = (j-slope*x) % n
            by_class[(residue,offset)] += 1
            by_intercept[offset] += 1
            # Independently invert the agreement equation at every observed point.
            require((inverse*(slope*residue+offset)) % n == j,
                    'modular-solution and histogram mismatch')
        class_max = max(class_max,max(by_class.values()))
        global_max = max(global_max,max(by_intercept.values()))
        require(max(by_class.values()) == 1, 'multiple agreements in one residue class')
        require(max(by_intercept.values()) <= r, 'global affine cap exceeded')
    require(global_max == r and class_max == 1, 'agreement bound or sharpness mismatch')
    return dict(r=r,N=n,slopes=n,point_tests=n*n,affine_maps_covered=n*n,
                inverse_equation_checks=n*n,per_class_max=class_max,global_max=global_max)


def affine_histogram(p, k):
    """Retained prime-power API with its original, stricter caps."""
    prime(p); integer(k, 'exponent', 1, 8)
    n = p**k; integer(n, 'affine modulus', 2, 256)
    return dict(fixed_support_affine(p,n),p=p,k=k)


def carrier_checks():
    count = 0; wrapped = 0
    for p,k,n in models():
        for start in range(n):
            for length in range(n//p+3):
                points = {(start+p*j)%n for j in range(length)}
                require(len(points) == min(length,n//p), 'wrong progression cardinality')
                require(all(x % p == start % p for x in points), 'carrier leaves class')
                count += 1
                wrapped += int(length > 0 and start+p*(length-1) >= n)
    return dict(carriers=count,wrapped_parameterizations=wrapped,
                lengths_tested='zero through additive period plus two')


def fixed_r_alias_case(r, n, theta):
    # This construction only needs divisibility, not prime support.
    fixed_r_domain(r,n,support=False)
    if type(theta) is not F or not 0 < theta < 1 or theta.denominator > 10000:
        raise ValueError('bounded positive rational cutoff below one required')
    radius=1/(2*r*theta); k0=radius.numerator//radius.denominator
    integer(k0,'toy radius',0,512)
    indexed=[(nu,j) for nu in range(r) for j in range(-k0,k0+1)]
    cover={(nu*(n//r)+j)%n for nu,j in indexed}
    preimage={freq for freq in range(n) if centered(r*freq,n) <= 1/(2*theta)}
    require(cover == preimage,'alias cover is not the exact centered preimage')
    for nu,j in indexed:
        b=(nu*(n//r)+j)%n
        require(r*b % n == r*j % n,'alias not killed by common step')
        require(centered(r*b,n) <= r*abs(j),'wrong centered norm bound')
    # Exact frequency multisets for a short strip: no complex arithmetic.
    m=min(5,n//r)
    for freq in range(n):
        baseline=Counter((r*freq*j)%n for j in range(m))
        for nu in range(r):
            require(Counter((r*(freq+nu*(n//r))*j)%n for j in range(m)) == baseline,
                    'Fourier alias phase multiset mismatch')
    if 1/theta >= r:
        require(len(indexed) <= 1/theta+r <= 2/theta,'indexed q bound failed')
    return dict(r=r,N=n,theta=str(theta),K0=k0,q=len(indexed),
                distinct_cover=len(cover),radius_integral=radius.denominator==1,
                scope='Rational surrogate cutoff; not the genuine source cutoff')


def alias_case(p, k, theta):
    prime(p); integer(k,'exponent',1,8)
    n=p**k; integer(n,'alias modulus',2,256)
    return dict(fixed_r_alias_case(p,n,theta),p=p,k=k)


def annihilator_case(r, n, m):
    fixed_r_domain(r,n,cap=4096,support=False)
    integer(m,'annihilator strip width',1,min(16,n//r))
    points=tuple(r*j for j in range(m))
    kernel=tuple(nu*(n//r) for nu in range(r))
    require(set(kernel) == {freq for freq in range(n) if r*freq % n == 0},
            'annihilator enumeration mismatch')
    for freq in kernel:
        phases=Counter((freq*x)%n for x in points)
        require(phases == {0:m},'annihilator Fourier phase is not identically one')
    # For f_h=N*1_T, every phase is 1, hence the coefficient is exactly N*m.
    require(n*m == F(m,n)*n*n,'annihilator Fourier normalization failed')
    return dict(r=r,N=n,m=m,kernel_size=len(kernel),phase_tests=r*m,
                exact_annihilator_coefficient=n*m,all_phases_one=True)


def subgroup_case(r, n):
    fixed_r_domain(r,n,support=False)
    kernel=tuple(nu*(n//r) for nu in range(r))
    minimum=None; thirds=0; trivial=0; carrier_count=0
    for step in range(n):
        image={freq*step % n for freq in kernel}
        order=r//gcd(r,step)
        require(len(image) == order,'annihilator image order formula failed')
        require(image == {j*(n//order) for j in range(order)},'wrong image subgroup')
        peak=max(centered(x,n) for x in image)
        expected=F(n*(order//2),order)
        require(peak == expected,'exact centered subgroup maximum failed')
        if order > 1:
            require(3*peak >= n and 4*peak > n,'nontrivial subgroup too narrow')
            ratio=F(peak,n); minimum=ratio if minimum is None else min(minimum,ratio)
            thirds += int(3*peak == n)
        else:
            trivial += 1
            require(image == {0} and step % r == 0,'trivial image divisibility failed')
            require(gcd(step,n) > 1,'r-divisible step unexpectedly a unit')
            # Entire periods include arbitrary starts and wrap across the cut.
            for start in (0,n-1):
                carrier={(start+step*j)%n for j in range(n//gcd(step,n))}
                require({x%r for x in carrier} == {start%r},'divisible step leaves class')
                carrier_count += 1
        require((3*peak < n) == (step % r == 0),'strict one-third rigidity failed')
        require((4*peak < n) == (step % r == 0),'one-quarter rigidity failed')
    return dict(r=r,N=n,steps=n,trivial_images=trivial,
                minimum_nontrivial_radius=str(minimum),sharp_third_steps=thirds,
                full_period_divisible_step_carriers=carrier_count)


def sharp_radius_checks():
    for order in range(2,129):
        radius=F(order//2,order)
        require(radius >= F(1,3),'finite subgroup one-third bound failed')
        require((radius == F(1,3)) == (order == 3),'sharp radius equality changed')
    r,n,step=6,72,2
    image={step*nu*(n//r)%n for nu in range(r)}
    require(image == {0,24,48} and max(centered(x,n) for x in image) == n//3,
            'sharp order-three image changed')
    require(step % r != 0,'sharpness witness has divisible step')
    return dict(orders_checked=127,order_range=[2,128],sharp_radius='1/3',
                weak_radius_counterexample=dict(r=r,N=n,step=step,image=sorted(image)),
                strict_inequality_required=True)


def joint_sums(n, points, values, order):
    integer(n,'joint modulus',2,4096); integer(order,'order',1,9)
    if type(points) is not tuple or type(values) is not tuple or not 1 <= len(points) <= 16:
        raise ValueError('bounded nonempty tuples required')
    if len(points) != len(values) or len(set(points)) != len(points):
        raise ValueError('distinct points and matching values required')
    for x in points+values:
        integer(x,'coordinate',0,n-1)
    counts=Counter({(0,0):1})
    for _ in range(order):
        new=Counter()
        for (x,y),count in counts.items():
            for a,b in zip(points,values):
                new[((x+a)%n,(y+b)%n)] += count
        if len(new)>100000:
            raise ValueError('joint state cap exceeded')
        counts=new
    return dict(counts)


def interval_coefficient(m, order, t):
    integer(m,'interval size',1,16); integer(order,'order',1,9)
    integer(t,'coefficient index',0,order*(m-1))
    return sum((-1)**j * comb(order,j)*comb(t-j*m+order-1,order-1)
               for j in range(min(order,t//m)+1))


def fixed_support_strip_case(r,n,s):
    fixed_r_domain(r,n,cap=4096)
    integer(s,'density exponent',2,12)
    if r**s < 8*r or n % (r**s):
        raise ValueError('require r^s >= 8r and r^s dividing N')
    m=n//(r**s); integer(m,'strip width',1,16)
    require(r*m <= F(n,8),'strip density bound failed')
    require(8*(m-1) < n//r,'no-wrap inequality failed')
    points=tuple(r*j for j in range(m)); values=tuple(range(m))
    observed=joint_sums(n,points,values,8)
    expected={((r*t)%n,t%n):interval_coefficient(m,8,t) for t in range(8*(m-1)+1)}
    require(observed == expected,'joint convolution and binomial coefficients disagree')
    by_domain=Counter()
    images={}
    for (x,y),count in observed.items():
        by_domain[x]+=count
        require(x not in images or images[x] == y,'order-eight Freiman failure')
        images[x]=y
    energy=sum(count*count for count in by_domain.values())
    require(sum(observed.values()) == m**8,'ordered tuple count mismatch')
    require(energy*n >= m**16,'Cauchy-Schwarz energy lower bound failed')
    fixed=n**16*energy
    require(fixed >= m**16*n**15,'fixed-height normalization failed')
    return dict(r=r,s=s,N=n,m=m,additive_energy=energy,
                fixed_height_arrangements=str(fixed),joint_states=len(observed),
                annihilator=annihilator_case(r,n,m),
                scope='Small admissible strip algebra; not a full-budget witness')



def strip_case(p,k,s):
    prime(p); integer(k,'exponent',2,12); integer(s,'density exponent',2,k)
    n=p**k; integer(n,'strip modulus',2,4096)
    return dict(fixed_support_strip_case(p,n,s),p=p,k=k)


def monomial_power(pair, exponent):
    if type(pair) is not tuple or len(pair)!=2 or type(exponent) not in (int,F):
        raise ValueError('two formal exponents and a rational power required')
    return tuple(F(x)*exponent for x in pair)


def monomial_mul(left,right):
    return tuple(F(x)+F(y) for x,y in zip(left,right))


def symbolic_checks():
    # Pair (u,v) denotes 2^u a^v. K-scaled exponents are reported separately.
    t=(-4,32)
    theta=monomial_mul((-37,0),monomial_power(t,F(11,2)))
    K=monomial_mul((74,0),monomial_power(t,-10))
    znum=monomial_mul((-155,0),monomial_power(t,18))
    theta1=monomial_mul((-1882,0),monomial_power(theta,10477))
    b=monomial_mul((1882,0),monomial_power(theta,-10479))
    relative=monomial_mul(b,(-(2**20)+1,2**21))
    identities={'theta':(theta,(-59,176)),'K':(K,(114,-320)),
      'z_numerator_per_K':(znum,(-227,576)),
      'theta1':(theta1,(-620025,1843952)), 'b':(b,(620143,-1844304)),
      'b_over_Q13_half':(relative,(-428432,252848)),
      'theta1_times_b':(monomial_mul(theta1,b),(118,-352)),
      'W_times_delta':(monomial_mul((135,-704),(-43,224)),(92,-480)),
      'theta_over_a32_quarter':(monomial_mul(theta,(2,-32)),(-57,144)),
      'theta_over_a':(monomial_mul(theta,(0,-1)),(-59,175)),
      'd_times_pi':(monomial_mul(theta1,(-6,0)),(-620031,1843952)),
      'd_over_eight_lower_using_pi_lt_four':
          (monomial_mul(theta1,(-11,0)),(-620036,1843952))}
    for name,(actual,expected) in identities.items():
        require(actual == expected,'formal monomial identity failed: '+name)
    # Q<=2^Q and 4Q^3<2^(7Q), bounded integer checks supplement the real proof.
    for q in range(2,81):
        require(q <= 2**q and 4*q**3 < 2**(7*q),'scalar comparison check failed')
    # Compare exponent coefficients at K>=2^114; no actual 2^(-228K) is formed.
    k_lower=2**114
    two_margin=1+228*k_lower-620036
    density_margin=576*k_lower-1843952
    require(two_margin > 0 and density_margin >= 0,'c < d/8 exponent margins failed')
    # The exact ceiling K is integral after a=r^-s, never expanded here.
    samples=[]
    for r,s in ((2,4),(3,3),(5,3),(11,2),(19,2),(4,3),(6,3),(10,2),(12,2),(15,2)):
        require(r**s >= 8*r,'sample density inadmissible')
        require(480*s > 1,'W*delta > r exponent comparison failed')
        samples.append(dict(r=r,s=s,K_formula='2^114 * r^(320*s)',
             K_integral=True,K0_formula='2^58 * r^(176*s-1)',
             q_formula='2^59 * r^(176*s) + r',genuine_constants_evaluated=False))
    return dict(identities={name:list(map(int,actual)) for name,(actual,_) in identities.items()},
                symbolic_density_examples=samples,scalar_integer_checks=79,
                c_less_than_d_over_eight=dict(K_lower_bound=k_lower,
                    two_exponent_margin=two_margin,density_exponent_margin=density_margin,
                    analytic_input='pi < 4 and 0 < a <= 1'),
                huge_witness_evaluated=False)


def floor_checks():
    count=0
    for denominator in range(1,65):
        for numerator in range(2*denominator,12*denominator+1):
            x=F(numerator,denominator); floor=numerator//denominator
            require(x/2 <= floor <= x < floor+1,'positive floor bound failed')
            count+=1
    return dict(exact_rational_cases=count)


def predecessor_floor_checks():
    rational_cases=branches=positive=0
    for denominator in range(1,65):
        for numerator in range(12*denominator+1):
            x=F(numerator,denominator); m=numerator//denominator
            require(m <= x < m+1,'literal source floor inequalities failed')
            rational_cases += 1
            for predecessor in (0,1):
                if m < predecessor:
                    continue  # The source lengths are natural numbers.
                lp=m-predecessor
                require(lp > x-2,'floor/predecessor strict bound failed')
                branches += 1
                if x > 8:
                    require(lp > x-2 > x/2 > 4,'width-derived positivity failed')
                    positive += 1
    return dict(exact_rational_cases=rational_cases,length_branches=branches,
                positive_width_branches=positive,branches=['floor','predecessor'],
                conclusion='L_P > X - 2 in both natural-number branches')


def surrogate_width_only_checks():
    """Width-only implications at exact dyadic toy constants, not actual records."""
    rows=[]
    for u in (F(1,16),F(1,8)):
        for w in (F(1,4),F(1,2),F(3,4)):
            e=4096; beta=u*w/2; epsilon=F(1,2)
            d=F(1,256); c=F(1,65536); width=F(4)
            require(0 < c < d/8 < 1,'surrogate separation failed')
            require(0 < beta < u*w < u and 0 < w < 1,'surrogate uniform margins failed')
            def npower(exponent):
                power=e*exponent
                require(power.denominator == 1,'surrogate dyadic power not integral')
                return F(2)**int(power)
            # Width <= (c N^beta)^epsilon, squared since epsilon=1/2.
            require(width > 1 and width**2 <= c*npower(beta),'surrogate width failed')
            require(npower(beta) > 1/c,'width failed to force N^beta > 1/c')
            x=d*npower(u)
            require(x > d/c > 8,'width-only initial scale failed')
            for predecessor in (0,1):
                lp=x.numerator//x.denominator-predecessor
                require(lp > x-2 > x/2 > 4,'width-only floor positivity failed')
                # No irrational power evaluation: raise each side to denominator(w).
                cp=d/2; wp,wq=w.numerator,w.denominator
                require(cp**wp >= cp**wq,'small-base power comparison failed')
                require(npower(u*w) > npower(beta),'strict exponent margin failed')
                raised_lower=cp**wp*npower(u*wp)
                raised_width=(cp*npower(beta))**wq
                require(lp**wp > raised_lower > raised_width > (d/(2*c))**wq > 4**wq,
                        'width-only structural power chain failed')
                require(lp**wp > 4**wq,'width-only radius is not strictly below 1/4')
                require(d/(2*c) > 4,'width-only structural margin failed')
                rows.append(dict(u=str(u),w=str(w),beta=str(beta),log2N=e,
                    length_branch='predecessor' if predecessor else 'floor',
                    positive_initial_length=True,normalized_radius_strictly_below='1/4',
                    other_five_budgets_assumed=False))
    return dict(scope='Exact dyadic toy constants only; not genuine source records or witnesses',
                cases=rows,case_count=len(rows),width_only=True)


def surrogate_threshold_checks():
    """Exercise all eight implications at dyadic surrogate constants, NOT source constants."""
    results=[]
    # Chosen so all rational powers used below are exact integer powers of 2.
    for t in range(1,7):
        e=4096*(t+1); nmod=2**e
        u=F(1,32); v=F(1,8); w=F(1,4); sigma=u*v/2
        beta=sigma/2; epsilon=F(1,2)
        d=F(1,2**8); cp=d/2; a=F(1,2**4)
        c=F(1,2**4); z=F(1,2**8); width=F(2**2)
        p,s,k0=2,4,2
        def npower(r):
            exp=e*r
            require(exp.denominator==1,'surrogate N power not integral')
            return F(2)**int(exp)
        rhs=[p**(s+1),2/d,d/a,2/cp,2,(p*k0)**2,None,None]
        exp=[F(1),u,1-u,u-sigma,sigma,F(1),u*w-sigma,beta*epsilon]
        for i in range(6): require(npower(exp[i])>=rhs[i],'surrogate threshold failed')
        # T7 and T8 raised to positive powers to avoid irrational cp^-w or c^-epsilon.
        require(npower(4*exp[6]) >= cp**-1*z**-4,'surrogate T7 failed')
        require(npower(2*exp[7]) >= width**2*c**-1,'surrogate T8 failed')
        raw=d*npower(u); ell=raw.numerator//raw.denominator
        raw_n=npower(sigma); m=raw_n.numerator//raw_n.denominator
        require(2*npower(sigma)<=cp*npower(u)<=ell<=d*npower(u)<=a*nmod,
                'surrogate scale chain failed')
        require(0<m and m*m<=nmod and m+1<=ell,'surrogate first budgets failed')
        require(c*npower(beta)<=m,'surrogate lower-length budget failed')
        require(F(m)**4 <= z**4*ell,'surrogate fifth budget failed')
        require(width**2 <= c*npower(beta),'surrogate sixth budget failed')
        results.append(dict(log2N=e,ell_log2=int(e*u)-8,M_log2=int(e*sigma),
                            eight_thresholds=True,six_budgets=True))
    return dict(scope='Dyadic surrogate constants only; not genuine source witnesses',cases=results)


def composite_boundary():
    # Prime-power unit cancellation can fail when another prime divides N.
    p,n,slope,intercept=2,18,5,0
    agreements=[x for x in range(n) if (slope*x+intercept-x//p)%n==0]
    require(agreements == [0,4,8,12,16],'boundary model changed')
    require(gcd(p*slope-1,n)==9,'composite zero-divisor witness changed')
    return dict(N=n,p=p,slope=slope,intercept=intercept,agreements=agreements,
                role='Failure of unrestricted unit argument, not a full-budget example')


def outside_support_boundary():
    r,n,s,slope=2,80,4,3
    agreements=[x for x in range(n) if (slope*x-x//r)%n == 0]
    require(r**s >= 8*r and n % (r**s) == 0,'boundary lost strip divisibility')
    require(not set(prime_support(n)) <= set(prime_support(r)),
            'boundary unexpectedly has fixed prime support')
    require(agreements == [0,32,64],'outside-support agreements changed')
    require(gcd(r*slope-1,n) == 5,'outside-support multiplier changed')
    require(len(agreements) > r and {x%r for x in agreements} == {0},
            'boundary no longer defeats both affine caps')
    return dict(r=r,N=n,s=s,slope=slope,intercept=0,agreements=agreements,
                role='Failure of both affine caps without prime support; not a theorem counterexample')


def source_checks():
    raw=(ROOT/'provenance/source_manifest.json').read_bytes()
    require(len(raw)<100000,'oversized source manifest')
    manifest=json.loads(raw)
    require(set(manifest)=={'schema','scope','sources','unchanged_at_later_pins'},'manifest keys changed')
    require(manifest['schema']=='report283-curated-sources-v1','manifest schema mismatch')
    require(manifest['unchanged_at_later_pins']==[],'unrequested later pin')
    require(len(manifest['sources'])==5,'wrong source count')
    seen=set(); rows=[]
    for entry in manifest['sources']:
        require(set(entry)=={'file','repository_path','commit','bytes','sha256','git_blob','verified_url'},'source fields changed')
        name=entry['file'].removeprefix('sources/')
        require(name in SOURCE_HASHES and entry['file']=='sources/'+name,'unexpected source path')
        require(name not in seen,'duplicate source'); seen.add(name)
        path='Combinatorics/Ramsey/Lean/GowersSzemeredi/'+name
        require(entry['repository_path']==path and entry['commit']==COMMIT,'source pin changed')
        require(entry['verified_url']=='https://github.com/VladimirReshetnikov/ProveIt/blob/'+COMMIT+'/'+path,'source URL mismatch')
        data=(ROOT/'provenance/sources'/name).read_bytes()
        require(type(entry['bytes']) is int and entry['bytes']==len(data),'source length mismatch')
        require(sha256(data).hexdigest()==entry['sha256']==SOURCE_HASHES[name],'source SHA256 mismatch')
        require(sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==entry['git_blob'],'Git blob mismatch')
        rows.append(dict(file=name,bytes=len(data),sha256=entry['sha256']))
    require(seen==set(SOURCE_HASHES),'source inventory mismatch')
    require({p.name for p in (ROOT/'provenance/sources').iterdir()}==seen,'unlisted source')
    return dict(commit=COMMIT,verified_lean_snapshots=len(rows),bindings=rows,
                remote_origin_reverified=False,lean_compiled=False)


def run_checks():
    aff=[affine_histogram(p,k) for p,k,n in models()]
    mixed_aff=[fixed_support_affine(r,n) for r,n in mixed_models()]
    aliases=[alias_case(p,k,F(j,16*p+h)) for p,k,n in models() for j,h in ((1,1),(2,3),(3,7),(1,0))]
    mixed_aliases=[fixed_r_alias_case(r,n,F(j,16*r+h)) for r,n in mixed_models()
                   for j,h in ((1,1),(2,3),(3,7),(1,0))]
    strips=[strip_case(*args) for args in ((2,5,4),(2,6,4),(2,7,4),(3,4,3),(3,5,3),(5,4,3),(11,3,2),(13,3,2))]
    mixed_strips=[fixed_support_strip_case(*args) for args in
                  ((4,128,3),(4,256,3),(6,216,3),(6,432,3),(6,648,3),
                   (10,200,2),(10,400,2),(10,1000,2),(12,288,2),(12,432,2),
                   (15,1125,2),(15,675,2))]
    all_models=[(p,n) for p,k,n in models()]+list(mixed_models())
    subgroups=[subgroup_case(r,n) for r,n in all_models]
    annihilators=[annihilator_case(r,n,min(16,n//r)) for r,n in all_models]
    combined_aff=aff+mixed_aff
    return dict(report=283,status='passed',scope='Bounded exact diagnostics, not a formal or numerical verification of the huge theorem witnesses',
        affine=dict(models=combined_aff,model_count=len(combined_aff),
                    prime_power_model_count=len(aff),composite_r_model_count=len(mixed_aff),
                    point_tests=sum(x['point_tests'] for x in combined_aff),
                    affine_maps_covered=sum(x['affine_maps_covered'] for x in combined_aff)),
        carriers=carrier_checks(),aliases=dict(cases=aliases+mixed_aliases,
                    case_count=len(aliases)+len(mixed_aliases)),
        annihilators=dict(cases=annihilators,case_count=len(annihilators),
                          phase_tests=sum(x['phase_tests'] for x in annihilators)),
        subgroups=dict(cases=subgroups,case_count=len(subgroups),
                       steps_checked=sum(x['steps'] for x in subgroups),
                       full_period_carriers=sum(x['full_period_divisible_step_carriers'] for x in subgroups),
                       sharp_radius=sharp_radius_checks()),
        strips=strips+mixed_strips,symbolic=symbolic_checks(),floors=floor_checks(),
        predecessor_floors=predecessor_floor_checks(),
        surrogate_width_only=surrogate_width_only_checks(),
        surrogate_thresholds=surrogate_threshold_checks(),composite_boundary=composite_boundary(),
        outside_support_boundary=outside_support_boundary(),sources=source_checks())


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)
    print(json.dumps(run_checks(),indent=2,sort_keys=True))
    return 0


if __name__=='__main__':
    raise SystemExit(main())
