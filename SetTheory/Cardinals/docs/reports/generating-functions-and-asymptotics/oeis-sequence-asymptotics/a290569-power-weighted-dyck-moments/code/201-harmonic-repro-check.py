#!/usr/bin/env python3
"""Report201: exact finite reproduction and separately optional diagnostics.

Standard-library exact mode; optional mpmath numerical mode. All identities use
explicit exceptions, so python -O does not disable a check. No network access.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)  # Bounded exact data may exceed 4,300 digits.
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import comb, factorial, lcm
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def require(test, message):
    if not test:
        raise RuntimeError(message)


def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n', encoding='utf-8')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def integral(n, d):
    q, r = divmod(n, d)
    require(r == 0, 'Nonintegral purported integer weight')
    return q


LAWS = {
    'A000182': lambda h: h*(h+1),
    'A002105': lambda h: integral(h*(h+1), 2),
    'A326328': lambda h: h*(h+2),
    'A395382': lambda h: h*(h+3),
    'A395383': lambda h: h*(h+4),
    'A000698': lambda h: h+1,
    'A167872': lambda h: h+2,
    'A321963': lambda h: h+3,
    'A216966': lambda h: h**3,
    'A218221': lambda h: integral(h*(h+1)*(h+2), 6),
    'A227887': lambda h: h**4,
    'A144853': lambda h: integral(h*h*(4*h*h-1), 3),
    'A261000': lambda h: h*h*(4*h*h-1),
    'A144849': lambda h: integral(h*(h+1)*(2*h+1)**2, 3),
}


def walk_moments(weight, N):
    """Time/height DP, each upstep has weight 1, each descent h has weight w(h)."""
    weights = [0] + [weight(h) for h in range(1, N+1)]
    v = [1] + [0]*N
    out = [1]
    for step in range(1, 2*N+1):
        nxt = [0]*(N+1)
        for h in range(step % 2, min(step, 2*N-step, N)+1, 2):
            nxt[h] = (v[h-1] if h else 0)
            if h < N:
                nxt[h] += weights[h+1]*v[h+1]
        v = nxt
        if step % 2 == 0:
            out.append(v[0])
    return out


def first_return(weight, N):
    """Rooted first-return recursion, independent of time/height walks."""
    @lru_cache(None)
    def z(j, n):
        if n == 0:
            return 1
        return weight(j+1)*sum(z(j+1, k)*z(j, n-1-k) for k in range(n))
    return [z(0, n) for n in range(N+1)]


def multiply(a, b, N):
    c = [0]*(N+1)
    for i, x in enumerate(a[:N+1]):
        if x:
            for j, y in enumerate(b[:N+1-i]):
                if y:
                    c[i+j] += x*y
    return c


def reciprocal(a, N):
    require(a[0] == 1, 'Reciprocal requires constant coefficient 1')
    out = [1] + [0]*N
    for n in range(1, N+1):
        out[n] = -sum(a[j]*out[n-j] for j in range(1, min(n, len(a)-1)+1))
    return out


def sfraction(weight, N):
    """Nested formal-series reciprocal, depth N; no first-return call."""
    out = [1]+[0]*N
    for h in range(N, 0, -1):
        out = reciprocal([1]+[-weight(h)*x for x in out[:N]], N)
    return out


def free_cumulants(m):
    """Triangular exact inversion of M(t)=A(t M(t)^2).

    The even symmetric free cumulants are A[n], n>=1; A[0]=1 is a
    generating-function convention, not a zeroth free cumulant.
    """
    N = len(m)-1
    q = multiply(m, m, N)
    powers = [[1]+[0]*N]
    for k in range(1, N+1):
        powers.append(multiply(powers[-1], q, N-k))
    a = [1]
    for n in range(1, N+1):
        a.append(m[n]-sum(a[k]*powers[k][n-k] for k in range(1, n)))
    for n in range(1, N+1):
        require(m[n] == sum(a[k]*powers[k][n-k] for k in range(1, n+1)),
                f'Free-cumulant composition n={n}')
    return a


def implicit_quartic_cf(N):
    """Direct finite nested A-x/(A-16x/(...))=1, solved coefficientwise."""
    a = [1]+[0]*N
    for n in range(1, N+1):
        tail = a[:n+1]
        for h in range(n, 0, -1):
            inv = reciprocal(tail, n)
            tail = [a[0]]+[a[j]-h**4*inv[j-1] for j in range(1, n+1)]
        a[n] = -tail[n]
    return a


def occupation_first_return(weight, N):
    """Dual-number first-return recursion gives weighted occupation totals."""
    @lru_cache(None)
    def z(j, n):
        if n == 0:
            return F(1), (F(0),)*(N+2)
        total = F(0)
        occ = [F(0)]*(N+2)
        h = j+1
        for k in range(n):
            a, da = z(j+1, k)
            b, db = z(j, n-1-k)
            w = weight(h)
            total += w*a*b
            for r in range(1, N+1):
                occ[r] += w*(da[r]*b+a*db[r])
            occ[h] += w*a*b
        return total, tuple(occ)
    return [z(0, n) for n in range(N+1)]


def negative_excursion(weight, h, k):
    """Primitive negative excursion: first D, confined walk, final U."""
    v = [F(0)]*h
    v[h-1] = weight(h)
    for _ in range(2*k-2):
        nxt = [F(0)]*h
        for j, x in enumerate(v):
            if j+1 < h:
                nxt[j+1] += x
            if j:
                nxt[j-1] += x*weight(j)
        v = nxt
    return v[h-1]


def varied_laws():
    return {
        'gaussian': lambda h: F(h),
        'shifted_linear': lambda h: F(2*h-1, 2),
        'secant_noninteger': lambda h: F(h*(3*h+2), 3),
        'pure_quartic': lambda h: F(h**4),
        'quartic_shift': lambda h: F(h**3*(h+1)),
        'lemniscatic': lambda h: F(h*h*(4*h*h-1), 3),
        'negative_nonintegral_square': lambda h: F(h*h*(2*h-3)**2, 4),
        'distinct_negative_nonintegral': lambda h: F((5*h-6)*(5*h-9), 25),
        'complex_roots': lambda h: F(h*h+1),
        'irregular_period_three': lambda h: F(h*h*(2 if h%3 == 0 else 7), 3),
        'irregular_rational': lambda h: F((17*h*h+3*h+5)%29+1, (11*h+2)%7+1),
    }


def occupation_checks(N=9):
    counts = {'occupation_sums': 0, 'negative_excursion_identities': 0,
              'spectral_chord_inequalities': 0, 'first_return_walk_equalities': 0,
              'primitive_shift_identities': 0}
    for name, w in varied_laws().items():
        require(all(w(h)>0 for h in range(1, N+1)), f'Positive weights: {name}')
        data = occupation_first_return(w, N)
        walk = walk_moments(w, N)
        for n in range(N+1):
            require(data[n][0] == walk[n], f'Occupation base {name},{n}')
            counts['first_return_walk_equalities'] += 1
        below = {h: walk_moments(lambda j,h=h: w(j) if j<h else F(0), N)
                 for h in range(1, N+1)}
        for n in range(1, N+1):
            z, occ = data[n]
            require(sum(occ) == n*z, f'Occupation sum {name},{n}')
            counts['occupation_sums'] += 1
            for k in range(n+1):
                require(data[n-k][0]**n <= z**(n-k), f'Chord {name},{n},{k}')
                counts['spectral_chord_inequalities'] += 1
            for h in range(1, n+1):
                rhs = sum(negative_excursion(w,h,k)*(data[n-k][1][h]+data[n-k][1][h+1])
                          for k in range(1, n-h+1))
                require(occ[h]-z+below[h][n] == rhs, f'Excursion {name},{n},{h}')
                counts['negative_excursion_identities'] += 1
        shifted = walk_moments(lambda h: w(h+1), N-1)
        # Primitive paths: the coefficient of 1-1/M equals w(1)*shifted moments.
        inv = reciprocal(walk, N)
        for n in range(1, N+1):
            require(-inv[n] == w(1)*shifted[n-1], f'Primitive shift {name},{n}')
            counts['primitive_shift_identities'] += 1
    return {'max_n': N, 'laws': list(varied_laws()), 'checks': counts}


def enumerate_paths(n, weight):
    paths = []
    def visit(u, d, hs, mass):
        h = hs[-1]
        if d == n:
            paths.append((tuple(hs), mass))
            return
        if u < n:
            visit(u+1,d,hs+[h+1],mass)
        if h:
            visit(u,d+1,hs+[h-1],mass*weight(h))
    visit(0,0,[0],1)
    return paths


def dixon_weight(h):
    if h%2:
        j=(h+1)//2
        return (3*j-2)*(3*j-1)**2
    j=h//2
    return (3*j)**2*(3*j+1)


LAWS['A104133'] = dixon_weight


def conditional_pair_checks(N=7):
    checks = 0
    cases = {'UU':0,'DD':0,'UD_at_zero':0,'UD_or_DU':0}
    laws = {'cubic':lambda h:h**3, 'dixon':dixon_weight,
            'negative_square':lambda h:h*h*(2*h-3)**2,
            'irregular':lambda h:F((13*h+1)%11+1,(3*h)%5+1)}
    for name, weight in laws.items():
        for n in range(1,N+1):
            paths = enumerate_paths(n,weight)
            for cutoff in (1,2):
                def w(h):
                    return F(0) if h<=cutoff else min(F(1),F(h-cutoff,cutoff))/h
                for pair in range(n):
                    mid=2*pair+1
                    groups={}
                    for hs,mass in paths:
                        key=hs[:mid]+hs[mid+1:]
                        contribution=F(0)
                        for j in (mid,mid+1):
                            if hs[j]<hs[j-1]:
                                h=hs[j-1]
                                contribution += (-1)**h*w(h)
                        z,total=groups.get(key,(F(0),F(0)))
                        groups[key]=(z+mass,total+mass*contribution)
                    for key,(z,total) in groups.items():
                        k,end=key[mid-1],key[mid]
                        require(k%2==0,'Even-time parity')
                        if end==k+2:
                            expected=F(0); case='UU'
                        elif end==k-2:
                            expected=w(k)-w(k-1); case='DD'
                        elif k==0:
                            expected=-w(1); case='UD_at_zero'
                        else:
                            expected=(weight(k)*w(k)-weight(k+1)*w(k+1))/(weight(k)+weight(k+1))
                            case='UD_or_DU'
                        require(total/z==expected,f'Conditional pair {name},{n},{pair},{k}')
                        cases[case]+=1
                        checks+=1
    return {'max_n':N,'law_count':len(laws),'cutoffs':[1,2],'checks':checks,'cases':cases}


def dixon_checks(N=48):
    # Derivative coefficients (EGF), s'=c^2, c'=s^2, s(0)=0,c(0)=1.
    # This is the positive signed-Dixon normalization smh.
    degree=3*N+1
    s=[0]*(degree+1); c=[0]*(degree+1); c[0]=1
    for k in range(degree):
        s[k+1]=sum(comb(k,j)*c[j]*c[k-j] for j in range(k+1))
        c[k+1]=sum(comb(k,j)*s[j]*s[k-j] for j in range(k+1))
    z=walk_moments(dixon_weight,N)
    for n in range(N+1):
        require(z[n]==s[3*n+1],f'Dixon ODE n={n}')
    require(all(s[k]==0 for k in range(degree+1) if k%3!=1),'Dixon s sparsity')
    require(all(c[k]==0 for k in range(degree+1) if k%3!=0),'Dixon c sparsity')
    return {'max_n':N,'equalities':N+1,'ode_degree':degree,
            'weights':[dixon_weight(h) for h in range(1,13)],
            'moments':[str(x) for x in z]}, z


def secant_power(beta,N):
    """Ordinary Taylor coefficients from T'=1+T^2 and F'=beta*T*F."""
    t=[F(0)]*(2*N+1)
    a=[F(0)]*(2*N+1); a[0]=F(1)
    for k in range(2*N):
        t[k+1]=(F(k==0)+sum(t[j]*t[k-j] for j in range(k+1)))/(k+1)
        a[k+1]=beta*sum(t[j]*a[k-j] for j in range(k+1))/(k+1)
    return [a[2*n]*factorial(2*n) for n in range(N+1)]


def classical_checks(N=24):
    count=0
    for beta in map(F,['1/2','1','5/3','2','3','4','5']):
        z=walk_moments(lambda h:F(h)*(h+beta-1),N)
        golden=secant_power(beta,N)
        require(z==golden,f'Secant power beta={beta}')
        count+=N+1
    z=walk_moments(lambda h:h,N)
    for n in range(N+1):
        require(z[n]==factorial(2*n)//(2**n*factorial(n)),f'Gaussian n={n}')
        count+=1
    return {'max_n':N,'equalities':count,'secant_beta':['1/2','1','5/3','2','3','4','5']}


def half_integer_gamma(x):
    """Gamma(x)=rational*sqrt(pi)^e, e in {0,1}; exact recurrence."""
    x=F(x)
    if x.denominator==1:
        require(x>0,'Gamma integer pole')
        return F(factorial(x.numerator-1)),0
    require(x.denominator==2,'Half-integer Gamma expected')
    result=F(1)
    y=F(1,2)
    while y<x:
        result*=y; y+=1
    while y>x:
        y-=1; result/=y
    return result,1


def gamma_algebra_checks():
    results=[]
    expected=[('cubic_binomial',[0,1,2],F(2),0),
              ('quartic_lemniscatic',[0,0,F(-1,2),F(1,2)],F(1,2),2),
              ('quartic_square',[0,F(1,2),F(1,2),1],F(1,4),2),
              ('negative_square',[0,0,F(-3,2),F(-3,2)],F(4),2)]
    for name,cs,coefficient,exponent in expected:
        q=F(1); e=0
        for shift in cs:
            a,b=half_integer_gamma(1+shift);q*=a;e+=b
        require((q,e)==(coefficient,exponent),f'Gamma reduction {name}')
        results.append({'name':name,'gamma_product_rational':str(q),'sqrt_pi_power':e})
    finite=0
    for cs in ([F(0),F(1),F(2)],[F(0),F(0),F(-3,2),F(-3,2)],[F(-6,5),F(-9,5)]):
        for N in range(1,33):
            direct=F(1); rising=F(1)
            for h in range(1,N+1):
                q=F(1)
                for c in cs:q*=1+c/h
                direct*=q
            for c in cs:
                r=F(1)
                for j in range(N):r*=1+c+j
                rising*=r/F(factorial(N))
            require(direct==rising,'Finite gamma/rising-factorial identity')
            finite+=1
    dixon_products=0
    def rising(x,m):
        out=F(1)
        for j in range(m):out*=x+j
        return out
    for m in range(1,33):
        direct=F(1)
        for h in range(1,2*m+1):direct*=F(8*dixon_weight(h),27*h**3)
        rhs=rising(F(1,3),m)*rising(F(2,3),m)**2*rising(F(4,3),m)/(rising(F(1,2),m)**3*rising(F(1),m))
        require(direct==rhs,'Dixon finite Gamma product')
        dixon_products+=1
    complex_count=0
    for N in range(1,33):
        direct=F(1);real=F(1);imag=F(0)
        for h in range(1,N+1):
            direct*=F(h*h+1,h*h)
            real,imag=real*h-imag,imag*h+real
        require(direct==(real*real+imag*imag)/factorial(N)**2,'Complex conjugate finite product')
        complex_count+=1
    # Monomials are exponent vectors for [2,3,pi,Gamma(1/3)].
    r3=(F(2),F(1,2),F(1),F(-3))
    c3=tuple(F(3,2)*x+y for x,y in zip(r3,(F(-1,2),F(1,2),F(-1,2),F(0))))
    amplitude=tuple(c+3*r+s for c,r,s in zip(c3,r3,(F(-1),F(0),F(0),F(0))))
    require(amplitude==(F(15,2),F(11,4),F(4),F(-27,2)),'Cubic amplitude algebra')
    exponential=tuple(3*x+y for x,y in zip(r3,(F(-1),F(-1),F(0),F(0))))
    require(exponential==(F(5),F(1,2),F(3),F(-9)),'Cubic exponential algebra')
    return {'gamma_reductions':results,'finite_product_equalities':finite,
            'dixon_finite_product_equalities':dixon_products,'complex_conjugate_finite_product_equalities':complex_count,'cubic_monomial_equalities':2,
            'scope':'Exact algebra after the classical Gamma recurrence/reflection identities; no numerical Gamma values used.'}


def exact_suite(N,fixture):
    moments={name:walk_moments(w,N) for name,w in LAWS.items()}
    moments['A338634']=free_cumulants(moments['A227887'])
    source_rows=[]
    prefix_checks=0
    weight_checks=0
    for entry in fixture['entries']:
        name=entry['id']
        raw=[int(x) for x in entry['displayed_terms']]
        expected=raw[entry['source_initial_terms_skipped']:]
        if entry['source_sign_alternated']:
            expected=[(-1)**n*x for n,x in enumerate(expected)]
        if entry.get('kind')=='weight_sequence':
            require([LAWS['A144853'](h) for h in range(len(expected))]==expected,'OEIS A187756 weights')
            weight_checks+=len(expected)
        else:
            require(moments[name][:len(expected)]==expected,f'OEIS displayed terms: {name}')
            prefix_checks+=len(expected)
        source_rows.append({'id':name,'displayed_terms':len(raw),'validated_terms':len(expected),'kind':entry.get('kind','moment_sequence'),
                            'source_initial_terms_skipped':entry['source_initial_terms_skipped'],
                            'source_sign_alternated':entry['source_sign_alternated']})
    independent=0
    for name,w in LAWS.items():
        length=min(N,24)
        a=first_return(w,length);b=sfraction(w,length)
        require(a==b==moments[name][:length+1],f'Independent constructions: {name}')
        independent+=length+1
    a=implicit_quartic_cf(20)
    require(a==moments['A338634'][:21],'A338634 direct nested continued fraction')
    scaling=0
    for n in range(N+1):
        require(moments['A261000'][n]==3**n*moments['A144853'][n],f'Quartic scale n={n}')
        scaling+=1
    dixon,z=dixon_checks(48)
    result={'status':'PASS','max_n':N,'arithmetic':'Python integers and fractions.Fraction',
            'oeis_displayed_prefixes':source_rows,'oeis_moment_term_equalities':prefix_checks,'oeis_weight_term_equalities':weight_checks,
            'independent_first_return_s_fraction_walk_equalities':independent,
            'independent_prefix_max_n':24,'quartic_scaling_equalities':scaling,
            'free_cumulant_composition_equalities':N,'free_cumulant_implicit_cf_equalities':21,
            'occupation_and_excursions':occupation_checks(),
            'conditional_pairs':conditional_pair_checks(),
            'dixon':dixon,'classical':classical_checks(),'gamma_algebra':gamma_algebra_checks(),
            'scope':'Finite exact validation; it does not prove asymptotics, convergence rates, or novelty.'}
    return result,moments,z


def harmonic_statistics(weight,N):
    """Exact scalar-marked walks using lcm to avoid rational states."""
    L=lcm(*range(1,N+1))
    v=[1]+[0]*N;u=[0]*(N+1)
    weights=[0]+[weight(h) for h in range(1,N+1)]
    out={}
    for step in range(1,2*N+1):
        a=[0]*(N+1);b=[0]*(N+1)
        for h in range(step%2,min(step,2*N-step,N)+1,2):
            if h:
                a[h]+=v[h-1];b[h]+=u[h-1]
            if h<N:
                q=weights[h+1]
                a[h]+=q*v[h+1]
                b[h]+=q*(u[h+1]+(L//(h+1))*v[h+1])
        v,u=a,b
        if step%2==0:out[step//2]=F(u[0],L*v[0])
    return out


def bridge_profile(weight,n,times):
    """Exact bridge marginal; reverse path weight ratio is product w(1)..w(h)."""
    wanted=set(times)|{2*n-t for t in times}
    v=[1]+[0]*n;snap={0:v[:]}
    weights=[0]+[weight(h) for h in range(1,n+1)]
    product=[1]
    for w in weights[1:]:product.append(product[-1]*w)
    for step in range(1,2*n+1):
        a=[0]*(n+1)
        for h in range(step%2,min(step,2*n-step,n)+1,2):
            if h:a[h]+=v[h-1]
            if h<n:a[h]+=weights[h+1]*v[h+1]
        v=a
        if step in wanted:snap[step]=v[:]
    z=v[0];out={}
    for t in times:
        masses=[snap[t][h]*snap[2*n-t][h]*product[h] for h in range(n+1)]
        require(sum(masses)==z,f'Profile probability normalization {n},{t}')
        mean=F(sum(h*x for h,x in enumerate(masses)),z)
        second=F(sum(h*h*x for h,x in enumerate(masses)),z)
        out[t]=(mean,second-mean*mean)
    return out



def high_precision_marked_walk(mp,weights,N):
    """Rescaled noninteger-weight walk; returns log moments and harmonic means.

    This entire routine is numerical, including its input weights. Scaling is
    common to the partition and marked sums, so their quotient is preserved.
    """
    v=[mp.mpf(1)]+[mp.mpf(0)]*N
    u=[mp.mpf(0)]*(N+1);logscale=mp.mpf(0);out={}
    for step in range(1,2*N+1):
        a=[mp.mpf(0)]*(N+1);b=[mp.mpf(0)]*(N+1)
        for h in range(step%2,min(step,2*N-step,N)+1,2):
            if h:
                a[h]+=v[h-1];b[h]+=u[h-1]
            if h<N:
                q=weights[h+1]
                a[h]+=q*v[h+1]
                b[h]+=q*(u[h+1]+v[h+1]/(h+1))
        scale=max(a)
        v=[x/scale for x in a];u=[x/scale for x in b]
        logscale+=mp.log(scale)
        if step%2==0:out[step//2]=(logscale+mp.log(v[0]),u[0]/v[0])
    return out

def numerical_suite(N,moments,dixon_values,dps):
    try:
        import mpmath as mp
    except ImportError as exc:
        raise RuntimeError('--diagnostics requires mpmath; exact mode does not') from exc
    mp.mp.dps=dps
    def number(x):
        if isinstance(x,F):return mp.mpf(x.numerator)/x.denominator
        return mp.mpf(x)
    def fmt(x):return mp.nstr(x,30)
    samples=[n for n in (16,32,64,128,256,512) if n<=N]
    baselines={p:walk_moments(lambda h,p=p:h**p,N) for p in (1,2,3,4)}
    constants={p:2*p*mp.gamma(mp.mpf(2)/p)/mp.gamma(mp.mpf(1)/p)**2 for p in (1,2,3,4)}
    normalized=[]
    specs=[('A218221',3,F(1,6),3,mp.mpf(2)),
           ('A144853',4,F(4,3),0,mp.pi/2),
           ('A261000',4,F(4),0,mp.pi/2),
           ('A144849',4,F(4,3),2,mp.pi/4)]
    for name,p,kappa,a,gamma in specs:
        for n in samples:
            prediction=number(kappa)**n*(constants[p]*n)**a/gamma
            value=number(moments[name][n])/baselines[p][n]/prediction
            normalized.append({'id':name,'n':n,'ratio_over_relative_equivalent':fmt(value)})
    power_shifts=[]
    for p in (1,2,3,4):
        for alpha in (F(-1,2),F(1),F(2)):
            denominator=alpha.denominator
            w=lambda h,p=p,alpha=alpha: h**(p-1)*(alpha.denominator*h+alpha.numerator)
            zs=walk_moments(w,N)
            stat=harmonic_statistics(w,N)
            for n in samples:
                pred=(constants[p]*n)**number(alpha)/mp.gamma(1+number(alpha))
                ratio=number(zs[n])/denominator**n/baselines[p][n]/pred
                power_shifts.append({'p':str(p),'alpha':str(alpha),'n':n,
                    'ratio_over_relative_equivalent':fmt(ratio),
                    'harmonic_constant_error':fmt(number(stat[n])-mp.log(n)-mp.euler-mp.log(constants[p]))})
    p=mp.mpf('0.5');r=2*p*mp.gamma(2/p)/mp.gamma(1/p)**2
    base=high_precision_marked_walk(mp,[mp.mpf(0)]+[mp.mpf(h)**p for h in range(1,N+1)],N)
    for alpha in (mp.mpf('-0.5'),mp.mpf(1),mp.mpf(2)):
        shifted=high_precision_marked_walk(mp,[mp.mpf(0)]+[mp.mpf(h)**p*(1+alpha/h) for h in range(1,N+1)],N)
        for n in samples:
            ratio=mp.exp(shifted[n][0]-base[n][0]-alpha*mp.log(r*n)+mp.loggamma(1+alpha))
            power_shifts.append({'p':'0.5','alpha':str(alpha),'n':n,
                'ratio_over_relative_equivalent':fmt(ratio),
                'harmonic_constant_error':fmt(shifted[n][1]-mp.log(n)-mp.euler-mp.log(r))})
    absolute=[]
    for p in (1,2,3,4):
        r=constants[p];C=mp.sqrt(p*r**p/(2*mp.pi))
        for n in samples:
            pred=C*r**(p*n)*mp.factorial(n)**p/mp.sqrt(n)
            absolute.append({'p':p,'n':n,'ratio_over_posted_general_power_formula':fmt(number(baselines[p][n])/pred)})
    harmonic=[];profiles=[]
    for p in (1,2,3,4):
        stat=harmonic_statistics(lambda h,p=p:h**p,N)
        K=mp.log(constants[p]);I=mp.beta(mp.mpf(1)/p,mp.mpf(1)/2)/p;H=1/I
        for n in samples:
            harmonic.append({'p':p,'n':n,'E_sum_Nh_over_h_minus_log_n_gamma_K':fmt(number(stat[n])-mp.log(n)-mp.euler-K)})
        for n in [x for x in (32,64,128,256) if x<=N]:
            data=bridge_profile(lambda h,p=p:h**p,n,[n//2,n,3*n//2])
            for t,(mean,var) in data.items():
                s=mp.mpf(t)/n
                goal=min(s,2-s)
                lo=mp.mpf(0);hi=mp.mpf(1)
                for _ in range(220):
                    u=(lo+hi)/2
                    time=H*mp.betainc(mp.mpf(1)/p,mp.mpf(1)/2,0,u**p)/p
                    if time<goal:lo=u
                    else:hi=u
                predicted=H*(lo+hi)/2
                profiles.append({'p':p,'n':n,'time_over_n':fmt(s),'mean_height_over_n':fmt(number(mean)/n),
                                 'limit_arch':fmt(predicted),'mean_minus_arch':fmt(number(mean)/n-predicted),
                                 'height_sd_over_n':fmt(mp.sqrt(number(var))/n)})
    special=[]
    examples=[('complex_roots',2,lambda h:h*h+1,F(1),[mp.j,-mp.j]),
              ('negative_nonintegral_pair',2,lambda h:(5*h-6)*(5*h-9),F(25),[mp.mpf('-1.2'),mp.mpf('-1.8')]),
              ('negative_nonintegral_square',4,lambda h:h*h*(2*h-3)**2,F(4),[mp.mpf(0),mp.mpf(0),mp.mpf('-1.5'),mp.mpf('-1.5')])]
    products=[]
    for name,p,w,denom,cs in examples:
        zs=walk_moments(w,N);a=sum(cs);P=1/mp.fprod(mp.gamma(1+c) for c in cs)
        require(abs(mp.im(P))<mp.mpf(10)**(-dps+10) and mp.re(P)>0,'Positive real reciprocal Gamma product')
        P=mp.re(P)
        for n in samples:
            ratio=number(zs[n])/number(denom)**n/baselines[p][n]/((constants[p]*n)**a*P)
            special.append({'law':name,'n':n,'ratio_over_relative_equivalent':fmt(mp.re(ratio)),'reciprocal_gamma_product':fmt(P)})
        prod=mp.mpf(1)
        for h in range(1,4097):
            prod*=number(w(h))/number(denom)/mp.mpf(h)**p
            if h in (16,64,256,1024,4096):
                products.append({'law':name,'N':h,'finite_product_over_N_power_gamma_limit':fmt(mp.re(prod/mp.mpf(h)**a/P))})
    rho=mp.beta(mp.mpf(1)/3,mp.mpf(1)/3)/3
    I3=mp.beta(mp.mpf(1)/3,mp.mpf(1)/2)/3
    P=9/(4*mp.sqrt(2*mp.pi))
    identities={'rho_over_2_one_third_I3':fmt(rho/(2**(mp.mpf(1)/3)*I3)),
                'r4_over_8_sqrt_pi_gamma_quarter_squared':fmt(constants[4]/(8*mp.sqrt(mp.pi)/mp.gamma(mp.mpf(1)/4)**2)),
                'Gamma_1_plus_i_product_over_pi_csch_pi':fmt(mp.re(mp.gamma(1+mp.j)*mp.gamma(1-mp.j)/(mp.pi/mp.sinh(mp.pi)))),
                'A218221_amplitude_quotient':fmt((mp.sqrt(3*constants[3]**3/(2*mp.pi))*constants[3]**3/2)/(2**mp.mpf('7.5')*3**mp.mpf('2.75')*mp.pi**4/mp.gamma(mp.mpf(1)/3)**mp.mpf('13.5')))}
    poles=[{'n':n,'ratio_over_three_pole_equivalent':fmt(number(dixon_values[n])/(3*mp.factorial(3*n+1)/rho**(3*n+2)))} for n in (1,2,4,8,16,32,48)]
    dprod=mp.mpf(1);dproducts=[]
    for h in range(1,4097):
        dprod*=mp.mpf(dixon_weight(h))/(mp.mpf(27)/8*h**3)
        if h in (16,64,256,1024,4096):dproducts.append({'N':h,'finite_product_over_sqrt_N_limit':fmt(dprod/mp.sqrt(h)/P)})
    inverse=[]
    # Thresholds are exact integers; locate crossings by direct comparison.
    # xi and the interpolation x_Y are diagnostics, not certified rounding rules.
    for name,p,kappa,a,gamma in [('A216966',3,F(1),0,mp.mpf(1)),('A218221',3,F(1,6),3,mp.mpf(2)),('A227887',4,F(1),0,mp.mpf(1)),('A144849',4,F(4,3),2,mp.pi/4)]:
        seq=moments[name];r=constants[p];R=r*number(kappa)**(mp.mpf(1)/p)
        C=mp.sqrt(p*r**p/(2*mp.pi))*r**a/gamma
        b=mp.mpf(a)+mp.mpf(p-1)/2;clog=mp.log(C*(2*mp.pi)**(mp.mpf(p)/2))
        for n in [x for x in (16,32,64,128) if x+1<=N]:
            for label,Y in [('equal',seq[n]),('above',seq[n]+1),('midpoint',(seq[n]+seq[n+1])//2)]:
                crossing=next(i for i,z in enumerate(seq) if z>=Y)
                L=mp.log(Y);t=L/(p*mp.lambertw(R*L/(p*mp.e)))
                xi=t-(b*mp.log(t)+clog)/(p*mp.log(R*t))
                if Y==seq[crossing]:xY=mp.mpf(crossing)
                else:
                    i=crossing-1
                    xY=i+(L-mp.log(seq[i]))/(mp.log(seq[i+1])-mp.log(seq[i]))
                inverse.append({'id':name,'base_index':n,'threshold_type':label,'threshold_integer':str(Y),
                                'exact_first_inclusive_crossing':crossing,'xi':fmt(xi),
                                'xY_minus_xi':fmt(xY-xi),'log_t_times_error':fmt(mp.log(t)*(xY-xi)),
                                'ceil_xi':int(mp.ceil(xi)),
                                'note':'The exact integer crossing is certified by finite comparisons. Numerical xY may round to an integer at very close thresholds.'})
    cumulants=[{'n':n,'A338634_over_A227887':fmt(number(moments['A338634'][n])/moments['A227887'][n])} for n in samples]
    return {'status':'DIAGNOSTICS_ONLY','precision_decimal_digits':dps,'displayed_significant_digits':30,
            'scope':'High-precision evaluations, not interval certificates or asymptotic proofs; no computable little-o inverse radius is asserted.',
            'relative_amplitudes':normalized,'general_power_shift_diagnostics':power_shifts,'absolute_baselines':absolute,'harmonic_statistics':harmonic,
            'profiles':profiles,'complex_and_negative_shift_examples':special,'gamma_product_limits':products,
            'special_function_identity_diagnostics':identities,'dixon_three_pole_diagnostics':poles,
            'dixon_product_diagnostics':dproducts,'inverse_diagnostics':inverse,'free_cumulant_ratios':cumulants,
            'absolute_baseline_attribution':'General-p formula posted by Vaclav Kotesovec in OEIS A216966, September 24, 2020. The article derives the absolute formula for every fixed p>0 using the published Freud leading-coefficient theorem and endpoint occupation. The separate Freud companion covers that comparison; these finite ratios are not its proof.'}


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=256,help='Moment depth, default 256 (48..512)')
    parser.add_argument('--out',type=Path,default=HERE/'generated',help='Output directory')
    parser.add_argument('--diagnostics',action='store_true',help='Add optional mpmath diagnostics')
    parser.add_argument('--dps',type=int,default=65,help='mpmath precision (>=45)')
    args=parser.parse_args()
    require(48<=args.max_n<=512,'--max-n must be in 48..512')
    require(args.dps>=45,'--dps must be at least 45')
    args.out.mkdir(parents=True,exist_ok=True)
    fixture_path=HERE/'data'/'oeis_displayed_terms.json'
    fixture=json.loads(fixture_path.read_text(encoding='utf-8'))
    result,moments,dixon=exact_suite(args.max_n,fixture)
    result['fixture_sha256']=digest(fixture_path)
    write_json(args.out/'exact_checks.json',result)
    write_json(args.out/'moments.json',{'max_n':args.max_n,'indexing':'Every array starts at n=0. Values are exact decimal strings. A338634 is the even free-cumulant transform; remaining arrays are normalized Dyck moments, with source offset/sign maps in exact_checks.json.',
                                      'sequences':{k:[str(x) for x in v] for k,v in moments.items()}})
    names=['exact_checks.json','moments.json']
    if args.diagnostics:
        write_json(args.out/'numerical_diagnostics.json',numerical_suite(args.max_n,moments,dixon,args.dps))
        names.append('numerical_diagnostics.json')
    manifest={'format':1,'max_n':args.max_n,'files':{name:digest(args.out/name) for name in names}}
    write_json(args.out/'manifest.json',manifest)
    print(json.dumps({'status':'PASS','max_n':args.max_n,'oeis_moment_term_equalities':result['oeis_moment_term_equalities'],
                      'conditional_pair_equalities':result['conditional_pairs']['checks'],
                      'dixon_ode_equalities':result['dixon']['equalities'],
                      'files':manifest['files']},sort_keys=True))


if __name__=='__main__':
    main()
