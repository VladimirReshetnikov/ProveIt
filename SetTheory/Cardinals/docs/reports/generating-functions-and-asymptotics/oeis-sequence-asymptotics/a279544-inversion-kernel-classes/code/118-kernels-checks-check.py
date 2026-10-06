#!/usr/bin/env python3
"""Independent exact finite checks for report118. Python >=3.10; stdlib only.
Analytic convergence and transfer are proved in the report, not by finite tests.
All substantive guards are explicit exceptions and survive python -O.
"""
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb, isqrt
from pathlib import Path
import argparse
import json
import re
import sys
sys.dont_write_bytecode = True
if __name__ == '__main__':
    sys.modules['check'] = sys.modules[__name__]
ROOT = Path(__file__).resolve().parent
MAX_BYTES = 262144
MAX_FILES = 32

class CheckFailure(Exception):
    def __init__(self, name, detail=''):
        self.name, self.detail = name, str(detail)
        super().__init__(name + ': ' + str(detail))

def need(test, name, detail=''):
    if not test:
        raise CheckFailure(name, detail)

def exact_json(path, name):
    def pairs(items):
        out = {}
        for key, value in items:
            need(key not in out, name, 'duplicate key ' + key)
            out[key] = value
        return out
    def integer(s):
        need(len(s) <= 100, name, 'integer exceeds 100 characters')
        return int(s)
    def reject(s):
        raise CheckFailure(name, 'noninteger JSON number: ' + s)
    try:
        need(path.is_file() and not path.is_symlink(), name, 'not an ordinary file')
        need(path.stat().st_size <= MAX_BYTES, name, 'file too large')
        return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=pairs,
                          parse_int=integer, parse_float=reject, parse_constant=reject)
    except (OSError, ValueError, UnicodeError) as error:
        raise CheckFailure(name, error) from None

def keys(value, names, diagnostic):
    need(type(value) is dict and set(value) == set(names), diagnostic)

def inventory(root):
    files = {}
    need(root.is_dir() and not root.is_symlink(), 'INTEGRITY_ROOT')
    entries = list(root.rglob('*'))
    need(len(entries) <= 64, 'INTEGRITY_COUNT')
    for path in sorted(entries):
        name = path.relative_to(root).as_posix()
        need(not path.is_symlink(), 'INTEGRITY_SYMLINK', name)
        need(path.is_dir() or path.is_file(), 'INTEGRITY_SPECIAL_FILE', name)
        if path.is_file():
            need(path.stat().st_size <= MAX_BYTES, 'INTEGRITY_SIZE', name)
            files[name] = sha256(path.read_bytes()).hexdigest()
    need(len(files) <= MAX_FILES, 'INTEGRITY_COUNT')
    return files

def integrity(root):
    actual = inventory(root)
    need('MANIFEST.json' in actual, 'INTEGRITY_MISSING', 'MANIFEST.json')
    manifest = exact_json(root/'MANIFEST.json', 'INTEGRITY_MANIFEST')
    keys(manifest, ['format', 'files'], 'INTEGRITY_MANIFEST')
    need(type(manifest['format']) is int and manifest['format'] == 1, 'INTEGRITY_MANIFEST')
    need(type(manifest['files']) is dict and 0 < len(manifest['files']) <= MAX_FILES,
         'INTEGRITY_MANIFEST')
    expected = manifest['files']
    for name, digest in expected.items():
        need(type(name) is str and re.fullmatch(r'[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*', name)
             and all(part not in ('.','..') for part in name.split('/')) and name != 'MANIFEST.json'
             and type(digest) is str and re.fullmatch(r'[0-9a-f]{64}', digest), 'INTEGRITY_MANIFEST')
        need(name in actual, 'INTEGRITY_MISSING', name)
        need(actual[name] == digest, 'INTEGRITY_HASH', name)
    actual.pop('MANIFEST.json')
    need(set(actual) == set(expected), 'INTEGRITY_UNLISTED', sorted(set(actual)-set(expected)))
    return len(actual)

RANGES = {'coefficient_n_max':80, 'external_prefix_n_max':28, 'brute_n_max':8,
          'derivative_M':96, 'jet_M':64, 'jet_degree':5, 'atan5_terms':100,
          'atan239_terms':32, 'sqrt_places':80, 'C_places':52, 'correction_places':24}
PROVENANCE = {'sequence':'A279544', 'class':214, 'offset':0,
 'oeis_url':'https://oeis.org/A279544',
 'paper_url':'https://arxiv.org/html/2512.21943v3',
 'paper_sections':'3.5 equations (3.31)-(3.33); 4.2 equation (4.8)',
 'retrieved_date':'2026-10-02',
 'prefix_scope':'29 displayed OEIS terms n=0..28; n=29..80 are internal cross-checks',
 'prior_values_sha256':'65d776f6aafa617370a3625b2ca3ab097f75f9c61fa1f88f5addc2005161ebdf'}
TAILS = {'derivative_numerator':16929, 'derivative_denominator':3072,
         'circle_radius':'1/10', 'circle_R':'101/400', 'circle_X':'11/9',
         'H_tail_constant':200000}
LIMITATIONS = [
 'Finite coefficient agreement does not prove the generating-tree interpretation or analytic convergence.',
 'The report proves the normal convergence, slit continuation, unique dominant singularity, and transfer hypotheses.',
 'Exact rational enclosures use the derivative and complex-circle tail inequalities proved in the report.',
 'Inverse error constants and starting thresholds are existential; no executable certified large-target inverse is supplied.',
 'No complete exponentially improved transseries, non-D-finiteness proof, or literature-priority claim is made.'
]

def rational(value, diagnostic):
    need(type(value) is str and len(value) <= 1024 and
         re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', value), diagnostic)
    result = F(value)
    need(str(result) == value, diagnostic, 'not canonical')
    return result

def decimal(value, places, diagnostic):
    need(type(value) is str and len(value) < 128 and
         re.fullmatch(r'-?(?:0|[1-9][0-9]*)\.[0-9]{'+str(places)+'}', value), diagnostic)
    return F(value)

def interval(value, places, diagnostic):
    keys(value, ['lower','upper'], diagnostic)
    lo, hi = (decimal(value[k], places, diagnostic) for k in ('lower','upper'))
    need(lo < hi, diagnostic)
    return lo, hi

def fixture(path):
    f = exact_json(path, 'FIXTURE_JSON')
    keys(f, ['schema_version','provenance','ranges','sequences','tails','enclosures','gamma','companion','limitations'], 'FIXTURE_SCHEMA')
    need(type(f['schema_version']) is int and f['schema_version'] == 1, 'FIXTURE_VERSION')
    for key, expected, code in [('provenance',PROVENANCE,'PROVENANCE'),('ranges',RANGES,'RANGE'),('tails',TAILS,'TAIL')]:
        keys(f[key], expected, code+'_SCHEMA')
        for name, value in expected.items():
            need(type(f[key][name]) is type(value) and f[key][name] == value, code+'_'+name.upper())
    keys(f['sequences'], ['external_prefix','internal_terms'], 'SEQUENCE_SCHEMA')
    for key, length in [('external_prefix',29),('internal_terms',81)]:
        seq = f['sequences'][key]
        need(type(seq) is list and len(seq) == length, 'SEQUENCE_LENGTH', key)
        need(all(type(x) is int and 0 < x < 10**60 for x in seq), 'SEQUENCE_INTEGER', key)
    keys(f['enclosures'], ['C','h','c1','c2'], 'ENCLOSURE_SCHEMA')
    interval(f['enclosures']['C'],52,'ENCLOSURE_VALUE')
    for key in ['c1','c2']:
        interval(f['enclosures'][key],24,'ENCLOSURE_VALUE')
    need(type(f['enclosures']['h']) is list and len(f['enclosures']['h']) == 6, 'ENCLOSURE_LENGTH')
    for item in f['enclosures']['h']:
        interval(item,24,'ENCLOSURE_VALUE')
    keys(f['gamma'], ['g_half','g_three_halves','gamma_ratios'], 'GAMMA_SCHEMA')
    for key, length in [('g_half',3),('g_three_halves',2),('gamma_ratios',3)]:
        need(type(f['gamma'][key]) is list and len(f['gamma'][key]) == length, 'GAMMA_LENGTH')
        for value in f['gamma'][key]:
            rational(value,'GAMMA_VALUE')
    import companion
    companion.validate_fixture(f['companion'])
    need(f['limitations'] == LIMITATIONS, 'LIMITATIONS')
    return f

# Dense, explicitly truncated power series. Operations never use floating point.
def add(a,b): return [x+y for x,y in zip(a,b)]
def scale(a,c): return [x*c for x in a]
def mul(a,b):
    n = len(a)
    out = [0]*n
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:n-i]):
                if y: out[i+j] += x*y
    return out

def inv(a):
    need(a[0] != 0, 'SERIES_INVERSE_ZERO')
    out = [F(1)/a[0]]
    for k in range(1,len(a)):
        out.append(-sum(a[j]*out[k-j] for j in range(1,k+1))/a[0])
    return out

def div(a,b): return mul(a,inv(b))
def monomial(n,k=0,c=1):
    out=[0]*n; out[k]=c; return out

def shift(a,k=1):
    return ([0]*k+a)[:len(a)] if k>=0 else a[-k:]+[0]*(-k)

def series_power(a,n):
    out=monomial(len(a))
    for _ in range(n): out=mul(out,a)
    return out

# Sparse Laurent polynomials provide independent exact symbolic identities.
def padd(*items):
    out=defaultdict(F)
    for item in items:
        for k,v in item.items(): out[k]+=v
    return {k:v for k,v in out.items() if v}

def pmul(a,b):
    out=defaultdict(F)
    for p,x in a.items():
        for q,y in b.items(): out[tuple(i+j for i,j in zip(p,q))]+=x*y
    return {k:v for k,v in out.items() if v}

def ps(a,c): return {k:v*c for k,v in a.items() if v*c}
def pp(a,n):
    out={tuple(0 for _ in next(iter(a))):F(1)}
    for _ in range(n): out=pmul(out,a)
    return out

def symbolic_checks():
    z={(1,0):F(1)}; x={(0,1):F(1)}; one={(0,0):F(1)}
    d=padd(one,ps(pmul(z,x),-1))
    P=padd(pmul(z,pp(x,2)),pmul(padd(ps(z,2),ps(one,-1)),x),z)
    Qnum=pmul(padd(one,pmul(padd(one,ps(z,-1)),x)),padd(one,ps(z,-1),ps(pmul(z,x),-1)))
    ynum=pmul(z,x)
    need(not padd(ynum,ps(pmul(z,pmul(x,d)),-1),ps(pmul(z,pmul(x,ynum)),-1)), 'KERNEL_SUBSTITUTION')
    need(not padd(pmul(z,padd(ynum,ps(pmul(x,ynum),2),ps(pmul(pp(x,2),d),-1))),ps(pmul(pmul(x,z),P),-1)), 'FUNCTIONAL_P')
    need(not padd(pmul(padd(ynum,pmul(z,d)),padd(ynum,ps(pmul(x,d),-1))),pmul(pmul(x,z),Qnum)), 'FUNCTIONAL_Q')
    b=pmul(x,padd(one,ps(z,-1),ps(pmul(z,x),-1)))
    need(not padd(pmul(ynum,b),ps(pmul(padd(P,ps(one,-1)),d),-1),ps(Qnum,-1)), 'FUNCTIONAL_G')
    # a=(1-zx)P/z expanded independently.
    zi={(-1,0):F(1)}
    a=pmul(pmul(d,P),zi)
    expanded=padd(one,pmul(padd(ps(one,2),ps(z,-1),ps(zi,-1)),x),pmul(padd(ps(one,2),ps(z,-2)),pp(x,2)),ps(pmul(z,pp(x,3)),-1))
    need(a==expanded,'FUNCTIONAL_A_EXPANSION')
    # The inverse coefficient equations are identities in L,beta,d1,d2,d3.
    def m(coef,*powers): return {powers:F(coef)}
    L=m(1,1,0,0,0,0); beta=m(1,0,1,0,0,0)
    d1=m(1,0,0,1,0,0); d2=m(1,0,0,0,1,0); d3=m(1,0,0,0,0,1)
    e1=m(-1,-1,0,1,0,0)
    e2=padd(m(-1,-2,1,1,0,0),m(-1,-1,0,0,1,0))
    e3=padd(m(-1,-3,2,1,0,0),m(-1,-2,1,0,1,0),m(-1,-2,0,2,0,0),m(-1,-1,0,0,0,1))
    for j,residual in enumerate([padd(pmul(L,e1),d1),padd(pmul(L,e2),ps(pmul(beta,e1),-1),d2),padd(pmul(L,e3),ps(pmul(beta,e2),-1),ps(pmul(d1,e1),-1),d3)],1):
        need(not residual,'INVERSE_E'+str(j))
    return {'kernel_and_F_to_G':'exact cleared polynomial identities','inverse_e1_e2_e3':'exact Laurent-polynomial residuals zero'}

def state_terms(N):
    states={(0,0):1}; terms=[]; f1=[]
    for n in range(N+2):
        terms.append(sum(count for (p,s),count in states.items() if s==0 and p<=2))
        f1.append(states.get((1,0),0))
        nxt=defaultdict(int)
        for (p,s),count in states.items():
            children=[(p+1,s)]
            if s: children.append((p+1,s-1))
            else:
                children.extend((k,p-k) for k in range(1,p+1))
                children.extend((k,p-1-k) for k in range(1,p))
            for label in children: nxt[label]+=count
        states=nxt
    need(f1[1:] == terms[:-1], 'TARGET_F1_NORMALIZATION')
    return terms[:N+1]

def orbit_terms(N):
    D=N+4; one=monomial(D); z=monomial(D,1)
    # Small root is Catalan(z)-1, reconstructed from r=z(1+r)^2.
    r=[0]*D
    for n in range(1,D):
        r[n]=(2*r[n-1] + (1 if n==1 else 0) + sum(r[i]*r[n-1-i] for i in range(n)))
    need(r==[0]+[comb(2*n,n)//(n+1) for n in range(1,D)], 'SMALL_ROOT_CATALAN')
    need(add(add(shift(mul(r,r)),mul(add(scale(z,2),scale(one,-1)),r)),z)==[0]*(D-1)+[0], 'SMALL_ROOT_POLYNOMIAL')
    x=r
    b=lambda u:mul(u,add(add(one,scale(z,-1)),scale(shift(u),-1)))
    q=b(x)
    for j in range(1,N+2):
        # Closed Mobius orbit, not the iterative substitution used in the draft.
        geometric=[1 if k<j else 0 for k in range(D)]
        denominator=add(one,scale(shift(mul(r,geometric)),-1))
        x=div(shift(r,j),denominator)
        need(all(v==0 for v in x[:j+1]),'ORBIT_VALUATION',j)
        a=add(one,add(add(add(scale(x,2),scale(shift(x),-1)),scale(shift(x,-1),-1)),add(scale(mul(x,x),2),add(scale(shift(mul(x,x)),-2),scale(shift(mul(mul(x,x),x)),-1)))))
        q=add(mul(a,q),b(x))
    need(all(v.denominator==1 if isinstance(v,F) else True for v in q), 'ORBIT_INTEGRAL')
    return [int(x) for x in q[1:N+2]]

def brute_terms(N):
    out=[]
    for n in range(N+1):
        count=0
        for seq in product(*(range(i) for i in range(1,n+1))):
            # A forbidden triple exists iff two earlier values are >= the current one.
            if all(sum(v>=seq[k] for v in seq[:k])<2 for k in range(n)):
                count+=1
        out.append(count)
    return out

def enumeration(f):
    terms=state_terms(80)
    need(terms==f['sequences']['internal_terms'],'INTERNAL_TERMS')
    need(terms[:29]==f['sequences']['external_prefix'],'EXTERNAL_PREFIX')
    orbit=orbit_terms(80)
    need(orbit==terms,'ORBIT_STATE_AGREEMENT')
    brute=brute_terms(8)
    need(brute==terms[:9],'BRUTE_STATE_AGREEMENT')
    need(all(terms[n+1]>terms[n] for n in range(1,80)),'FINITE_MONOTONICITY')
    targets=sorted({x for v in terms for x in (v-1,v,v+1) if 0<x<=terms[-1]})
    for Y in targets:
        n=next(i for i,a in enumerate(terms) if a>=Y)
        need(terms[n]>=Y and (n==0 or terms[n-1]<Y),'FINITE_THRESHOLD_EQUALITY')
    return {'internal_n_range':[0,80],'internal_coefficients':81,'external_prefix_n_range':[0,28],
            'external_terms':29,'brute_n_range':[0,8],'finite_threshold_boundary_cases':len(targets),
            'terms_sha256':sha256(json.dumps(terms,separators=(',',':')).encode()).hexdigest()}

def derivative(M):
    q=F(1,2); v=F(1,4)
    for j in range(1,M+1):
        p=4**j; u=F(3,2*p+1); du=F(9*p,(2*p+1)**2)
        # Independent expanded polynomial and its differentiated polynomial.
        a=1-F(9,4)*u+F(3,2)*u*u-u**3/4
        ap=-F(9,4)+3*u-F(3,4)*u*u
        b=F(3,4)*u-u*u/4; bp=F(3,4)-u/2
        q,v=a*q+b,a*v+du*(ap*q+bp)
    return q,v

def atan_interval(k,n):
    lo=F(); hi=F()
    # Positive pairs bound arctan from below; the next positive term bounds above.
    need(n%2==0,'ATAN_EVEN_TERMS')
    for j in range(0,n,2):
        lo+=F(1,(2*j+1)*k**(2*j+1))-F(1,(2*j+3)*k**(2*j+3))
    hi=lo+F(1,(2*n+1)*k**(2*n+1))
    return lo,hi

def decimal_outward(x,places,up=False):
    S=10**places
    n= -((-x.numerator*S)//x.denominator) if up else (x.numerator*S)//x.denominator
    sign='-' if n<0 else ''; n=abs(n)
    return sign+str(n//S)+'.'+str(n%S).zfill(places)

def displayed_interval(value,places):
    return {'lower':decimal_outward(value[0],places),'upper':decimal_outward(value[1],places,True)}

def leading(f):
    # Verify every constant in the report's conservative derivative-tail arithmetic.
    Q=F(9,8); V=F(1,4)+(F(9,4)*Q+F(3,4))*F(3,4)
    need(V==F(347,128),'DERIVATIVE_V_BOUND')
    step=V*F(9,4)*F(3,2)+(F(9,4)*Q+F(3,4))*F(9,4)
    need(step==F(16929,1024) and step/3==F(16929,3072),'DERIVATIVE_TAIL_ARITHMETIC')
    _,v8=derivative(8); need(v8-F(16929,3072*4**8)>0,'DERIVATIVE_POSITIVE')
    _,v=derivative(96); E=F(16929,3072*4**96); vI=(v-E,v+E)
    a=atan_interval(5,100); b=atan_interval(239,32)
    piI=(16*a[0]-4*b[1],16*a[1]-4*b[0])
    # Machin angle: tan(4 atan(1/5)-atan(1/239))=1, with angle in (0,pi/2).
    t=F(1,5); t2=2*t/(1-t*t); t4=2*t2/(1-t2*t2)
    need((t4-F(1,239))/(1+t4/F(239))==1,'MACHIN_TANGENT_IDENTITY')
    need(0<4*(F(1,5)-F(1,375))-F(1,239)<4*F(1,5)<F(3,2),'MACHIN_ANGLE_RANGE')
    S=10**80
    lower=isqrt(piI[0].numerator*S*S//piI[0].denominator)
    upper=isqrt(piI[1].numerator*S*S//piI[1].denominator)+1
    sqrtI=(F(lower,S),F(upper,S))
    need(0<sqrtI[0]**2<=piI[0]<piI[1]<sqrtI[1]**2,'PI_SQRT_ENCLOSURE')
    C=(4*vI[0]/sqrtI[1],4*vI[1]/sqrtI[0])
    need(0<C[0]<C[1] and C[1]-C[0]<F(1,10**56),'C_RATIONAL_WIDTH')
    need(displayed_interval(C,52)==f['enclosures']['C'],'C_ENCLOSURE')
    return {'derivative_M':96,'derivative_positive_at_M':8,'pi_terms':[100,32],
            'sqrt_places':80,'C':displayed_interval(C,52),'pre_display_width_bound':'1/10^56'}

def local_jet(M,D):
    size=D+1; one=monomial(size); z=monomial(size,0,F(1,4));z[2]=F(-1,4)
    numer=monomial(size);numer[1]=-1
    denom=monomial(size);denom[1]=1
    r=div(numer,denom)
    def ab(x):
        P=add(add(mul(z,mul(x,x)),mul(add(scale(z,2),scale(one,-1)),x)),z)
        a=div(mul(add(one,scale(mul(z,x),-1)),P),z)
        b=mul(x,add(add(one,scale(z,-1)),scale(mul(z,x),-1)))
        return a,b
    _,q=ab(r)
    # Closed iterates x_j=z^j r/[1-r*z*(1-z^j)/(1-z)].
    power=one
    geom=[0]*size
    for j in range(1,M+1):
        geom=add(geom,power); power=mul(power,z)
        x=div(mul(power,r),add(one,scale(mul(mul(r,z),geom),-1)))
        a,b=ab(x);q=add(mul(a,q),b)
    return div(q,z)

def iadd(a,b):return a[0]+b[0],a[1]+b[1]
def iscale(a,c):return (a[0]*c,a[1]*c) if c>=0 else (a[1]*c,a[0]*c)
def idiv(a,b):
    need(not b[0]<=0<=b[1],'INTERVAL_ZERO_DIVISOR')
    values=[x/y for x in a for y in b]
    return min(values),max(values)

def gamma_coefficients(alpha,K):
    # Exact recurrence for f(n)=n^(alpha+1) Gamma(n-alpha)/Gamma(n+1):
    # f(n+1)=(1+1/n)^alpha*(1-alpha/n)*f(n).
    size=K+3
    binom=[F(1)]
    for k in range(1,size):binom.append(binom[-1]*(alpha-k+1)/k)
    factor=add(binom,scale(shift(binom),-alpha))
    w=[F(0)]+[F((-1)**(k-1)) for k in range(1,size)]
    powers=[series_power(w,j) for j in range(K+1)]
    g=[F(1)]+[F(0)]*K
    def residual(g):
        poly=g+[F(0)]*(size-len(g));lhs=[F(0)]*size
        for j,c in enumerate(g):lhs=add(lhs,scale(powers[j],c))
        return add(lhs,scale(mul(factor,poly),-1))
    for k in range(1,K+1):
        constant=residual(g)[k+1]; g[k]=1
        slope=residual(g)[k+1]-constant
        need(slope!=0,'GAMMA_RECURRENCE_PIVOT')
        g[k]=-constant/slope
    need(residual(g)[:K+2]==[0]*(K+2),'GAMMA_RECURRENCE_RESIDUAL')
    return g

def corrections(f):
    R=F(101,400);X=F(11,9);delta=1-R*X/(1-R);T=X/delta
    need(delta>0,'JET_ORBIT_DENOMINATOR')
    Ac=T+(2+R)*T*R+(2+2*R)*T*T*R*R+T**3*R**3
    Bc=T*(1+R+R*T)
    need(Ac/(1-R)<6 and Ac<5 and Bc<4 and 1/(1-R)<F(3,2),'JET_CIRCLE_BOUNDS')
    need(4*F(3,2)*3**6<5000,'JET_PARTIAL_BOUND')
    need((5000*Ac+Bc*R)/(1-R)<40000 and F(400,99)<5,'JET_TELESCOPING_BOUND')
    need(40000*5==200000,'JET_H_TAIL_BOUND')
    h=local_jet(64,5)
    intervals=[(h[j]-200000*10**j*R**64,h[j]+200000*10**j*R**64) for j in range(6)]
    need([displayed_interval(v,24) for v in intervals]==f['enclosures']['h'],'H_JET_ENCLOSURES')
    _,v=derivative(64); E=F(16929,3072*4**64)
    need(intervals[1][0]<=-8*v<=intervals[1][1] and abs(h[1]+8*v)==0,'H1_DERIVATIVE_IDENTITY')
    ghalf=gamma_coefficients(F(1,2),2);gthree=gamma_coefficients(F(3,2),1)
    ratios=[F(1),F(-3,2),F(15,4)]
    for key,values in [('g_half',ghalf),('g_three_halves',gthree),('gamma_ratios',ratios)]:
        need([str(v) for v in values]==f['gamma'][key],'GAMMA_'+key.upper())
    ratio3=idiv(intervals[3],intervals[1]);ratio5=idiv(intervals[5],intervals[1])
    c1=iadd((ghalf[1],ghalf[1]),iscale(ratio3,ratios[1]))
    c2=iadd(iadd((ghalf[2],ghalf[2]),iscale(ratio3,ratios[1]*gthree[1])),iscale(ratio5,ratios[2]))
    need(displayed_interval(c1,24)==f['enclosures']['c1'],'C1_ENCLOSURE')
    need(displayed_interval(c2,24)==f['enclosures']['c2'],'C2_ENCLOSURE')
    return {'M':64,'degree':5,'circle_radius':'1/10','H_tail':'200000*(101/400)^64',
            'h':[displayed_interval(v,24) for v in intervals],
            'c1':displayed_interval(c1,24),'c2':displayed_interval(c2,24),
            'gamma_half':[str(v) for v in ghalf],'gamma_three_halves':[str(v) for v in gthree]}

def run(root=ROOT,skip_integrity=False):
    count=None if skip_integrity else integrity(root)
    f=fixture(root/'fixtures/certificate.json')
    # Cheap independent reconstruction rejects corrupted coefficient fixtures before
    # doing unrelated high-order certificates. All full checks still run on success.
    terms=state_terms(80)
    need(terms==f['sequences']['internal_terms'],'INTERNAL_TERMS')
    need(terms[:29]==f['sequences']['external_prefix'],'EXTERNAL_PREFIX')
    import companion
    cterms=companion.state_terms(80)
    need(cterms==f['companion']['internal_terms'],'COMPANION_INTERNAL_TERMS')
    need(cterms[:26]==f['companion']['external_prefix'],'COMPANION_EXTERNAL_PREFIX')
    symbolic=symbolic_checks()
    enumeration_result=enumeration(f)
    leading_result=leading(f)
    correction_result=corrections(f)
    import companion
    companion_result=companion.run(f['companion'])
    return {'status':'PASS','kind':'EXACT_FINITE_REPLAY','sealed_files':count,
            'algebra':symbolic,'enumeration':enumeration_result,'leading':leading_result,
            'corrections':correction_result,'companion':companion_result,'limitations':LIMITATIONS}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--skip-integrity',action='store_true',help='development only; not a sealed-bundle validation')
    args=ap.parse_args()
    try: result=run(skip_integrity=args.skip_integrity)
    except CheckFailure as error:
        print(json.dumps({'status':'FAIL','diagnostic':error.name,'detail':error.detail},indent=2));return 1
    except Exception as error:
        print(json.dumps({'status':'ERROR','diagnostic':'UNEXPECTED_EXCEPTION','detail':type(error).__name__+': '+str(error)},indent=2));return 2
    print(json.dumps(result,indent=2,sort_keys=True));return 0
if __name__=='__main__':sys.exit(main())
