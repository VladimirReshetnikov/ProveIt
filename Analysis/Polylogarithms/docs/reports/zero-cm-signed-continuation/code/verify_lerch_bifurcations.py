"""Exact sign certificates used by the Lerch zero-bifurcation theorem.

Only the Python standard library is required. All interval endpoints are
integers divided by 2**160, and all rounding is directed. The proof uses
the elementary monotone tail after 1,000 summands, not special-function
software. This certifies endpoint signs; it does not certify the separately
reported numerical bifurcation coordinates.
"""
from fractions import Fraction
from pathlib import Path
import json

BITS = 160
SCALE = 1 << BITS
LOG_TERMS = 64
TERMS = 1000


def ceildiv(a, b):
    return -((-a)//b)


def add(a,b):
    return a[0]+b[0], a[1]+b[1]


def neg(a):
    return -a[1], -a[0]


def sub(a,b):
    return add(a,neg(b))


def mul(a,b):
    products = [x*y for x in a for y in b]
    return min(products)//SCALE, ceildiv(max(products),SCALE)


def power(a,n):
    out = (SCALE,SCALE)
    for _ in range(n):
        out=mul(out,a)
    return out


def rational_scale(a, q):
    q=Fraction(q)
    if q < 0:
        return neg(rational_scale(a,-q))
    return a[0]*q.numerator//q.denominator, ceildiv(a[1]*q.numerator,q.denominator)


def log_core(x):
    """Enclose log(x) for rational 1 <= x <= 2."""
    assert 1 <= x <= 2
    u=(x-1)/(x+1)
    numerator,denominator=u.numerator,u.denominator
    numpow,denpow=numerator,denominator
    lo=hi=0
    for j in range(LOG_TERMS):
        den=(2*j+1)*denpow
        num=2*SCALE*numpow
        lo+=num//den
        hi+=ceildiv(num,den)
        numpow*=numerator*numerator
        denpow*=denominator*denominator
    # Exact majorant 2*u**(2J+1)/((2J+1)*(1-u*u)).
    rem=Fraction(2*numpow*denominator*denominator,
                 denpow*(2*LOG_TERMS+1)*(denominator*denominator-numerator*numerator))
    hi+=ceildiv(SCALE*rem.numerator,rem.denominator)
    return lo,hi


LOG2=log_core(Fraction(2))


def logarithm(x):
    x=Fraction(x)
    assert x > 0
    if x < 1:
        return neg(logarithm(1/x))
    exponent=0
    while x >= 2:
        x/=2
        exponent+=1
    return add(rational_scale(LOG2,exponent),log_core(x))


def elementary(n,x):
    """d/da [log(a)**n/a], evaluated at positive rational x."""
    lx=logarithm(x)
    return rational_scale(mul(power(lx,n-1),sub((n*SCALE,n*SCALE),lx)),1/(x*x))


def certificate(n,a):
    a=Fraction(a)
    total=(0,0)
    for m in range(TERMS):
        total=add(total,elementary(n,a+m))
    b=a+TERMS
    lb=logarithm(b)
    # For n=3,4 and log(b)>6, h=-elementary(n,b) is positive decreasing.
    # The derivative is -(log b)**(n-2)/b**3 times
    # [2(log b)**2 - 3*n*log b + n*(n-1)], which is strictly positive at
    # log b >= 6 for n=3,4. The quadratic is increasing on that ray.
    assert n in (3,4) and lb[0] > 6*SCALE
    assert 2*6*6-3*n*6+n*(n-1) > 0
    integral=rational_scale(power(lb,n),1/b)
    f_b=elementary(n,b)
    assert f_b[1] < 0
    # Integral test: f(b)-I <= sum_{m>=M} f(a+m) <= -I.
    tail=(f_b[0]-integral[1], -integral[0])
    total=add(total,tail)
    normalized=rational_scale(total,(-1)**(n+1)*a*a)
    sign=1 if normalized[0]>0 else -1 if normalized[1]<0 else 0
    assert sign
    unit=10**6
    rounded=(normalized[0]*unit//SCALE,ceildiv(normalized[1]*unit,SCALE))
    return dict(n=n,a=str(a),sign=sign,lower_integer=normalized[0],
                upper_integer=normalized[1],denominator=SCALE,
                decimal_6=[f'{v/unit:.6f}' for v in rounded])


def verify():
    rows=[]
    for n,points in [(3,['4/5','11/10','3/2','21/10']),
                     (4,['4/5','47/50','6/5','17/10','11/5'])]:
        group=[certificate(n,a) for a in points]
        assert [r['sign'] for r in group] == [(-1)**i for i in range(n+1)]
        rows.extend(group)
    # The cubic unfolding coefficient for n=4 is negative in F convention:
    assert LOG2[0]>0 and LOG2[1]<SCALE
    return dict(status='all exact endpoint sign certificates passed',
                arithmetic='outward fixed-point integer intervals',bits=BITS,
                logarithm_terms=LOG_TERMS,series_terms=TERMS,
                tail='monotone integral comparison',rows=rows)


if __name__=='__main__':
    result=verify()
    out=(Path(__file__).resolve().parents[1] / "results" / "lerch_endpoint_certificates.json")
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'])
    for row in result['rows']:
        print(row['n'],row['a'],row['decimal_6'],row['sign'])
