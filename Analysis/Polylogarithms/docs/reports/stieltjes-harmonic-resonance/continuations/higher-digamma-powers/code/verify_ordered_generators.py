"""Independent finite-word and convergent polylogarithm diagnostics."""
from functools import lru_cache
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps=70
ROOT=Path(__file__).resolve().parents[1]
results=[]

def record(name,lhs,rhs,tolerance='1e-57'):
    residual=abs(lhs-rhs)
    assert residual < mp.mpf(tolerance)*max(1,abs(lhs),abs(rhs)),(name,residual)
    results.append({'name':name,'lhs':str(lhs),'rhs':str(rhs),
                    'absolute_residual':mp.nstr(residual,8)})

def finite_harmonic(n,b,orders,tag_derivatives=None):
    """Direct decreasing-index recursion, independent of Gamma products."""
    if tag_derivatives is None:tag_derivatives=(0,)*len(orders)
    @lru_cache(None)
    def value(bound,position):
        if position==len(orders):return mp.mpf(1)
        return mp.fsum((mp.mpf(j)+b)**(-orders[position])*
                     (-mp.log(mp.mpf(j)+b))**tag_derivatives[position]*
                     value(j,position+1) for j in range(bound))
    return value(n,0)

b=mp.mpf('0.7'); n=6; a=b+n; s=mp.mpc('2.4','0.3')
for m in (1,2,3,4):
    left=mp.fsum((-m)**p*finite_harmonic(n,b,(1,)*p+(s,))
                for p in range(n))
    right=mp.gamma(a-m)/mp.gamma(a)*mp.fsum(
         (b+j)**(1-s)*mp.fprod(b+j-h for h in range(1,m))
         for j in range(n))
    record(f'one_tag_integer_gap_m{m}',left,right)

for derivative in (0,1,2,3):
    left=mp.fsum((-1)**p*finite_harmonic(n,b,(1,)*p+(2,),
                                  (0,)*p+(derivative,)) for p in range(n))
    right=(-1)**derivative*(mp.stieltjes(derivative,b)-
                            mp.stieltjes(derivative,a))/(a-1)
    record(f'generalized_Stieltjes_index_{derivative}',left,right)

left=mp.fsum((-1)**p*finite_harmonic(n,b,(1,)*p+(1,),
                                    (0,)*p+(1,)) for p in range(n))
record('log_Gamma_tag_derivative',left,(mp.loggamma(b)-mp.loggamma(a))/(a-1))

for orders in ((2,2),(mp.mpc('1.8','0.2'),mp.mpc('2.3','-0.1'))):
    left=mp.fsum((-2)**p*(-1)**q*finite_harmonic(
         n,b,(1,)*p+(orders[0],)+(1,)*q+(orders[1],))
         for p in range(n-1) for q in range(n-1-p))
    right=finite_harmonic(n,b,(orders[0]-1,orders[1]-1))/((a-1)*(a-2))
    record('two_tag_staircase_'+str(orders),left,right)

def single_polylog(order,z,terms=280):
    return mp.fsum(z**n/mp.mpf(n)**order for n in range(1,terms+1))

def depth_two_polylog(order,z,terms=280):
    # Li_(1,order): the inner partial sum is computed independently.
    inner=mp.mpf(0); total=mp.mpc(0)
    for n in range(1,terms+1):
        total += z**n*inner/n
        inner += mp.mpf(n)**(-order)
    return total

def polylog_depth_generator(order,z,marker,terms=280):
    # Coefficients obtained by adding a new largest integer to every
    # finite ordered subset, before summing their powers of z.
    prefix=mp.mpc(0); total=mp.mpc(0)
    for n in range(1,terms+1):
        increment=mp.mpf(n)**(-order)+marker*prefix/n
        total += z**n*increment
        prefix += increment
    return total

for z in (mp.mpf('0.3'),mp.mpc('0.25','0.2')):
    for order in (mp.mpf(1),mp.mpc('2.2','0.4'),mp.mpc('-0.3','0.2')):
        for m in (1,2):
            left=polylog_depth_generator(order,z,-m)
            if m==1:
                right=(1-z)*(single_polylog(order,z)+depth_two_polylog(order-1,z))
            else:
                right=((1-z)**2*(single_polylog(order,z)+
                       depth_two_polylog(order-1,z)-depth_two_polylog(order-2,z))+
                       z*(1-z)*single_polylog(order-1,z))
            record(f'polylog_z{z}_s{order}_m{m}',left,right)

result={'status':'pass','working_digits':mp.mp.dps,'checks':len(results),
        'max_absolute_residual':mp.nstr(max(mp.mpf(x['absolute_residual'])
                                         for x in results),8),
        'meaning':'non-interval diagnostics; finite-word and power-series evaluations',
        'mpmath_version':mp.__version__,'results':results}
(ROOT/'data'/'ordered_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))
