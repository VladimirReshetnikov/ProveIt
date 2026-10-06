#!/usr/bin/env python3
"""Report176 exact offline verifier. Python standard library only; no assert guards."""
from __future__ import annotations
import argparse
import ast
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial, isfinite
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent
ORDER = 5
SOURCE = [3,14,342,5256,252360,7950960,582346800,30400755840,
          3055726477440,234650484230400,30479146156166400,3193083216360576000,
          515174657767010841600,69927761804930559129600,
          13622234004598726450944000,2307722078006148475736064000]

class VerificationError(ValueError):
    pass

def require(ok, message):
    if not ok:
        raise VerificationError(message)

def integer(value, minimum, maximum, label):
    require(type(value) is int and minimum <= value <= maximum, 'invalid '+label)
    return value

def poly(a):
    a = list(map(F,a)) or [F(0)]
    while len(a)>1 and not a[-1]:
        a.pop()
    return tuple(a)

def add(a,b):
    return poly((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                for i in range(max(len(a),len(b))))

def scale(a,c):
    return poly(x*c for x in a)

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]+=x*y
    return poly(c)

def monomial(power, coefficient=1):
    return poly([0]*power+[coefficient])

def diff(a):
    return poly(i*a[i] for i in range(1,len(a)))

def evaluate(a,value):
    out=F(0)
    for c in reversed(a):
        out=out*value+c
    return out

def gaussian_derivative(a):
    # e^(3z^2/8) d/dz [e^(-3z^2/8) a(z)].
    return add(diff(a),mul(a,(0,F(-3,4))))

def ps_exp(d,order):
    """exp(sum_{j>=1}d_j h^j), where d_j are rational polynomials."""
    require(d[0]==(F(0),),'formal exponential needs zero constant')
    p=[(F(1),)]
    for j in range(1,order+1):
        total=(F(0),)
        for r in range(1,j+1):
            total=add(total,scale(mul(d[r],p[j-r]),r))
        p.append(scale(total,F(1,j)))
    return p

def series_mul(a,b,order):
    return [sum((a[i]*b[j-i] for i in range(j+1) if i<len(a) and j-i<len(b)),F(0))
            for j in range(order+1)]

def series_div(a,b,order):
    require(bool(b) and b[0]!=0,'division by zero formal constant')
    c=[]
    for j in range(order+1):
        c.append(((a[j] if j<len(a) else F(0))-
                  sum((b[i]*c[j-i] for i in range(1,min(j,len(b)-1)+1)),F(0)))/b[0])
    return c

def series_exp(a,order):
    require(a and a[0]==0,'formal exponential needs zero constant')
    out=[F(1)]
    for j in range(1,order+1):
        out.append(sum((r*a[r]*out[j-r] for r in range(1,min(j,len(a)-1)+1)),F(0))/j)
    return out

def series_log(a,order):
    require(a and a[0]==1,'formal logarithm needs constant one')
    der=[(j+1)*a[j+1] if j+1<len(a) else F(0) for j in range(order)]
    quotient=series_div(der,a,order-1)
    return [F(0)]+[quotient[j-1]/j for j in range(1,order+1)]

@lru_cache(None, typed=True)
def bernoulli(n):
    integer(n,0,24,'Bernoulli index')
    if n==0:return F(1)
    return -sum((F(comb(n+1,k))*bernoulli(k) for k in range(n)),F(0))/(n+1)

def bernoulli_at(n,x):
    return sum((F(comb(n,k))*bernoulli(k)*x**(n-k) for k in range(n+1)),F(0))

def rising(p,r):
    out=1
    for j in range(r):out*=p+j
    return out

def gamma_log_coefficients(order):
    """Taylor in the shift using psi(x+1)=log x+1/(2x)-sum B_2r/(2r x^2r)."""
    integer(order,0,12,'gamma order')
    d=[(F(0),) for _ in range(order+1)]
    for m in range(2,order+3):
        c=-F((2*(-1)**m+1)*(-1)**(m-2),m*(m-1)*2**m)
        d[m-2]=add(d[m-2],monomial(m,c))
    psi=[(1,F(1,2))]+[(2*r,-bernoulli(2*r)/F(2*r)) for r in range(1,order//2+2)]
    for p,c in psi:
        for m in range(1,order+3):
            j=2*p+m-2
            if j<=order:
                coefficient=-F(2*(-1)**m+1,2**m*factorial(m))*c*(-1)**(m-1)*rising(p,m-1)
                d[j]=add(d[j],monomial(m,coefficient))
    return d

def shifted_gamma(d,shift,order):
    integer(shift,0,2,'factorial-moment shift')
    out=[(F(0),) for _ in range(order+1)]
    for s,a in enumerate(d):
        for power,c in enumerate(a):
            for t in range(min(power,order-s)+1):
                out[s+t]=add(out[s+t],monomial(power-t,c*comb(power,t)*shift**t))
    return out

def centered_moments(maximum):
    mu=[(F(1),),(F(0),)]
    for r in range(1,maximum):
        mu.append(mul((0,1),add(diff(mu[r]),scale(mu[r-1],r))))
    return mu[:maximum+1]

def poisson_q(d,order,shift=0):
    """Finite centered-Poisson-moment expansion; parameter held fixed during differentiation."""
    dd=shifted_gamma(d,shift,order)
    require(dd[0]==(F(0),F(0),F(-3,8)),'incorrect Gaussian constant')
    dd[0]=(F(0),)
    p=ps_exp(dd,order)
    mu=centered_moments(2*order)
    q=[(F(0),) for _ in range(order+1)]
    for s in range(order+1):
        derivative=p[s]
        for r in range(2*(order-s)+1):
            for ell,c in enumerate(mu[r]):
                j=s+r-ell
                if c and 0<=j<=order:
                    q[j]=add(q[j],scale(mul(monomial(ell),derivative),c/F(factorial(r))))
            derivative=gaussian_derivative(derivative)
    return q

def poisson_q_operator(d,order):
    """Independent finite cumulant-operator recurrence, indexed by derivative order."""
    p=ps_exp([(F(0),)]+d[1:],order)
    operator=[{0:(F(1),)}]
    for m in range(1,order+1):
        current={}
        for r in range(1,m+1):
            for derivative,a in operator[m-r].items():
                k=derivative+r+1
                term=scale(mul((0,1),a),F(r,m*factorial(r+1)))
                current[k]=add(current.get(k,(F(0),)),term)
        operator.append(current)
    q=[]
    for j in range(order+1):
        total=(F(0),)
        for m in range(j+1):
            derivative=p[j-m]
            for r in range(2*m+1):
                if r in operator[m]:total=add(total,mul(operator[m][r],derivative))
                derivative=gaussian_derivative(derivative)
        q.append(total)
    return q

def exact_histogram(n):
    integer(n,0,1000,'part size')
    numerator=factorial(n)**3
    out={}
    for k in range(n%2,n+1,2):
        divisor=factorial(k)*factorial((n-k)//2)**2*factorial((n+k)//2)
        value,remainder=divmod(numerator,divisor)
        require(remainder==0,'nonintegral labeled matching count')
        out[k]=value if k==0 else 3*value
    return out

@lru_cache(None, typed=True)
def recursive_histogram(a,b,c,unmatched_part=-1):
    for x in (a,b,c):integer(x,0,8,'recursive part size')
    integer(unmatched_part,-1,2,'unmatched part')
    counts=[a,b,c]
    if not sum(counts):return ((0,1),)
    i=next(j for j,n in enumerate(counts) if n)
    counts[i]-=1
    out={}
    if unmatched_part in (-1,i):
        for k,num in recursive_histogram(*counts,i):out[k+1]=out.get(k+1,0)+num
    for j in range(3):
        if j==i or not counts[j]:continue
        choices=counts[j];counts[j]-=1
        for k,num in recursive_histogram(*counts,unmatched_part):out[k]=out.get(k,0)+choices*num
        counts[j]+=1
    return tuple(sorted(out.items()))

def marking_interval(a,b):
    require(type(a) in (int,float,F) and type(b) in (int,float,F), 'marking endpoints must be real')
    require(isfinite(a) and isfinite(b) and 0<a<=b,'marking compact must lie in (0,infinity)')
    return a/2,2*b

def marked_exact_moments(n,v):
    marking_interval(v,v)
    v=F(v)
    hist=exact_histogram(n)
    a=sum((value*v**k for k,value in hist.items()),F(0))
    first=sum((k*value*v**k for k,value in hist.items()),F(0))/a
    second=sum((k*k*value*v**k for k,value in hist.items()),F(0))/a
    return a,first,second-first*first

def rational_strings(a):return [str(c) for c in a]
def polynomial_strings(a):return [rational_strings(p) for p in a]
def canonical(data):return json.dumps(data,sort_keys=True,indent=2,ensure_ascii=True)+'\n'

def inverse_refinement_check():
    # x=2 lambda^2 implies lambda'=1/(4 lambda), while H''=3/(2x).
    x_over_lambda_squared=F(2)
    lambda_prime_coefficient=1/(2*x_over_lambda_squared)
    h_second_coefficient=F(3,2)/x_over_lambda_squared
    # g~lambda: multiplying Laurent monomials cancels lambda exponents.
    first_exponent=-1+1
    second_exponent=-2+1+1
    first=lambda_prime_coefficient
    second=-h_second_coefficient/2
    require(first_exponent==second_exponent==0,'inverse Laurent powers did not cancel')
    require(first==F(1,4) and second==F(-3,8),'inverse refinement coefficients differ')
    return {'x_over_lambda_squared':str(x_over_lambda_squared),
            'lambda_prime_coefficient_of_lambda_inverse':str(lambda_prime_coefficient),
            'H_second_coefficient_of_lambda_inverse_squared':str(h_second_coefficient),
            'gprime_g_coefficient_of_D_inverse_squared':str(first),
            'minus_half_Hsecond_g_squared_coefficient_of_D_inverse_cubed':str(second)}

def rational_ceiling(value):
    require(type(value) is F,'ceiling input must be an exact Fraction')
    return -((-value.numerator)//value.denominator)

def rational_floor(value):
    require(type(value) is F,'floor input must be an exact Fraction')
    return value.numerator//value.denominator

def finite_boundary_check():
    """Finite rational inequalities used at ceiling boundaries, not an onset proof."""
    cases=[]
    exact_lower=exact_upper=0
    for center in range(1,9):
        for displacement in (F(-1,1000),F(0),F(1,1000)):
            for epsilon in (F(1,1000),F(1,2000)):
                x=F(center)+displacement
                left,right=x-epsilon,x+epsilon
                lower,upper=rational_ceiling(left),rational_ceiling(right)
                n_minus=lower-1
                floor_left=rational_floor(left)
                require(n_minus<left<=lower and upper-1<right<=upper,
                        'rational ceiling boundary inequality failed')
                require(floor_left<=left<floor_left+1,'rational floor inequality failed')
                # These are exactly the endpoint inequalities for the linear
                # monotone model with errors bounded by epsilon.
                left_margin=x-(n_minus+epsilon)
                right_margin=(upper-epsilon)-x
                require(left_margin>0 and right_margin>=0,'threshold endpoint margin failed')
                require(lower<=upper,'reversed threshold enclosure')
                if left.denominator==1:
                    exact_lower+=1
                    require(floor_left==left and not floor_left<left,
                            'integer floor boundary did not expose equality')
                if right.denominator==1:
                    exact_upper+=1
                    require(right_margin==0,'exact upper threshold equality failed')
                cases.append({'x':str(x),'epsilon':str(epsilon),
                              'floor_x_minus_epsilon':floor_left,
                              'ceil_x_minus_epsilon':lower,'ceil_x_plus_epsilon':upper,
                              'n_minus':n_minus,'strict_lower_margin':str(left_margin),
                              'weak_upper_margin':str(right_margin)})
    require(len(cases)==48 and exact_lower==8 and exact_upper==8,'boundary case coverage differs')
    return {'scope':'Finite exact rounding inequalities only; no effective asymptotic proof',
            'integer_centers':[1,2,3,4,5,6,7,8], 'cases':cases,
            'exact_lower_integer_cases':exact_lower,'exact_upper_equality_cases':exact_upper}

def derive():
    d=gamma_log_coefficients(ORDER)
    q=poisson_q(d,ORDER)
    require(q==poisson_q_operator(d,ORDER),'independent Poisson constructions differ')
    for j,p in enumerate(q):
        require(len(p)-1<=3*j,'q degree exceeds bound')
        require(all(not c or i%2==j%2 for i,c in enumerate(p)),'q parity fails')
    values=[evaluate(p,F(1)) for p in q]
    carrier=series_mul(values,series_exp([F(0),F(0),F(-1,8)],ORDER),ORDER)
    logcarrier=series_log(values,ORDER);logcarrier[2]-=F(1,8)
    inverses=series_div([F(1)],values,4)
    shifted=[poisson_q(d,ORDER,r) for r in (1,2)]
    quotients=[series_div([evaluate(p,F(1)) for p in qs],values,ORDER) for qs in shifted]
    mean={j-1:c for j,c in enumerate(quotients[0])}
    second={j-2:c for j,c in enumerate(quotients[1])}
    variance={j:second.get(j,F(0))+mean.get(j,F(0))-
              sum((a*b for i,a in mean.items() for k,b in mean.items() if i+k==j),F(0))
              for j in range(-2,3)}
    require(variance[-2]==0,'variance leading cancellation failed')
    log_fixed=[F(0)]+[F((-1)**(j+1),j*(j+1))*(3*bernoulli_at(j+1,F(1))-
                2*bernoulli_at(j+1,F(1,2))-bernoulli_at(j+1,F(3,2))) for j in range(1,5)]
    fixed=series_exp(log_fixed,4)
    # Independent consistency: substitute z=h in the central log gamma algebra.
    central_fixed=[F(0)]*9
    for j,p in enumerate(gamma_log_coefficients(8)):
        for k,c in enumerate(p):
            if j+k<=8:central_fixed[j+k]+=c
    require(all(central_fixed[2*j]==log_fixed[j] for j in range(5)) and
            all(central_fixed[j]==0 for j in (1,3,5,7)),'fixed-shift gamma methods differ')
    fixed_h=[fixed[j//2] if j%2==0 else F(0) for j in range(5)]
    odd=series_mul(inverses,fixed_h,4)
    counts=[sum(exact_histogram(n).values()) for n in range(101)]
    require(counts[1:17]==SOURCE,'OEIS displayed values differ')
    require(all(a<b for a,b in zip(counts,counts[1:])),'counts are not strictly increasing on checked range')
    histograms={}
    for n in range(9):
        exact=exact_histogram(n)
        require(dict(recursive_histogram(n,n,n))==exact,'matching recursion differs at n='+str(n))
        histograms[str(n)]={str(k):value for k,value in exact.items()}
    # Enforce the printed results separately from the supplied certificate.
    require(values[:5]==list(map(F,['1','13/96','2185/18432','-4125847/26542080','1950842261/10192158720'])), 'displayed q(1) differ')
    require(carrier[:5]==list(map(F,['1','13/96','-119/18432','-4575127/26542080','1879441301/10192158720'])), 'displayed elementary coefficients differ')
    require(logcarrier[:5]==list(map(F,['0','13/96','-1/64','-5243/30720','425/2048'])), 'displayed logarithmic coefficients differ')
    require([mean[j] for j in range(-1,3)]==list(map(F,['1','-3/4','21/32','-9/32'])), 'displayed mean differs')
    require([variance[j] for j in range(-1,3)]==list(map(F,['1','-3/2','71/32','-41/16'])), 'displayed variance differs')
    require(inverses==list(map(F,['1','-13/96','-1847/18432','4912087/26542080','-2299743979/10192158720'])), 'displayed even rare probability differs')
    require(odd==list(map(F,['1','-13/96','-4151/18432','5361367/26542080','-818433259/10192158720'])), 'displayed odd rare probability differs')
    return {
        'schema_version':1, 'report':176, 'order':ORDER,
        'inverse_refinement':inverse_refinement_check(), 'finite_threshold_boundaries':finite_boundary_check(),
        'convention':'Ascending rational polynomial coefficients, normalized reduced fraction strings; h=1/lambda; y=1/lambda^2',
        'd_polynomials':polynomial_strings(d), 'q_polynomials':polynomial_strings(q),
        'q_at_one':rational_strings(values), 'elementary_carrier':rational_strings(carrier),
        'log_elementary_carrier':rational_strings(logcarrier),
        'shifted_q_polynomials':{str(r):polynomial_strings(qs) for r,qs in zip((1,2),shifted)},
        'factorial_moment_quotients':{str(r):rational_strings(qs) for r,qs in zip((1,2),quotients)},
        'mean_h_powers':{str(j):str(mean[j]) for j in range(-1,3)},
        'variance_h_powers':{str(j):str(variance[j]) for j in range(-1,3)},
        'fixed_shift_log_y':rational_strings(log_fixed), 'fixed_shift_R_y':rational_strings(fixed),
        'rare_even_relative_h':rational_strings(inverses), 'rare_odd_relative_h':rational_strings(odd),
        'counts_n0_to100':counts, 'recursive_histograms_n0_to8':histograms,
        'source':{'url':'https://oeis.org/A297487','displayed_offset':1,'displayed_values':SOURCE},
        'scope':{'algebraic_order':5,'fixed_shift_order_in_y':4,'count_maximum':100,
                 'recursion_maximum':8,'source_values_compared':16,
                 'numerical_remainder_bounds_certified':False,'global_priority_certified':False}
    }

def reject(call,label):
    try:call()
    except (VerificationError,ValueError,TypeError,OverflowError):return
    raise VerificationError('invalid parameter accepted: '+label)

def self_tests():
    require(mul((1,2),(3,4))==poly((3,10,8)),'polynomial multiplication failed')
    require(diff((1,2,3))==poly((2,6)),'polynomial differentiation failed')
    require(series_div([F(1)],[F(1),F(-1)],5)==[F(1)]*6,'series inversion failed')
    require([bernoulli(j) for j in (0,1,2,4,6,8,10)]==list(map(F,['1','-1/2','1/6','-1/30','1/42','-1/30','5/66'])),'Bernoulli check failed')
    require(centered_moments(6)==list(map(poly,[(1,),(0,),(0,1),(0,1),(0,1,3),(0,1,10),(0,1,25,15)])),'Poisson centered moments failed')
    require(marked_exact_moments(0,1)==(F(1),F(0),F(0)),'empty graph boundary failed')
    require(marked_exact_moments(1,1)==(F(3),F(1),F(0)),'n=1 boundary failed')
    require(marked_exact_moments(2,1)==(F(14),F(6,7),F(48,49)),'n=2 boundary failed')
    require(marking_interval(F(1,2),F(3,2))==(F(1,4),F(3)),'enlarged compact failed')
    bad=0
    for n in (-1,True,1.0,'1',1001):reject(lambda n=n:exact_histogram(n),'n');bad+=1
    for order in (-1,True,1.0,13):reject(lambda order=order:gamma_log_coefficients(order),'order');bad+=1
    for endpoints in ((0,1),(-1,1),(2,1),(float('nan'),1),(1,float('inf')),(True,1),('1',2)):
        reject(lambda p=endpoints:marking_interval(*p),'marking interval');bad+=1
    for shift in (-1,True,3):reject(lambda shift=shift:shifted_gamma(gamma_log_coefficients(1),shift,1),'shift');bad+=1
    reject(lambda:recursive_histogram(9,0,0),'recursive n');bad+=1
    reject(lambda:series_div([F(1)],[F(0)],1),'series denominator');bad+=1
    return {'arithmetic_and_boundary_checks':9,'invalid_parameter_rejections':bad}

def warm_cache_type_tests():
    """Type guards must survive already cached equal-valued integer arguments."""
    rejected=0
    names=('a','b','c','unmatched_part')
    for position in range(4):
        invalid_values=(False,True,0.0,1.0,F(0))+((-1.0,) if position==3 else ())
        for invalid in invalid_values:
            valid=[0,0,0,-1]
            valid[position]=int(invalid)
            recursive_histogram(*valid)
            altered=valid[:];altered[position]=invalid
            reject(lambda args=altered:recursive_histogram(*args),'warm recursive positional type')
            rejected+=1
            valid_keywords=dict(zip(names,valid))
            recursive_histogram(**valid_keywords)
            altered_keywords=dict(zip(names,altered))
            reject(lambda args=altered_keywords:recursive_histogram(**args),'warm recursive keyword type')
            rejected+=1
    # Even a one-argument cache needs typed=True: keyword calls otherwise give
    # equal cache keys for n=0, n=False and n=0.0.
    for invalid in (False,True,0.0,1.0,2.0,F(0)):
        bernoulli(int(invalid))
        reject(lambda value=invalid:bernoulli(value),'warm Bernoulli positional type')
        rejected+=1
        bernoulli(n=int(invalid))
        reject(lambda value=invalid:bernoulli(n=value),'warm Bernoulli keyword type')
        rejected+=1
    require(rejected==54,'warm-cache type-test coverage differs')
    return rejected

def unique_object(pairs):
    out={}
    for key,value in pairs:
        require(key not in out,'duplicate JSON object key: '+key)
        out[key]=value
    return out

def load_certificate(path):
    def reject_constant(value):raise VerificationError('nonfinite JSON constant '+value)
    return json.loads(Path(path).read_text(encoding='utf-8'),object_pairs_hook=unique_object,
                      parse_constant=reject_constant)

def same(expected,actual,path='$'):
    require(type(expected) is type(actual),'wrong JSON type at '+path)
    if type(expected) is dict:
        require(expected.keys()==actual.keys(),'wrong JSON fields at '+path)
        for key in expected:same(expected[key],actual[key],path+'.'+key)
    elif type(expected) is list:
        require(len(expected)==len(actual),'wrong array length at '+path)
        for i,(x,y) in enumerate(zip(expected,actual)):same(x,y,path+'['+str(i)+']')
    else:require(expected==actual,'certificate mismatch at '+path)

def parse_polynomial(text,variable):
    """Read frozen reference expressions with a closed arithmetic AST; never eval."""
    require(type(text) is str and len(text)<10000,'invalid reference expression')
    tree=ast.parse(text,mode='eval')
    require(sum(1 for _ in ast.walk(tree))<=300,'reference expression too large')
    def raw(node):
        if isinstance(node,ast.Expression):return read(node.body)
        if isinstance(node,ast.Constant):
            require(type(node.value) is int,'reference constant is not an integer')
            return poly((node.value,))
        if isinstance(node,ast.Name):
            require(node.id==variable,'unexpected reference variable')
            return poly((0,1))
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,(ast.USub,ast.UAdd)):
            return scale(read(node.operand),-1 if isinstance(node.op,ast.USub) else 1)
        if isinstance(node,ast.BinOp):
            a=read(node.left);b=read(node.right)
            if isinstance(node.op,ast.Add):return add(a,b)
            if isinstance(node.op,ast.Sub):return add(a,scale(b,-1))
            if isinstance(node.op,ast.Mult):
                require(len(a)+len(b)-2<=30,'reference polynomial degree too large')
                return mul(a,b)
            if isinstance(node.op,ast.Div):
                require(len(b)==1 and b[0]!=0,'reference division is not by a nonzero constant')
                return scale(a,1/b[0])
            if isinstance(node.op,ast.Pow):
                require(len(b)==1 and b[0].denominator==1 and 0<=b[0]<=20,'invalid reference exponent')
                require((len(a)-1)*b[0]<=30,'reference polynomial degree too large')
                out=poly((1,))
                for _ in range(int(b[0])):out=mul(out,a)
                return out
        raise VerificationError('unsupported reference expression')
    def read(node):
        result=raw(node)
        require(all(c.numerator.bit_length()<=4096 and c.denominator.bit_length()<=4096 for c in result),'reference coefficient too large')
        return result
    return read(tree)

def verify_reference(path,derived):
    reference=load_certificate(path)
    for key,target,variable in [('d_j','d_polynomials','z'),('q_j','q_polynomials','v')]:
        require(type(reference[key]) is list and len(reference[key])==6,'wrong reference polynomial array')
        parsed=[rational_strings(parse_polynomial(item,variable)) for item in reference[key]]
        same(derived[target],parsed,'reference.'+key)
    same(derived['q_at_one'],reference['q_j_at_1'],'reference.q_j_at_1')
    same(derived['recursive_histograms_n0_to8'],reference['recursive_histograms_n0_to8'],'reference.histograms')
    same(16,reference['oeis_displayed_values_matched'],'reference.source_count')
    same(101,reference['author_exact_counts_matched'],'reference.count_range')

def check_manuscript_prefix(text,expected):
    """Read only the uniquely marked first-value display, with a closed grammar."""
    marker=r'The first values for $n=0,\ldots,8$ are'
    require(type(text) is str and text.count(marker)==1,'manuscript initial-value marker must occur once')
    following=text.split(marker,1)[1]
    display=re.match(r'\s*\\\[\s*(.*?)\s*\\\]',following,re.S)
    require(display is not None,'manuscript initial-value display is missing')
    content=display.group(1).replace(r'\,','').replace('\\ ',' ')
    require(re.fullmatch(r'\s*(?:0|[1-9][0-9]*)(?:\s*,\s*(?:0|[1-9][0-9]*))*\s*\.?\s*',content) is not None,
            'manuscript initial-value display has invalid syntax')
    stripped=content.strip()
    if stripped.endswith('.'):stripped=stripped[:-1].rstrip()
    values=[int(token.strip()) for token in stripped.split(',')]
    require(len(values)==9,'manuscript initial-value display must have nine integers')
    same(expected,values,'manuscript.initial_values')
    return len(values)

def verify(path,reference_path=ROOT/'references/independent_results.json',manuscript_path=ROOT/'report.tex'):
    tests=self_tests()
    derived=derive()
    tests['warm_cache_type_rejections']=warm_cache_type_tests()
    same(derived,load_certificate(path))
    verify_reference(reference_path,derived)
    prefix_count=check_manuscript_prefix(Path(manuscript_path).read_text(encoding='utf-8'),derived['counts_n0_to100'][:9])
    return {'status':'PASS','all_checks_passed':True,'report':176,'derivation_order':ORDER,
            'gamma_polynomials':6,'poisson_polynomials':6,'independent_poisson_methods':2,'independent_reference_polynomials':12,
            'direct_factorial_moment_shifts':[1,2],'fixed_shift_coefficients_in_y':5,
            'rare_probability_orders':4,'exact_count_values':101,'recursive_histograms':9,'inverse_refinement_coefficients':2,'finite_rational_boundary_cases':48,
            'oeis_displayed_values':16,'manuscript_initial_values':prefix_count,'parameter_tests':tests,
            'q5_at_one':derived['q_at_one'][5],
            'claims_not_certified':['analytic remainder constants or onset','global priority','exponential count transseries']}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=ROOT/'data/certificates.json')
    parser.add_argument('--manuscript',type=Path,default=ROOT/'report.tex')
    parser.add_argument('--reference',type=Path,default=ROOT/'references/independent_results.json')
    parser.add_argument('--json',action='store_true',help='JSON is always emitted; retained for scripting')
    parser.add_argument('--extended',action='store_true',help='compatibility alias: all checks always run')
    args=parser.parse_args()
    try:print(canonical(verify(args.data,args.reference,args.manuscript)),end='')
    except (VerificationError,OSError,ValueError,TypeError,KeyError,SyntaxError) as exc:
        print('VERIFICATION FAILED: '+str(exc),file=sys.stderr);sys.exit(1)

if __name__=='__main__':main()
