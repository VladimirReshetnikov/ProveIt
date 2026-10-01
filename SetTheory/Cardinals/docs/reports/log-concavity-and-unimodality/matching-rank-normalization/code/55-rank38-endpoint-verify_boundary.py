"""Exact finite certificate and independent endpoint regression checks.

Python 3.10+, standard library only. Outputs are deterministic.
"""
from fractions import Fraction as Q
from math import comb, gcd, lcm
from pathlib import Path
from random import Random
import json

HERE = Path(__file__).resolve().parent

def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0

def cubic_coefficients(a, b):
    r = a + b
    return [a*b*b*(r-1), -b*(r-1)*(a*b-2*a-2*b),
            a*(a*a+2*a*b-a+2*b*b-b), a*(a*a+2*a*b-a-b)]

def parameters(a, b, h, m):
    r = a+b
    x, y = Q(b,h), Q(b*(b-1),h*(h+1))
    R, rho = Q(m-a+1,a), Q(a-1,m-a+2)
    J = Q(a*(a-1),2)+a*x+y
    K = Q(2*r*(a-1),a)*J
    A = (r-1)*(a+x)**2-K
    alpha = A+K/Q(m-a+2)
    B = (r-1)*x*(a+x)-r*(a*x+y)
    C = b*(b*(r-1)*x*x-r*(b-1)*y)
    return A, alpha, 2*b*R*B, R*R*C, B, C, K

def coefficients(a, b, n, m, w):
    return [sum(choose(a,i)*choose(n,k-i)*choose(b,j)*choose(m,k-j)*w**j
                for i in range(a+1) for j in range(b+1) if i+j >= k)
            for k in range(a+b+1)]

def positive_identity(a,b,h):
    r=a+b
    A,_,_,_,B,C,_=parameters(a,b,h,a)
    H=a*h*h-b*(r-1)
    Q0=a*a*(b*b+2*b-1)+a*(b-1)*(2*b*b+3*b-1)+b*(b-1)**2
    Q1=(r-1)*(2*a*b-a-b)
    R0=a*(b*b+2*b-1)+(b-1)*(3*b-1)
    R1=a*(3*b-1)+(b-1)
    left=Q(a*h**3*(h+1)**2,b*b*r)*(A*C-b*b*B*B)
    right=H*(Q0+Q1*h)+b*r*(r-1)*(R0+R1*h)
    assert left==right
    assert Q0>0 and Q1>=0 and R0>0 and R1>0
    if H>=0:
        assert left>0 and A>0

def first_negative_integer(poly):
    A,B,C=poly
    assert A<0<C
    def value(w):return A*w*w+B*w+C
    lo,hi=0,1
    while value(hi)>=0:hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if value(mid)<0:hi=mid
        else:lo=mid
    return hi,value(hi-1),value(hi)

def main():
    records=[]; negative=[]; rank_minima=[]
    for r in range(4,39):
        rank_values=[]
        for a in range(2,r-1):
            b=r-a
            cs=cubic_coefficients(a,b)
            H=max(1,(-cs[1]+cs[2]-1)//cs[2])
            assert all(cs[i]>0 for i in [0,2,3]) and cs[2]*H+cs[1]>=0
            vals=[]
            for h in range(1,H+1):
                value=sum(c*h**j for j,c in enumerate(cs))
                A=parameters(a,b,h,a)[0]
                assert value==A*a*h*h*(h+1)
                positive_identity(a,b,h)
                vals.append(value);rank_values.append((value,a,b,h))
                if value<0:negative.append([r,a,b,h,value])
                if r<38:assert value>0
                assert value!=0
            records.append({'a':a,'b':b,'H':H,'coefficients':cs,'values':vals})
        rank_minima.append([r,*min(rank_values)])
    assert len(records)==630 and sum(len(x['values']) for x in records)==2237
    assert negative==[[38,7,31,3,-3056],[38,8,30,3,-4392]]
    assert max(x['H'] for x in records)==10
    rng=Random(20261001)
    for _ in range(160):
        a,b=rng.randrange(1,14),rng.randrange(1,14)
        h=rng.randrange(1,25);m=a+rng.randrange(20);n=b+h-1
        w=Q(rng.randrange(1,200),rng.randrange(1,12))
        p=coefficients(a,b,n,m,w);r=a+b
        A,alpha,beta,gamma,_,_,_=parameters(a,b,h,m)
        D=choose(n,b)*choose(m,a-1)
        gap=(r-1)*p[-2]**2-2*r*p[-3]*p[-1]
        assert gap==D*D*w**(2*b-2)*(alpha*w*w+beta*w+gamma)
        positive_identity(a,b,h)
        if alpha>=0:assert gap>0
    witnesses=[]
    for a,b,h,expected_m,expected_poly,expected_w in [
        (8,30,3,794,[-22,6437219280,11385894392295],292602646),
        (7,31,3,923,[-2,3479879022,8332557477297],1739941906)]:
        A,_,_,_,_,_,K=parameters(a,b,h,a)
        m=a-1+K//(-A)
        assert m==expected_m
        assert parameters(a,b,h,m-1)[1]>=0>parameters(a,b,h,m)[1]
        _,alpha,beta,gamma,_,_,_=parameters(a,b,h,m)
        den=lcm(alpha.denominator,beta.denominator,gamma.denominator)
        nums=[int(c*den) for c in [alpha,beta,gamma]]
        g=gcd(gcd(abs(nums[0]),abs(nums[1])),abs(nums[2]))
        poly=[c//g for c in nums];factor=Q(g,den)
        assert poly==expected_poly
        w,prev,val=first_negative_integer(poly)
        assert w==expected_w
        n=b+h-1;p=coefficients(a,b,n,m,w);r=a+b
        D=choose(n,b)*choose(m,a-1)
        gap=(r-1)*p[-2]**2-2*r*p[-3]*p[-1]
        assert gap==factor*D*D*w**(2*b-2)*val<0
        witnesses.append({'a':a,'b':b,'n':n,'m':m,'alpha_infinity':str(A),
            'quadratic':poly,'positive_factor':str(factor),'first_integer_weight':w,
            'previous_value':prev,'first_negative_value':val,'vertices':r+n+m,
            'edges':a*b+n*b+a*m,'failing_indices':[k for k in range(1,r)
             if k*(r-k)*p[k]**2-(k+1)*(r-k+1)*p[k-1]*p[k+1]<0]})
    out={'pairs':len(records),'integer_values':2237,'maximum_tail_cutoff':10,
         'rank_minima':rank_minima,'negative_cases':negative,'records':records}
    (HERE/'data').mkdir(exist_ok=True)
    (HERE/'data'/'rank_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
    (HERE/'data'/'verification.json').write_text(json.dumps({
         'rational_regression_checks':160,'witnesses':witnesses},indent=2)+'\n')
    print('PASS: 2237 exact cubic values, 160 full-sum regressions, both rank-38 thresholds')
    print('Witnesses:',[(z['vertices'],z['first_integer_weight'],z['failing_indices']) for z in witnesses])

if __name__=='__main__':main()
