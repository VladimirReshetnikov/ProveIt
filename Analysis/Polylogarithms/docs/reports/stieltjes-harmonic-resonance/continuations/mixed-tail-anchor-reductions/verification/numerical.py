"""Independent high-precision diagnostics; these are not interval certificates."""
from pathlib import Path
from functools import lru_cache
import json
import mpmath as mp
import sympy as sp
from reduce_values import reduce, mixed_moment, Z
ROOT=Path(__file__).resolve().parents[1]

@lru_cache(None)
def centered_coefficients(ps,K):
    out=[sp.Integer(1)]+[sp.Integer(0)]*(K-1)
    for p in ps:
        eta=[sp.Rational(1,p-1)]+[sp.rf(p,2*j-1)*sp.bernoulli(2*j,sp.Rational(1,2))/sp.factorial(2*j) for j in range(1,K)]
        out=[sum(out[j]*eta[k-j] for j in range(k+1)) for k in range(K)]
    return tuple(out)

def mpq(q):
    a,b=sp.fraction(q);return mp.mpf(int(a))/int(b)

@lru_cache(None)
def finite_tail_values(p,N,dps):
    # Direct recurrence from zeta(p), with precision included in the cache key.
    with mp.workdps(dps):
        value=mp.zeta(p); out=[]
        for n in range(N+1):
            out.append(+value)
            value-=mp.mpf(n+1)**(-p)
        return tuple(out)

def tail_moment(ps,m,N=80,K=28):
    R=sum(p-1 for p in ps);cs=centered_coefficients(tuple(ps),K)
    low=max(0,(m-R)//2+1)
    finite=mp.fsum((mp.mpf(n)+mp.mpf('.5'))**m*mp.fprod(finite_tail_values(p,N,mp.mp.dps)[n] for p in ps)
      -mp.fsum(mpq(cs[j])*(mp.mpf(n)+mp.mpf('.5'))**(m-R-2*j) for j in range(low))
      for n in range(N))
    tail=mp.fsum(mpq(cs[j])*mp.zeta(R+2*j-m,mp.mpf(N)+mp.mpf('.5')) for j in range(low,K))
    return finite+tail

def zeta53(N=80,K=28):
    finite=mp.fsum((mp.zeta(3)-finite_tail_values(3,N,mp.mp.dps)[n-1])/mp.mpf(n)**5 for n in range(1,N))
    tail=mp.zeta(3)*mp.zeta(5,N)-mp.zeta(7,N)/2-mp.zeta(8,N)/2
    tail-=mp.fsum(mpq(sp.bernoulli(2*j)*sp.rf(3,2*j-1)/sp.factorial(2*j))*mp.zeta(7+2*j,N) for j in range(1,K))
    return finite+tail

@lru_cache(None)
def drop_coefficients(d,h,K):
    # A_{n-1}=zeta(2,n)=u+u^2/2+sum B_{2j}u^{2j+1}.
    # A_n has -u^2/2 instead. Rational convolution avoids symbolic series.
    a=[sp.Integer(0)]*(K+1);a[1]=sp.Integer(1);a[2]=sp.Rational(1,2)
    for j in range(1,(K-1)//2+1):a[2*j+1]=sp.bernoulli(2*j)
    b=a.copy();b[2]=-b[2]
    def power(v):
        out=[sp.Integer(1)]+[sp.Integer(0)]*K
        for _ in range(d):out=[sum(out[j]*v[k-j] for j in range(k+1)) for k in range(K+1)]
        return out
    aa,bb=power(a),power(b)
    return tuple((k-h,aa[k]-bb[k]) for k in range(K+1) if aa[k]!=bb[k])

def anchor_sum(d,h,N=80,K=58):
    finite=mp.fsum(mp.mpf(n)**h*(finite_tail_values(2,N,mp.mp.dps)[n-1]**d-finite_tail_values(2,N,mp.mp.dps)[n]**d) for n in range(1,N))
    return finite+mp.fsum(mpq(c)*mp.zeta(q,N) for q,c in drop_coefficients(d,h,K))

def eval_expression(expr,z53=None):
    vals={}
    for symbol in expr.free_symbols:
        w=tuple(map(int,str(symbol)[2:].split('_')))
        if len(w)==1:vals[symbol]=mp.zeta(w[0])
        elif w==(5,3):vals[symbol]=zeta53() if z53 is None else z53
        else:raise ValueError(f'Unsupported numerical MZV {w}')
    return mp.fsum(mpq(term.as_coeff_Mul()[0])*mp.fprod((mp.mpf(1) if b==1 else vals[b])**int(e) for b,e in term.as_coeff_Mul()[1].as_powers_dict().items())
                   for term in sp.Add.make_args(sp.expand(expr)))

def run():
    mp.mp.dps=90; records=[]
    def check(name,left,right,tol=mp.mpf('1e-55')):
        err=abs(left-right); assert err<tol,(name,mp.nstr(err,10))
        records.append({'name':name,'left':mp.nstr(left,68),'right':mp.nstr(right,68),'absolute_residual':mp.nstr(err,8),'tolerance':str(tol)})
    z53=zeta53()
    check('zeta53 two truncations',z53,zeta53(110,33))
    z=lambda n:mp.zeta(n)
    k8=10*z(2)*z(3)**2-50*z(3)*z(5)-10*z53+mp.mpf(4927)/96*z(8)
    j7=-8*z(2)*z(5)-4*z(3)*z(4)+21*z(7)
    k9=-222*z(2)*z(7)+171*z(3)*z(6)-858*z(4)*z(5)+1086*z(9)
    check('K8 drop sum',mp.mpf(5)/6*anchor_sum(3,-2)+mp.mpf(289)/32*z(8),k8)
    check('J7 drop sum',anchor_sum(2,-3),j7)
    check('K9 drop sum',anchor_sum(2,-5)-5*anchor_sum(4,-1),k9)
    examples=[((2,3),1),((2,3),3),((2,3),5),((2,2,3),0),((2,2,3),2),((2,2,3),4),((3,3),0),((3,3),2),((3,3),4),((2,3,4),0),((2,3,4),2),((2,3,4),4),((2,)*5,1),((2,)*5,3),((2,)*5,5)]
    for ps,m in examples:
        rhs=eval_expression(reduce(mixed_moment(ps,m)),z53)
        val=tail_moment(ps,m)
        check(f'moment {ps} m={m}',val,rhs)
        check(f'moment truncations {ps} m={m}',val,tail_moment(ps,m,110,33))
    check('rational -15 mixed sum',23*tail_moment((2,3),1)+232*tail_moment((2,3),3)+240*tail_moment((2,3),5),mp.mpf(-15))
    # Exact finite-cutoff identities, tested numerically with independent special functions.
    ps=(2,3);a=mp.mpf('0.7');b=mp.mpf('1.4');N=4
    T=lambda n:mp.zeta(2,n+1)*mp.zeta(3,n+1)
    D=lambda n:T(n-1)-T(n)
    for q in range(3):
        left=mp.fsum(D(n)*mp.stieltjes(q,n+a) for n in range(1,N+1))
        right=T(0)*mp.stieltjes(q,a)-mp.fsum(T(k)*mp.log(k+a)**q/(k+a) for k in range(N))-T(N)*mp.stieltjes(q,N+a)
        check(f'finite Stieltjes transport q={q}',left,right,mp.mpf('1e-75'))
    f=lambda y:mp.loggamma(y+b)-mp.loggamma(y+a)
    check('finite Gamma transport',mp.fsum(D(n)*f(n) for n in range(1,N+1)),T(0)*f(0)+mp.fsum(T(k)*mp.log((k+b)/(k+a)) for k in range(N))-T(N)*f(N),mp.mpf('1e-75'))
    # A one-tail polylogarithm integral, E_(2)(1)=2*zeta(3).
    kernel=lambda t:(mp.zeta(2)-mp.polylog(2,mp.exp(-t)))/mp.expm1(t)
    integral=mp.quad(kernel,[0,1,5,mp.inf])
    check('polylog E2(1) integral',integral,2*mp.zeta(3),mp.mpf('1e-75'))
    result={'status':'passed','working_decimal_digits':mp.mp.dps,'diagnostic_only':True,'number_of_checks':len(records),'checks':records}
    (ROOT/'results'/'numerical.json').write_text(json.dumps(result,indent=2))
    print('Numerical diagnostics passed:',len(records),flush=True)
    return result
if __name__=='__main__':run()
