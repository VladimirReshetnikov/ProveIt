"""Exact finite checks for the new q-p=4 theorem.

No floating-point inference is used.  The general theorem is proved in
gap_four_notes.md; these checks exercise its independently written formulas.
"""
from functools import lru_cache
from pathlib import Path
import json
import sympy as s


@lru_cache(None)
def beta(k):
    assert k >= 1
    return 2*abs(s.bernoulli(2*k))/s.factorial(2*k)


def A(r):
    return s.Integer(0) if r <= 2 else s.prod(range(2*r-3,2*r+1))


def B(n):
    return s.prod(range(2*n-4,2*n))


def d(n):
    return 16*(n-1)**2*(2*n-1)*(2*n-3)


def solutions(N):
    u={1:s.Integer(1),2:s.Integer(0)}
    v={1:s.Integer(0),2:s.Integer(1)}
    for n in range(3,N+1):
        u[n]=sum(beta(n-r)*(A(r)+B(n))*u[r] for r in range(1,n))/d(n)
        v[n]=sum(beta(n-r)*(A(r)+B(n))*v[r] for r in range(1,n))/d(n)
    return u,v


def source_matrix(b):
    p,q=2*b-4,2*b
    def entry(t,k):
        dd=2*(b+t)+1
        e=dd-p-q+2*k+1
        if e<0: return s.Integer(0)
        ans=s.Integer(0)
        for upper,lower in [(dd-q+1,p-2*k),(dd-p+1,q-2*k)]:
            if 2 <= lower <= upper:
                ans+=s.binomial(upper,lower)/upper
        return s.bernoulli(e)*ans
    return s.Matrix(b,b,entry)


def derivative_matrix(b):
    t=s.Symbol('t')
    h=2/t+sum(2*s.bernoulli(2*k)*t**(2*k-1)/s.factorial(2*k)
               for k in range(1,b+2))
    cols=[]
    for n in range(1,b+1):
        q=t**(2*n)
        q4=s.diff(q,t,4)
        out=s.expand((q4-q4.subs(t,0))*h+s.diff(q*h,t,4))
        cols.append(s.Matrix([out.coeff(t,2*r+1) for r in range(b)]))
    return s.Matrix.hstack(*cols)


def main():
    counts={"source_operator_matrix":0,"determinant":0,
            "recurrence_coefficients":0,"ratio_monotonicity":0,
            "bernoulli_log_convexity":0,"weights_decrease":0}
    u,v=solutions(24)
    for k in range(1,23):
        assert beta(k+1)**2 < beta(k)*beta(k+2)
        counts['bernoulli_log_convexity']+=1
    for n in range(3,24):
        assert u[n] > 0 and v[n] > 0
        assert u[n+1]*v[n]-u[n]*v[n+1] > 0
        counts['ratio_monotonicity']+=1
        for r in range(3,n):
            wn=beta(n-r)/beta(n-2)*(1+A(r)/B(n))
            wnext=beta(n+1-r)/beta(n-1)*(1+A(r)/B(n+1))
            assert wnext < wn
            counts['weights_decrease']+=1
    t=s.Symbol('t')
    hs=2/t+sum(2*s.bernoulli(2*k)*t**(2*k-1)/s.factorial(2*k)
                 for k in range(1,24))
    for values,offset in [(u,1),(v,2)]:
        Q=sum((-1)**(n-offset)*values[n]*t**(2*n) for n in range(1,25))
        q4=s.diff(Q,t,4)
        out=s.expand((q4-q4.subs(t,0))*hs+s.diff(Q*hs,t,4))
        for n in range(3,25):
            assert out.coeff(t,2*n-5)==0
            counts['recurrence_coefficients']+=1
    table=[]
    for b in range(3,19):
        M=source_matrix(b)
        Delta=u[b+2]*v[b+1]-u[b+1]*v[b+2]
        factor=s.prod(d(n) for n in range(3,b+3))/(4**b*s.factorial(b))
        predicted=(-1)**(b*(b-1)//2+1)*factor*Delta
        det=M.det(method='domain-ge')
        assert det==predicted
        counts['determinant']+=1
        if b<=12:
            K=derivative_matrix(b)
            lhs=s.diag(*[s.Rational(2,s.factorial(2*r+1)) for r in range(b)])
            rhs=s.diag(*[s.factorial(2*n) for n in range(1,b+1)])
            assert K==lhs*M[:,::-1]*rhs
            counts['source_operator_matrix']+=1
        table.append({'b':b,'p':2*b-4,'q':2*b,'determinant':str(det),
                      'positive_delta':str(Delta)})
    out={'description':'Exact rational diagnostic checks, distinct from the proof',
         'checks':counts,'total_checks':sum(counts.values()),'all_passed':True,
         'determinant_table':table,
         'fundamental_solutions':[
             {'n':n,'u':str(u[n]),'v':str(v[n]),'ratio':str(u[n]/v[n])}
             for n in range(3,11)]}
    path=(Path(__file__).resolve().parent.parent / 'data').joinpath('gap_four_verification.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'checks':counts,'total_checks':sum(counts.values()),
                      'all_passed':True,'results':str(path)},indent=2))


if __name__=='__main__': main()
