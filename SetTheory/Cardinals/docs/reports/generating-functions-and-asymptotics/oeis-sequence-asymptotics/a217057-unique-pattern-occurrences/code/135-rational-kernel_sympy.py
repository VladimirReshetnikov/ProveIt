"""Exact exponent checks and a factored SymPy builder for the rational CT kernel.
The contour argument is proved in Report135.pdf, not by this script.
"""
import json
import sympy as sp

def require(condition, message):
    if not condition: raise ValueError(message)


NAMES=('s','i','j','lambda1','lambda2','lambda3','mu1','mu2','mu3','nu1','nu2','nu3')

def weights(z,H,A,B,C,P,Q,T,V,U,W):
    return (z*H/(A*B*C), B*P/H, C*Q/H,
            A*T[0]*V[0], A*T[2]*V[2]/(T[1]*V[1]), A*T[4]*V[4]/(T[3]*V[3]),
            B*U[0]*T[1]/T[0], B*U[1]*T[3]/T[2], B*U[2]/T[4],
            C*W[0]*V[1]/V[0], C*W[1]*V[3]/V[2], C*W[2]/V[4])

def J(X):
    return (X[0]-X[1])*(X[0]-X[2])*(X[1]-X[2])/(X[0]**2*X[1])

def block(z,P,Q,suffix):
    A,B,C,b=sp.symbols(' '.join(n+suffix for n in ('A','B','C','b')))
    pv=sp.symbols(' '.join('p'+str(i)+suffix for i in range(1,6)))
    qv=sp.symbols(' '.join('q'+str(i)+suffix for i in range(1,6)))
    X=sp.symbols(' '.join('X'+str(i)+suffix for i in range(1,4)))
    Y=sp.symbols(' '.join('Y'+str(i)+suffix for i in range(1,4)))
    c=lambda v:(1+v)/v
    R=weights(z,c(b),A,B,C,P,Q,tuple(map(c,pv)),tuple(map(c,qv)),
              tuple(sum(X)/v for v in X),tuple(sum(Y)/v for v in Y))
    kernel=sp.Mul((1-A)/(A**2*B*C),J(X),J(Y),
                  *(sp.Pow(1-r,-1,evaluate=False) for r in R),evaluate=False)
    return kernel,(A,B,C,b)+pv+qv+X+Y,R

def build_kernel():
    """Return parameter z, 42 CT variables, and the unexpanded integrand including z^4."""
    z,xi,eta=sp.symbols('z xi eta')
    north,nvars,NR=block(z,(1+xi)/xi,(1+eta)/eta,'')
    south,svars,SR=block(z,1+xi,1+eta,'_s')
    return z,nvars+svars+(xi,eta),sp.Mul(z**4,north,south,evaluate=False)

def check_weights():
    z,H,A,B,C,P,Q=sp.symbols('z H A B C P Q',nonzero=True)
    T=sp.symbols('T1:6',nonzero=True); V=sp.symbols('V1:6',nonzero=True)
    U=sp.symbols('U1:4',nonzero=True); W=sp.symbols('W1:4',nonzero=True)
    R=weights(z,H,A,B,C,P,Q,T,V,U,W)
    def raw(a):
        s,i,j=a[:3]; la=a[3:6]; mu=a[6:9]; nu=a[9:12]
        out=z**s*H**(s-i-j)*A**(sum(la)-s)*B**(sum(mu)-s+i)*C**(sum(nu)-s+j)*P**i*Q**j
        for r in range(3):out*=U[r]**mu[r]*W[r]**nu[r]
        gaps=lambda v:(la[0]-v[0],v[0]-la[1],la[1]-v[1],v[1]-la[2],la[2]-v[2])
        for t,e in zip(T,gaps(mu)):out*=t**e
        for v,e in zip(V,gaps(nu)):out*=v**e
        return out
    require(raw([0]*12)==1, "zero exponents")
    for col in range(12):
        a=[0]*12;a[col]=1
        require(sp.cancel(R[col]/raw(a))==1, NAMES[col])
    original=sum((-1)**a*A**(-2+a)*B**(-1)*C**(-1) for a in (0,1))
    require(sp.cancel(original-(1-A)/(A**2*B*C))==0, "H factor")
    return 12

if __name__=='__main__':
    n=check_weights()
    z,ct,kernel=build_kernel()
    require(len(ct)==42 and len(set(ct))==42, "CT variables")
    require(kernel.free_symbols==set(ct)|{z}, "free symbols")
    out={'status':'PASS','independent_exponent_columns_checked':n,
         'H_difference_factorization':'PASS','constant_term_variables':42,
         'geometric_denominator_factors':24,
         'factored_sympy_operation_count':sp.count_ops(kernel),
         'scope':'Exact algebraic exponent and factor checks; not numerical 42-dimensional integration'}
    print(json.dumps(out,indent=2))

