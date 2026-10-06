"""Finite exact coefficient extraction; z=sqrt(log(2)/8), s=n^(-1/4)."""
import argparse
import sympy as S

def derive(K=2):
    if isinstance(K, bool) or not isinstance(K, int) or K < 0:
        raise ValueError("order must be a nonnegative integer")
    N=2*K+5
    s,U,V=S.symbols('s U V', real=True)
    z=S.symbols('z', positive=True)
    I=S.I
    L=8*z*z
    # Laurent series ring in s; expression coefficients in z,U,V
    
    def T(x,n=N): return S.Poly(S.expand(x),s).as_dict()
    def trim(x,n=N): return S.Add(*(c*s**p[0] for p,c in T(x).items() if p[0]<n))
    def mul(x,y,n=N):
     dx,dy=T(x),T(y); out={}
     for (i,),a in dx.items():
      for (j,),b in dy.items():
       if i+j<n: out[i+j]=out.get(i+j,0)+a*b
     return S.Add(*(S.expand(c)*s**k for k,c in out.items()))
    def exp0(x,n=N):
     p=S.Integer(1); out=p
     for j in range(1,n):
      p=mul(p,x,n)/j
      if p==0: break
      out+=p
     return trim(out,n)
    def coeff(x,k): return T(x).get((k,),S.Integer(0))
    r=L-z*s*s
    m=mul(mul(r,exp0(I*U*s**3)),sum((-1)**j*(V*s*s)**(2*j)/S.factorial(2*j) for j in range(N//4+1)))
    h=mul(mul(I*r,exp0(I*U*s**3)),sum((-1)**j*(V*s*s)**(2*j+1)/S.factorial(2*j+1) for j in range(N//4+1)))
    M=m-L
    d=trim(2*mul(exp0(M),exp0(h)+exp0(-h))-4*exp0(2*M))
    # d=s²*D, reciprocal by recurrence
    D=[coeff(d,k+2) for k in range(N-2)]
    invD=[1/D[0]]
    for k in range(1,2*K+3):
     invD.append(S.expand(-sum(D[j]*invD[k-j] for j in range(1,k+1))/D[0]))
    # Pj: full exponent apart leading β/s² and -2nlogL
    P=[]
    for j in range(2*K+1):
     radial=2*(z/L)**((j+4)//2)/S.Integer((j+4)//2) if j%2==0 else 0
     P.append(S.expand(2*coeff(m,j)+invD[j+2]-(1 if j==0 else 0)+radial))
    C0=P[0].subs({U:0,V:0}); A=-P[0].coeff(U,2); B=-P[0].coeff(V,2)
    Q=[S.Integer(1)]
    for j in range(1,2*K+1):
     Q.append(S.expand(sum(k*P[k]*Q[j-k] for k in range(1,j+1))/j))
    def moment(poly):
     return S.factor(sum(c*S.factorial2(p-1)*S.factorial2(q-1)/(2*A)**(p//2)/(2*B)**(q//2) for (p,q),c in S.Poly(poly,U,V).terms() if p%2==q%2==0))

    coefficients = [S.Integer(1)] + [moment(Q[2*k]) for k in range(1,K+1)]
    return dict(z=z, U=U, V=V, A=A, B=B, gamma=C0, P=P, Q=Q, c=coefficients)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("order", nargs="?", type=int, default=2)
    args=parser.parse_args()
    if args.order < 0:
        parser.error("order must be nonnegative")
    data=derive(args.order)
    print("A",data["A"],"B",data["B"],"gamma",data["gamma"])
    for j in range(1, min(2,len(data["P"])-1)+1):
        print("P",j,S.factor(data["P"][j]))
    for k,c in enumerate(data["c"]):
        print("c",k,c)
        print("value",S.N(c.subs(data["z"],S.sqrt(S.log(2)/8)),40))

if __name__ == "__main__":
    main()
