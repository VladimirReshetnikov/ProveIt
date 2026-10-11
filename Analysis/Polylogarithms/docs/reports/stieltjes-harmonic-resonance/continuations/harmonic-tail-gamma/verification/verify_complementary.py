"""Checks the all-gap complementary determinant, beyond its gap-four case."""
import json
from pathlib import Path
import sympy as s


def falling(n,k):
    return s.prod(range(n-k+1,n+1)) if n>=k else s.Integer(0)


def matrix(a,b):
    def entry(r,k):
        ell=r+k-a+1
        if ell<0:return s.Integer(0)
        mu=s.bernoulli(2*ell)/s.factorial(2*ell)
        value=s.factorial(2*b+2*r-2*a+1)/s.factorial(2*b-2*k)
        if k<a:
            value+=s.factorial(2*r+1)/s.factorial(2*a-2*k)
        return mu*value
    return s.Matrix(b,b,entry)


def recurrence(m,N):
    C={n:s.eye(m)[n-1,:] for n in range(1,m+1)}
    for n in range(m+1,N+1):
        B=falling(2*n-1,2*m)
        d=2*(falling(2*n,2*m)+B)
        C[n]=s.zeros(1,m)
        for r in range(1,n):
            beta=2*abs(s.bernoulli(2*(n-r)))/s.factorial(2*(n-r))
            A=falling(2*r,2*m) if r>m else s.Integer(0)
            C[n]+=beta*(A+B)*C[r]/d
    return C


def main():
    checks=0
    determinants=[]
    for b in range(2,11):
        for a in range(1,b):
            m=b-a
            C=recurrence(m,b+m)
            end=s.Matrix.vstack(*(C[b+i] for i in range(1,m+1)))
            minor=end.det(method='domain-ge')
            factor=s.prod(2*(falling(2*n,2*m)+falling(2*n-1,2*m))
                          for n in range(m+1,b+m+1))/(4**b*s.factorial(b))
            M=matrix(a,b)
            value=M.det(method='domain-ge')
            assert value==(-1)**(b*(b-1)//2)*factor*minor
            checks+=1
            determinants.append({'p':2*a,'q':2*b,'m':m,
                                 'matrix_det':str(value),'endpoint_det':str(minor)})
    ratio_checks=0
    for m in range(2,6):
        C=recurrence(m,m+8)
        for i in range(m):
            for j in range(i+1,m):
                for n in range(m+1,m+8):
                    assert C[n][i]*C[n+1][j]-C[n][j]*C[n+1][i]<0
                    ratio_checks+=1
    out={'all_passed':True,'general_determinants':checks,
         'general_ratio_minors':ratio_checks,
         'total_checks':checks+ratio_checks,'cases':determinants}
    path=(Path(__file__).resolve().parent.parent / 'data').joinpath('complementary_verification.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2))


if __name__=='__main__':main()
