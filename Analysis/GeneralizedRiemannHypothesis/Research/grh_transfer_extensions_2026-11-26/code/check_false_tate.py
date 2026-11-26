#!/usr/bin/env python3
"""Exact maximal monic approximants in Q_p(p^(1/p), zeta_(p^h)).

This checks pN*v(B(zeta-1)) by an integer polynomial resultant,
followed by reduction modulo the shifted cyclotomic polynomial. It
uses neither ramification filtration nor discriminant/index formulas.
SymPy is needed only for exact polynomial arithmetic.
"""
import argparse, json, time
from pathlib import Path
import sympy as sp
T, Y = sp.symbols('T Y')

def vp(x,p):
    assert x
    v=0
    while x % p == 0:
        x//=p; v+=1
    return v

def cyclotomic_shift(p,h):
    d=p**(h-1)
    return sp.Poly(sum((1+T)**(j*d) for j in range(p)),T)

class Calculator:
    def __init__(self,p,h):
        self.p,self.h=p,h
        self.N=(p-1)*p**(h-1)
        self.n=self.N//p
        self.phi=cyclotomic_shift(p,h)
        self.calls=0
    def value(self,parts):
        self.calls+=1
        expr=sum(Y**i * sum(a*T**j for j,a in enumerate(row) if a) for i,row in enumerate(parts))
        norm=sp.resultant(Y**self.p-self.p,expr,Y)
        rem=sp.rem(sp.Poly(norm,T),self.phi)
        # In the Eisenstein power basis, distinct exponents have distinct
        # valuations modulo N, so no cancellation is possible here.
        return min(j+self.N*vp(int(c),self.p) for (j,),c in rem.terms())
    def maximize(self):
        parts=[[0]*(self.n+1) for _ in range(self.p)]
        parts[0][self.n]=1
        records=[]
        r=self.value(parts)
        while r%self.p==0:
            k,j=divmod(r//self.p,self.n)
            exponent,index=divmod(k,self.p)
            step=self.p**exponent
            old=parts[index][j]
            for digit in range(1,self.p):
                parts[index][j]=old+digit*step
                s=self.value(parts)
                if s>r:
                    records.append({'old_value':r,'new_value':s,'pi_power':index,'T_power':j,'integer_coefficient_increment':digit*step})
                    r=s
                    break
            else:
                raise AssertionError('residue cancellation failed')
        expected=(2*self.p-1)*(self.p**(self.h-1)-1)
        assert r==expected,(self.p,self.h,r,expected)
        # Certificate that the constructed basis has distinct valuations
        # modulo 1/p, and that its monic elements saturate every degree.
        residues=[(self.p*j+k*r)%self.N for k in range(self.p) for j in range(self.n)]
        assert sorted(residues)==list(range(self.N))
        delta=sp.Rational(r,self.p*self.N)-sp.Rational(1,self.p)
        return {'p':self.p,'h':self.h,'N':self.N,'n':self.n,'scaled_value':r,
                'valuation':str(sp.Rational(r,self.p*self.N)),'delta':str(delta),
                'coefficients_in_pi_power_basis':parts,'corrections':records,
                'distinct_residues_verified':True,'norm_calls':self.calls}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--cases', default='3:2,3:3,3:4,5:2,5:3,7:2')
    parser.add_argument('--output',default=str(Path(__file__).resolve().parents[1] / 'data' / 'false_tate_certificates.json'))
    args=parser.parse_args()
    out=[]
    for pair in args.cases.split(','):
        p,h=map(int,pair.split(':'))
        assert sp.isprime(p) and p>2 and h>=2
        start=time.monotonic()
        result=Calculator(p,h).maximize()
        result['elapsed_seconds']=round(time.monotonic()-start,3)
        out.append(result)
        print(f'p={p}, h={h}, N={result["N"]}, pN*v={result["scaled_value"]}, delta={result["delta"]}, calls={result["norm_calls"]}',flush=True)
        Path(args.output).write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__': main()
