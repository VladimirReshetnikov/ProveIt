"""Small arithmetic coordinate spaces obtained from the all-power generator."""
from pathlib import Path
from math import comb, factorial
import json
import sympy as s

Q7,Q5,Z2,Z3,Z4,K8,Z6,R11,K9,J7=s.symbols('Q7 Q5 Z2 Z3 Z4 K8 Z6 R11 K9 J7')

def generate(order=36):
    H={};G={}
    def integ(f,k): return [s.S.Zero]*k+f[:order+1-k]
    def mulcosh(f):
        return [s.expand(sum(s.binomial(n,j)*s.Rational(1,2)**j*f[n-j]
                             for j in range(0,n+1,2))) for n in range(order+1)]
    def add(*terms):
        return [s.expand(sum(c*f[n] for c,f in terms)) for n in range(order+1)]
    def poly(terms):
        a=[s.S.Zero]*(order+1)
        for k,v in terms.items():
            if k<=order:a[k]=s.factorial(k)*v
        return a
    def setrow(d,values):
        H[d]=values; g=[s.S.Zero]*(order+1)
        for m in range(d%2,order,2):
            g[m]=s.expand((values[m+1]-sum(s.binomial(m+1,j)*2**s.Integer(1-j)*g[m+1-j]
                                      for j in range(3,m+2,2)))/(m+1))
        G[d]=g
    setrow(1,poly({2:-s.Rational(1,4)}))
    setrow(2,add((1,poly({1:3*Z3})),(2,integ(mulcosh(G[1]),2))))
    setrow(3,add((3,integ(mulcosh(G[2]),2)),
                 (1,poly({2:-s.Rational(17,8)*Z4,4:-Z2/48,6:s.Rational(1,2880)}))))
    setrow(4,add((4,integ(mulcosh(G[3]),2)),(-1,integ(H[2],4)),
                 (1,poly({1:Q7,3:Q5/6}))))
    setrow(5,add((5,integ(mulcosh(G[4]),2)),(-s.Rational(5,3),integ(H[3],4)),
                 (1,poly({2:-K8,4:-s.Rational(19,64)*Z6,6:Z4/4320,
                          8:Z2/241920,10:-s.Rational(1,43545600)}))))
    setrow(6,add((6,integ(mulcosh(G[5]),2)),(-s.Rational(5,2),integ(H[4],4)),
                 (s.Rational(1,2),integ(H[2],8)),
                 (1,poly({1:R11,3:K9/12,5:J7/240,7:-Q5/10080}))))
    return H,G

def main():
    H,G=generate()
    coords={5:[K8,Z6,Q7,Q5,Z2,Z3,Z4,s.S.One],
            6:[R11,K9,J7,K8,Z6,Q7,Q5,Z2,Z3,Z4,s.S.One]}
    results={}
    for d,cs in coords.items():
        ms=list(range(d%2,2*len(cs),2))
        rows=[G[d][m] for m in ms]
        mat=s.Matrix([[s.expand(row).coeff(c) if c!=1 else s.expand(row).subs({x:0 for x in cs if x!=1})
                       for c in cs] for row in rows])
        det=s.factor(mat.det())
        print('d',d,'coordinates',len(cs),'determinant',det)
        assert det!=0
        # Exact rational elimination: a polynomial times A_n^d evaluates to 1.
        target=s.zeros(len(cs),1);target[-1]=1
        coeffs=mat.T.inv()*target
        den=s.ilcm(*[s.denom(x) for x in coeffs])
        ints=[int(x*den) for x in coeffs]
        divisor=s.igcd(*ints)
        ints=[x//int(divisor) for x in ints]
        rational=s.Rational(den,divisor)
        results[str(d)]={'coordinates':[str(c) for c in cs], 'exponents':ms,
                        'rows':[str(x) for x in rows], 'matrix':[[str(x) for x in row] for row in mat.tolist()],
                        'determinant':str(det),'rational_extraction':{'coefficients':ints,'value':str(rational)}}
        print('first row:',rows[0])
    Path(__file__).with_name('quintic_sextic_coordinates.json').write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':main()
