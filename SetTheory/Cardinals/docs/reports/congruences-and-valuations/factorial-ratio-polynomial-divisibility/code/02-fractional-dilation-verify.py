#!/usr/bin/env python3
"""Exact certificates for the accompanying fractional-factorial article.

Python >= 3.10, standard library only. No network access or floating point.
Run: python verify.py --max-n 200 --output results.txt
Finite floor partitions and Gram identities are certificates for the reductions
proved in the article. Term tests are cross-checks, not proofs for arbitrary n.
This is not a proof-assistant kernel or an independent formalization.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import sys
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from typing import Sequence

@dataclass(frozen=True)
class Row:
    oeis: str
    L: int
    A: int
    B: int
    m: int
    c: int
    d: int
    base: str
    prefix: tuple[int, ...]

ROWS = (
    Row('A347854',6,3,2,1,1,2,'I',(1,40,4620,622336,89237148,13236695040)),
    Row('A347855',4,2,1,1,1,3,'I',(1,9,189,4620,120285,3241134)),
    Row('A347856',6,4,1,1,1,2,'II',(1,20,990,56576,3432198,215147520)),
    Row('A347857',6,3,2,1,3,2,'III',(1,24,1386,91392,6374082,458625024)),
    Row('A347858',9,3,2,4,1,2,'IV',(1,512,1021020,2399141888,6016814703900,15626259253952512)),
)
# Polynomial coefficients are in increasing order, including the leading 1.
BASES = {
 'I': dict(num=[12,1],den=[6,4,3],lam=F(27648),
   alpha=['1/12','5/12','7/12','11/12'],beta=['1/3','1/2','2/3','1'],
   f=[1,0,-1,0,1],g=[-1,-1,0,1,1],
   H=[[2,-1,1,0],[-1,2,-1,1],[1,-1,2,-1],[0,1,-1,2]],
   minors=[2,3,4,4],M=12),
 'II': dict(num=[12,1],den=[8,2,3],lam=F(19683,4),
   alpha=['1/12','1/6','5/12','7/12','5/6','11/12'],
   beta=['1/8','3/8','1/2','5/8','7/8','1'],
   f=[1,-1,0,1,0,-1,1],g=[-1,0,1,0,-1,0,1],
   H=[[4,2,1,-1,-2,-1],[2,4,2,1,-1,-2],[1,2,4,2,1,-1],
      [-1,1,2,4,2,1],[-2,-1,1,2,4,2],[-1,-2,-1,1,2,4]],
   minors=[4,12,36,81,162,243],M=24),
 'III': dict(num=[12,3],den=[6,4,5],lam=F(2**10*3**9,5**5),
   alpha=['1/12','1/3','5/12','7/12','2/3','11/12'],
   beta=['1/5','2/5','1/2','3/5','4/5','1'],
   f=[1,1,0,-1,0,1,1],g=[-1,-1,0,0,0,1,1],
   H=[[10,-8,4,1,-5,7],[-8,10,-8,4,1,-5],[4,-8,10,-8,4,1],
      [1,4,-8,10,-8,4],[-5,1,4,-8,10,-8],[7,-5,1,4,-8,10]],
   minors=[10,36,72,108,162,243],M=60),
 'IV': dict(num=[18,1],den=[6,4,9],lam=F(2**4*3**12),
   alpha=['1/18','5/18','7/18','11/18','13/18','17/18'],
   beta=['1/4','1/3','1/2','2/3','3/4','1'],
   f=[1,0,0,-1,0,0,1],g=[-1,-1,-1,0,1,1,1],
   H=[[4,-1,-2,2,1,-1],[-1,4,-1,-2,2,1],[-2,-1,4,-1,-2,2],
      [2,-2,-1,4,-1,-2],[1,2,-2,-1,4,-1],[-1,1,2,-2,-1,4]],
   minors=[4,15,36,81,162,243],M=36)
}
EXPECTED = {
 'A347854': [['1/6:2/3','5/6:1'],['1/6:1/3','5/6:1']],
 'A347855': [['1/4:1'],['3/4:1'],['1/4:1/2','3/4:1']],
 'A347856': [['1/6:1/4','1/3:3/4','5/6:1'],['1/6:1/4','2/3:3/4','5/6:1']],
 'A347857': [['1/6:2/5','2/3:4/5','5/6:1'],['1/6:1/5','1/3:3/5','5/6:1']],
 'A347858': [['1/9:1/2','5/9:2/3','7/9:1'],['2/9:1/3','4/9:1/2','8/9:1']],
}

def require(test: bool, message: str) -> None:
    if not test:
        raise AssertionError(message)

def value(row: Row, n: int) -> F:
    if n < 0:
        raise ValueError('n must be nonnegative')
    numer = row.d**(row.m*n) * math.factorial(row.L*n)
    denom = math.factorial(row.A*n)*math.factorial(row.B*n)
    denom *= math.prod(row.c*n+row.d*j for j in range(1,row.m*n+1))
    return F(numer,denom)

def ordinary(row: Row, n: int) -> F:
    return F(math.factorial(row.d*row.L*n)*math.factorial(row.c*n),
             math.factorial(row.d*row.A*n)*math.factorial(row.d*row.B*n)*
             math.factorial((row.c+row.d*row.m)*n))

def floor_data(row: Row, shift: int) -> list[tuple[int,F,F]]:
    return [(1,F(row.L),F(0)),(-1,F(row.A),F(0)),(-1,F(row.B),F(0)),
            (-1,F(row.c+row.d*row.m,row.d),F(-shift,row.d)),
            (1,F(row.c,row.d),F(-shift,row.d))]

def floor_sum(row: Row, shift: int, x: F) -> int:
    return sum(sign*math.floor(a*x+b) for sign,a,b in floor_data(row,shift))

def breakpoints(row: Row, shift: int) -> list[F]:
    pts={F(0),F(1)}
    for _,a,b in floor_data(row,shift):
        for k in range(math.floor(b)-1,math.ceil(a+b)+2):
            x=(k-b)/a
            if 0 <= x <= 1:
                pts.add(x)
    return sorted(pts)

def floor_certificate(row: Row, shift: int) -> tuple[list[tuple[F,F]],int]:
    pts=breakpoints(row,shift)
    ones=[]
    for left,right in zip(pts,pts[1:]):
        val=floor_sum(row,shift,left)
        require(val in (0,1),'floor value outside {0,1}')
        require(floor_sum(row,shift,(left+right)/2)==val,'endpoint convention')
        if val:
            if ones and ones[-1][1]==left:
                ones[-1]=(ones[-1][0],right)
            else:
                ones.append((left,right))
    expected=[tuple(F(x) for x in item.split(':')) for item in EXPECTED[row.oeis][shift]]
    require(ones==expected,f'printed floor table mismatch {row.oeis}:{shift}')
    return ones,len(pts)-1

def v_int(n: int,p: int) -> int:
    if n<=0:
        raise ValueError('valuation requires a positive integer')
    result=0
    while n%p==0:
        result+=1
        n//=p
    return result

def v_rat(x: F,p: int) -> int:
    return v_int(x.numerator,p)-v_int(x.denominator,p)

def predicted_v(row: Row,n: int,p: int) -> int:
    require(row.d%p != 0,'use only primes coprime to denominator')
    result=0
    q=p
    while q<=max(row.L,row.c+row.d*row.m)*n:
        r=n%q
        shift=(row.c*r*pow(q,-1,row.d))%row.d if row.d>1 else 0
        result+=floor_sum(row,shift,F(r,q))
        q*=p
    return result

def transpose(A):
    return [list(row) for row in zip(*A)]

def mul(A,B):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]

def determinant(A) -> F:
    n=len(A)
    B=[[F(x) for x in row] for row in A]
    det=F(1)
    for i in range(n):
        pivot=next((j for j in range(i,n) if B[j][i]),None)
        if pivot is None:
            return F(0)
        if pivot!=i:
            B[i],B[pivot]=B[pivot],B[i]
            det=-det
        t=B[i][i]
        det*=t
        for j in range(i+1,n):
            fac=B[j][i]/t
            for k in range(i+1,n):
                B[j][k]-=fac*B[i][k]
            B[j][i]=F(0)
    return det

def companion(poly: Sequence[int]):
    n=len(poly)-1
    require(poly[-1]==1,'monic polynomial required')
    A=[[0]*n for _ in range(n)]
    for i in range(1,n):
        A[i][i-1]=1
    for i in range(n):
        A[i][-1]=-poly[i]
    return A

def expand_roots(slopes: list[int]) -> list[F]:
    return sorted(F(j,a) for a in slopes for j in range(1,a+1))

def poly_trim(a):
    a=[F(x) for x in a]
    while len(a)>1 and a[-1]==0:
        a.pop()
    return a

def poly_mul(a,b):
    result=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            result[i+j]+=x*y
    return poly_trim(result)

def poly_div(a,b):
    a=poly_trim(a); b=poly_trim(b)
    require(b!=[0],'polynomial division by zero')
    q=[F(0)]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        k=len(a)-len(b);t=a[-1]/b[-1];q[k]+=t
        for j,x in enumerate(b):
            a[j+k]-=t*x
        a=poly_trim(a)
    return poly_trim(q),a

def poly_gcd(a,b):
    while b!=[0]:
        _,r=poly_div(a,b);a,b=b,r
    return [x/a[-1] for x in a]

def cyclotomic_quotient(num,den):
    a,b=[F(1)],[F(1)]
    for k in num:
        a=poly_mul(a,[-1]+[0]*(k-1)+[1])
    for k in den:
        b=poly_mul(b,[-1]+[0]*(k-1)+[1])
    common=poly_gcd(a,b)
    f,r=poly_div(a,common);g,s=poly_div(b,common)
    require(r==[0] and s==[0],'polynomial cancellation')
    return f,g

def verify_base(name: str, b: dict) -> None:
    f,g=cyclotomic_quotient(b['num'],b['den'])
    require(f==b['f'] and g==b['g'],'cyclotomic companion polynomials')
    alpha,beta=expand_roots(b['num']),expand_roots(b['den'])
    for a in alpha[:]:
        if a in beta:
            alpha.remove(a)
            beta.remove(a)
    require(alpha==list(map(F,b['alpha'])),'alpha mismatch')
    require(beta==list(map(F,b['beta'])),'beta mismatch')
    lam=F(math.prod(a**a for a in b['num']),math.prod(a**a for a in b['den']))
    require(lam==b['lam'],'lambda mismatch')
    require(len(alpha)==len(beta),'rank mismatch')
    require(all(a<z for a,z in zip(alpha,beta)),'beta-product positivity')
    require(sum(beta)-sum(alpha)==F(1,2),'height-one parameter excess')
    M=b['M']
    for unit in range(1,M):
        if math.gcd(unit,M)==1:
            aa=sorted((unit*x)%1 for x in alpha)
            bb=sorted((unit*x)%1 or F(1) for x in beta)
            require(aa==alpha and bb==beta,'Galois invariance')
            require(all(aa[i]<bb[i] for i in range(len(aa))),'interlacing upper')
            require(all(bb[i]<aa[i+1] for i in range(len(aa)-1)),'interlacing lower')
    H=b['H']
    require(H==transpose(H),'H is not symmetric')
    minors=[determinant([row[:k] for row in H[:k]]) for k in range(1,len(H)+1)]
    require(minors==b['minors'] and all(x>0 for x in minors),'positive definiteness')
    for poly in (b['f'],b['g']):
        C=companion(poly)
        require(abs(determinant(C))==1,'not unimodular')
        require(mul(mul(transpose(C),H),C)==H,'Gram invariance')
    # Values of the rational ratio at many rational points supplement exact
    # root-list and leading-constant matching above, which is the identity proof.
    for t in (F(0),F(1,2),F(1,3),F(2,3),F(7,4)):
        direct=F(math.prod(F(a*t+j) for a in b['num'] for j in range(1,a+1)),
                 math.prod(F(a*t+j) for a in b['den'] for j in range(1,a+1)))
        hyper=lam*math.prod(t+a for a in alpha)/math.prod(t+z for z in beta)
        require(direct==hyper,'hypergeometric recurrence')

def verify(max_n: int, root: Path) -> list[str]:
    logs=['Exact verification for Fractional-factorial theorems',
          'Arithmetic is integer/rational only. No network or floating point.']
    cert={}
    primes=[p for p in range(2,100) if all(p%d for d in range(2,math.isqrt(p)+1))]
    valuations=0
    term_rows=[]
    for row in ROWS:
        require(row.L==row.A+row.B+row.m and math.gcd(row.c,row.d)==1,'parameter constraints')
        b=BASES[row.base]
        require(sorted([row.d*row.L,row.c])==sorted(b['num']),'base numerator')
        require(sorted([row.d*row.A,row.d*row.B,row.c+row.d*row.m])==sorted(b['den']),'base denominator')
        cert[row.oeis]={}
        for shift in range(row.d):
            intervals,count=floor_certificate(row,shift)
            cert[row.oeis][str(shift)]={'cells':count,'one_intervals':[[str(a),str(b)] for a,b in intervals]}
        for n in range(max_n+1):
            a=value(row,n)
            require(a.denominator==1,'nonintegral term')
            if n < len(row.prefix):
                require(a==row.prefix[n],'OEIS prefix mismatch')
            if n%row.d==0:
                require(a==ordinary(row,n//row.d),'ordinary subsequence mismatch')
            if n%row.d:
                require((a/row.d**(row.m*n)).denominator==1,'denominator-prime refinement')
            if n<=50:
                term_rows.append([row.oeis,n,a.numerator])
                for p in primes:
                    if row.d%p:
                        require(v_rat(a,p)==predicted_v(row,n,p),'valuation formula')
                        valuations+=1
            if row.oeis=='A347854' and n>=1:
                require((a/(6*n-1)).denominator==1,'linear-factor divisibility')
                if n%2:
                    require(v_rat(a,2)==2*n+n.bit_count(),'exact binary valuation')
                    require((a/F(2**(2*n+1)*(6*n-1))).denominator==1,'odd refined quotient')
        for r in range(row.d):
            require(1-F(r,row.d) in map(F,b['beta']),'missing Frobenius exponent')
        logs.append(f'{row.oeis}: all floor cells certified; n=0..{max_n} integral; prefix and refinements agree.')
    for name,b in BASES.items():
        verify_base(name,b)
        logs.append(f'Base {name}: exact parameters, Galois interlacing, two Gram identities; minors {b["minors"]}.')
    # A295432 identity in the refinement, checked independently as rational arithmetic.
    for n in range(min(max_n,100)+1):
        B=F(math.factorial(12*n)*math.factorial(3*n)*math.factorial(2*n),
            math.factorial(6*n)**2*math.factorial(4*n)*math.factorial(n))
        q=F(12*n+1,(2*n+1)*(6*n+1))*B
        require(q.denominator==1,'A295432 refined integrality')
        require(value(ROWS[0],2*n+1)==2**(4*n+3)*(12*n+5)*q,'A295432 identity')
    # Ordinary step functions: all their breakpoints lie on the 1/12 grid.
    for numerator,denominator,ones in (
        ([12,1],[6,4,3],{1,2,3,5,7,11}),
        ([12,3,2],[6,6,4,1],{1,5,7,8,9,11})):
        for j in range(12):
            for x in (F(j,12),F(2*j+1,24)):
                step=sum(math.floor(a*x) for a in numerator)-sum(math.floor(a*x) for a in denominator)
                require(step==int(j in ones),'ordinary floor partition')
    # General valuation identities, including composite denominators. No
    # integrality assumption is used in these identity checks.
    general_count=0
    for d in range(1,13):
        for c in range(1,d+1):
            if math.gcd(c,d)!=1:
                continue
            rr=Row('general',4,2,1,1,c,d,'',())
            for n in range(1,21):
                a=value(rr,n)
                for p in primes[:10]:
                    if d%p:
                        pred=predicted_v(rr,n,p)
                    else:
                        e=v_int(d,p);h=v_int(n,p)
                        if h<e:
                            T=F(math.factorial(rr.L*n),math.factorial(rr.A*n)*math.factorial(rr.B*n))
                            pred=rr.m*n*(e-h)+v_rat(T,p)
                        else:
                            pe=p**e
                            reduced=Row('reduced',pe*rr.L,pe*rr.A,pe*rr.B,pe*rr.m,c,d//pe,'',())
                            require(a==value(reduced,n//pe),'denominator prime-power reduction')
                            pred=predicted_v(reduced,n//pe,p)
                    require(v_rat(a,p)==pred,'general/composite valuation identity')
                    general_count+=1
    logs.append(f'{general_count} general valuation identities passed, including composite denominators d<=12.')
    # Additional denominator-clearing conjectures in A295431 and A295432.
    for n in range(max_n+1):
        U=ordinary(ROWS[0],n)
        for multiplier,denominator in (
            (385,n+1),(5,2*n+1),(1,3*n+1),
            (770,(n+1)*(2*n+1)*(3*n+1)),(1,12*n-1)):
            require((multiplier*U/denominator).denominator==1,'A295431 sharp displayed multiplier')
        if n>=1:
            B=F(math.factorial(12*n)*math.factorial(3*n)*math.factorial(2*n),
                math.factorial(6*n)**2*math.factorial(4*n)*math.factorial(n))
            require((B/(6*(6*n+1)*(12*n-1))).denominator==1,'A295432 product divisibility')
    for r in range(1,9):
        L=math.lcm(*range(1,12*r+1))
        D=math.lcm(*range(1,r+1))**r
        for n in range(31):
            U=ordinary(ROWS[0],n)
            for k in (1,2,3):
                C=(k*L)**r
                den=math.prod(k*n+i for i in range(1,r+1))
                require((C*U/den).denominator==1,'A295431 C(k,r) family')
            den=math.prod(12*n-i for i in range(1,r+1) if math.gcd(i,12)==1)
            require((D*U/den).denominator==1,'A295431 D(r) family')
    logs.append('A295431 displayed multipliers and A295432 product divisibility checked through max-n.')
    logs.append('Two explicit denominator-clearing families checked for r=1..8 and n=0..30.')
    logs.append(f'{valuations} exact prime-valuation cross-checks passed (p < 100, n <= 50).')
    logs.append('A295432 odd-subsequence identity and refinement verified through n=100 (or max-n).')
    with (root/'floor_certificates.json').open('w') as out:
        json.dump(cert,out,indent=2)
        out.write('\n')
    with (root/'terms.csv').open('w',newline='') as out:
        w=csv.writer(out);w.writerow(['OEIS','n','a(n)']);w.writerows(term_rows)
    logs.append('ALL CHECKS PASSED.')
    logs.append('Universal claims rely on the proved reductions in article.tex, not on term sampling.')
    return logs

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=200)
    parser.add_argument('--output',default='results.txt')
    args=parser.parse_args()
    if args.max_n<6:
        parser.error('--max-n must be at least 6')
    if hasattr(sys,'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    root=Path(__file__).resolve().parent
    logs=verify(args.max_n,root)
    text='\n'.join(logs)+'\n'
    output=Path(args.output)
    if not output.is_absolute():
        output=root/output
    output.write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()
