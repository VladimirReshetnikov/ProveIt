"""Independent endpoint-state DP for the connected hybrid graph.
This does not use Hall-subset testing or the author's type-profile formula.
"""
from itertools import combinations
from math import comb,prod
from fractions import Fraction as F
from pathlib import Path
import json
CORE=[2,1,0]
RIGHT=[(1,F(15)),(2,F(15)),(4,F(15))]+[(3,F(1))]*7+[(5,F(1,10))]
NLEFT=8

def match(rows,n):
    states={0}
    for row in sorted(rows,key=int.bit_count):
        nxt=set()
        for used in states:
            avail=row & ~used
            while avail:
                bit=avail & -avail
                avail-=bit
                nxt.add(used|bit)
        states=nxt
        if not states:return False
    return (1<<n)-1 in states

p=[[F(0) for b in range(4)] for k in range(7)]
for b in range(4):
    for B in combinations(range(3),b):
        for r in range(4):
            k=b+r
            for J in combinations(range(len(RIGHT)),r):
                activity=prod(RIGHT[j][1] for j in J)
                for aset in range(8):
                    ell=k-aset.bit_count()
                    if not 0<=ell<=b:continue
                    rows=[(1<<b)-1]*ell
                    for a in range(3):
                        if aset>>a&1:
                            row=sum(1<<i for i,Bi in enumerate(B) if CORE[a]>>Bi&1)
                            row+=sum(1<<(b+i) for i,j in enumerate(J) if RIGHT[j][0]>>a&1)
                            rows.append(row)
                    if match(rows,k):p[k][b]+=comb(NLEFT,ell)*activity

def conv(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out

gaps=[]
for k in range(1,6):
    aa=conv(p[k],p[k]);bb=conv(p[k-1],p[k+1])
    gaps.append([k*(6-k)*x-(k+1)*(7-k)*y for x,y in zip(aa,bb)])
ref=json.loads((Path(__file__).resolve().parent.parent/'data'/'verify_common_field.json').read_text())
if not (p==[[F(x) for x in row] for row in ref['support_coefficients_by_common_B_power']]):raise RuntimeError('independent exact replay failed')
if not (gaps==[[F(x) for x in row] for row in ref['newton_gap_coefficients']]):raise RuntimeError('independent exact replay failed')
certs=[]
for k,shift,scale in [(1,0,5),(2,0,25),(5,4,25)]:
    c,b,a=[scale*x for x in gaps[k-1][shift:shift+3]]
    disc=b*b-4*a*c
    if not (a>0 and disc<0):raise RuntimeError('independent exact replay failed')
    certs.append({'gap':k,'scale':scale,'shift':shift,'discriminant':str(disc)})
if not (all(x>=0 for x in gaps[2]+gaps[3]+gaps[1][3:])):raise RuntimeError('independent exact replay failed')
if not (all(any(x>0 for x in g) for g in gaps)):raise RuntimeError('independent exact replay failed')
C=[p[i+3][3] for i in range(4)]
if not (C==list(map(F,[120]))+[F(26602,5),F(393176,5),F(1937208,5)]):raise RuntimeError('independent exact replay failed')
scaled=[5*x for x in C]
if not (scaled[1]**2-3*scaled[0]*scaled[2]==-50396):raise RuntimeError('independent exact replay failed')
if not (scaled[2]**2-3*scaled[1]*scaled[3]==-13454672):raise RuntimeError('independent exact replay failed')
out={'independent_method':'actual endpoint-subset dynamic states with eight-left twin multiplicity','table_matches':True,'newton_polynomials_match':True,'full_common_field_strict_ulc6':True,'scaled_conditional_cubic':[str(x) for x in scaled],'first_ulc3_gap':str(scaled[1]**2-3*scaled[0]*scaled[2]),'second_ulc3_gap':str(scaled[2]**2-3*scaled[1]*scaled[3]),'quadratic_certificates':certs}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
