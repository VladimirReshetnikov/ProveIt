#!/usr/bin/env python3
"""New independent exact verifier: rectangular backend + inherited tree menus.

Standard library only. Does not import or execute any incoming archive code.
Exact integers verify every support tuple; finite checks support the proof.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import isqrt
import json

L = 1400000
COEFFICIENTS = tuple(sorted(set(permutations((1400007, 1400007, 0))))) + tuple(permutations((L, 1175014, 750000)))
MENUS = {
9: (((0,1,2),(3,4,5),(6,7,8)), ((6,2,5),(4,7,0),(1,8,3)), ((5,2,8),(4,6,1),(0,7,3))),
13: (((0,1,2,3,4),(5,6,7,8),(9,10,11,12)), ((12,10,1,6,4),(9,0,3,8),(5,2,7,11)), ((0,8,11,12,1),(7,10,4,3),(5,2,6,9))),
}
EXPECTED = {
9: (57, 246255154308036, 24785168341806412920, F(2280140317667, 6615000000000)),
13: (89, 519754477218816, 144283691430119248320, F(24170130079, 69316406250)),
}

def require(ok, message):
    if not ok: raise ArithmeticError(message)

def supports(r, plan):
    edges = tuple(combinations(range(r), 2))
    edge_id = {e:i for i,e in enumerate(edges)}
    operations=[]
    def subtree(vertices):
        if len(vertices)==1: return
        mid=len(vertices)//2
        left,right=vertices[:mid],vertices[mid:]
        subtree(left);subtree(right)
        outside=tuple(v for v in range(r) if v not in vertices)
        operations.append((left,right,outside))
    for block in plan: subtree(block)
    operations.append(plan)
    require(len(operations)==r-2, 'wrong operation count')
    vectors=set()
    for parts in operations:
        classes=[]
        for i,j in ((0,1),(0,2),(1,2)):
            classes.append(tuple(edge_id[tuple(sorted((u,v)))] for u in parts[i] for v in parts[j]))
        for coefficients in COEFFICIENTS:
            vector=[0]*len(edges)
            for coefficient, support in zip(coefficients,classes):
                for e in support: vector[e]=coefficient
            vectors.add(tuple(vector))
    return tuple(sorted(vectors))

def certify(r):
    sets=tuple(supports(r,plan) for plan in MENUS[r])
    expected_count,expected_max,expected_sum,expected_b2=EXPECTED[r]
    require(all(len(s)==expected_count for s in sets),'wrong support count')
    # Dot-product expansion is exact over unbounded Python integers.
    dot=lambda a,b:sum(x*y for x,y in zip(a,b))
    norms=[[dot(a,a) for a in s] for s in sets]
    ab=[[dot(a,b) for b in sets[1]] for a in sets[0]]
    ac=[[dot(a,c) for c in sets[2]] for a in sets[0]]
    bc=[[dot(b,c) for c in sets[2]] for b in sets[1]]
    maximum=-1; total=0; count=0; witness=None
    for i,j,k in product(*(range(len(s)) for s in sets)):
        q=norms[0][i]+norms[1][j]+norms[2][k]+2*(ab[i][j]+ac[i][k]+bc[j][k])
        total+=q;count+=1
        if q>maximum: maximum=q;witness=(i,j,k)
    require(maximum==expected_max,'wrong maximum squared norm')
    require(total==expected_sum,'wrong sum of squared norms')
    # Direct coordinate reconstruction independently verifies the attaining tuple.
    direct=sum(sum(sets[j][witness[j]][e] for j in range(3))**2 for e in range(r*(r-1)//2))
    require(direct==maximum,'bad witness')
    b2=F(2*maximum,9*r*r*L*L)
    require(b2==expected_b2,'wrong coefficient')
    return {'r':r,'supports_per_plan':expected_count,'tuples':count,'Q':maximum,'sum_Q':total,'b_squared':str(b2),'witness_indices':witness}

class I:
    def __init__(self,lo,hi=None):self.lo=F(lo);self.hi=F(lo if hi is None else hi)
    def __add__(self,o):
        if not isinstance(o,I):o=I(o)
        return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __mul__(self,o):
        if not isinstance(o,I):o=I(o)
        require(min(self.lo,o.lo)>=0,'positive interval needed')
        return I(self.lo*o.lo,self.hi*o.hi)
    __rmul__=__mul__
    def __truediv__(self,o):
        if not isinstance(o,I):o=I(o)
        require(o.lo>0,'positive denominator needed')
        return I(self.lo/o.hi,self.hi/o.lo)
    def decimal_enclosure(self,digits=12):
        scale=10**digits
        lower=self.lo.numerator*scale//self.lo.denominator
        upper=(self.hi.numerator*scale+self.hi.denominator-1)//self.hi.denominator
        def fmt(n):return str(n//scale)+'.'+str(n%scale).zfill(digits)
        return [fmt(lower),fmt(upper)]

def sq(q):
    q=F(q);scale=10**40
    root=isqrt(q.numerator*scale*scale//q.denominator)
    return I(F(root,scale),F(root+1,scale))

def atan_inverse(n,terms=120):
    partial=sum((F(1,(2*j+1)*n**(2*j+1)) if j%2==0 else -F(1,(2*j+1)*n**(2*j+1))) for j in range(terms))
    omitted=F(1,(2*terms+1)*n**(2*terms+1))
    return I(partial,partial+omitted) # even number of terms: first omitted positive

def constants():
    a,b=atan_inverse(5),atan_inverse(239)
    pi=I(16*a.lo-4*b.hi,16*a.hi-4*b.lo)
    n=120
    ln2lo=2*sum(F(1,(2*j+1)*3**(2*j+1)) for j in range(n))
    remainder=F(2,(2*n+1)*3**(2*n+1))/F(8,9)
    ln2=I(ln2lo,ln2lo+remainder)
    return pi*sq(2)/ln2

def schedule(retuned=False):
    kappa=constants()
    f0,f1,f2=(F(1577,100000),F(2813,250000),F(1433,300000)) if retuned else (F(63,4000),F(9,800),F(77,16200))
    K0=kappa/sq(f0);K1=kappa*F(2,9)/sq(f1);K2=kappa*F(4,117)/sq(f2)
    a9=sq(16)/9;a13=sq(24)/13
    b9=sq(EXPECTED[9][3]);b13=sq(EXPECTED[13][3]);b7=sq(F(632,1225))
    C0=b9*K0;C1=a9*K0+b13*K1;Cinf=a9*K0+a13*K1+sq(3)*K2/2
    require(C1.lo>max(C0.hi,Cinf.hi),'claimed time branch not dominant')
    require(C0.lo>max((b13*K1).hi,(b7*K2).hi),'root space branch not dominant')
    require(C1.hi<F(30630,1000),'eventual time bound failed')
    require(C0.hi<F(29986,1000),'eventual space bound failed')
    require(C1.hi<F(30891,1000),'no strict improvement in time')
    require(C0.hi<F(30753,1000),'no strict improvement in space')
    # Exact schedule capacity/packing comparisons; log inequalities via integer powers.
    if retuned:
        require(f0+f1==F(13511,500000),'bad retuned prefix capacity')
        require(f0+f1+f2/F(5,9)==F(1781,50000),'bad retuned total capacity')
        require(9**1577<2**5000,'retuned root9 gate')
        require(13**13511<2**50000,'retuned depth1 gate')
        require(7**1781<2**5000,'retuned tail7 gate')
        require(13**1000<2**3701,'auxiliary log13 bound')
        require(F(1781,50000)*(2*F(3701,1000)+1)<F(3,10),'fresh and rounding gates')
        require(C1.hi<F(30615,1000),'retuned eventual time bound failed')
        require(C0.hi<F(29967,1000),'retuned eventual space bound failed')
    else:
        require(f0+f1==F(27,1000),'bad prefix capacity')
        require(f0+f1+f2/F(5,9)==F(8,225),'bad total capacity')
        require(9**63<2**200,'root9 gate')
        require(13**27<2**100,'depth1 gate')
        require(7**16<2**45,'tail7 gate')
    return {'f0':str(f0),'f1':str(f1),'f2':str(f2),'C0_space':C0.decimal_enclosure(),'C1_time':C1.decimal_enclosure(),'C_infinity':Cinf.decimal_enclosure(),'safe_eventual_time':'30.615' if retuned else '30.630','safe_eventual_space':'29.967' if retuned else '29.986'}


if __name__=='__main__':
    output={'method':'exact rational rectangular support portfolio; no incoming code executed', 'scale':L,'certificates':[certify(r) for r in (9,13)],'unchanged_schedule_ablation':schedule(),'retuned_schedule':schedule(True)}
    print(json.dumps(output,indent=2,sort_keys=True))
