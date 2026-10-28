#!/usr/bin/env python3
"""Exact standard-library four-plan certificate, authored in this iteration.
No archive code is read, imported, or executed. Checks remain active under -O.
"""
from fractions import Fraction as F
from operator import add
from math import prod
import json
from verify_rectangular_tree import supports, MENUS, L, require, constants, sq

AFFINE9=tuple(tuple(tuple(3*x+y for y in range(3)) for x in range(3)) for _ in range(1)) + tuple(tuple(tuple(3*x+((m*x+c)%3) for x in range(3)) for c in range(3)) for m in range(3))
PERM13=tuple((5*x+3)%13 for x in range(13))
MENUS4={9:AFFINE9,13:MENUS[13]+((PERM13[:5],PERM13[5:9],PERM13[9:]),)}
EXPECTED4={9:(57,405850918811760,F(563681831683,1764000000000)),13:(89,895372728026656,F(27980397750833,82810000000000))}

def certify4(r):
    sets=tuple(supports(r,plan) for plan in MENUS4[r])
    count,Qexpected,b2expected=EXPECTED4[r]
    require(len(sets)==4 and all(len(v)==count for v in sets),'bad support count')
    dot=lambda a,b:sum(x*y for x,y in zip(a,b))
    norms=[[dot(a,a) for a in s] for s in sets]
    grams={(i,j):[[2*dot(a,b) for b in sets[j]] for a in sets[i]] for i in range(4) for j in range(i+1,4)}
    maximum=-1;witness=None;checked=0
    for i in range(count):
        for j in range(count):
            fixed=norms[0][i]+norms[1][j]+grams[0,1][i][j]
            left=[norms[2][k]+grams[0,2][i][k]+grams[1,2][j][k] for k in range(count)]
            right=[norms[3][ell]+grams[0,3][i][ell]+grams[1,3][j][ell] for ell in range(count)]
            for k in range(count):
                row=grams[2,3][k]
                q=fixed+left[k]+max(map(add,row,right))
                checked+=count
                if q>maximum:
                    maximum=q
                    ell=max(range(count),key=lambda ell:row[ell]+right[ell])
                    witness=(i,j,k,ell)
    require(checked==count**4,'wrong number of support tuples')
    require(maximum==Qexpected,'wrong maximum squared norm')
    direct=sum(sum(sets[j][witness[j]][e] for j in range(4))**2 for e in range(r*(r-1)//2))
    require(direct==maximum,'bad direct-coordinate witness')
    b2=F(2*maximum,16*r*r*L*L)
    require(b2==b2expected,'wrong local coefficient')
    return {'r':r,'plans':MENUS4[r],'supports_per_plan':count,'tuples_checked':checked,'Q':maximum,'b_squared':str(b2),'witness_indices':witness}

def schedule4():
    kappa=constants()
    f0,f1,f2=F(1577,100000),F(2813,250000),F(1433,300000)
    K0=kappa/sq(f0);K1=kappa*F(2,9)/sq(f1);K2=kappa*F(4,117)/sq(f2)
    a9=sq(16)/9;a13=sq(24)/13
    b9=sq(EXPECTED4[9][2]);b13=sq(EXPECTED4[13][2]);b7=sq(F(632,1225))
    C0=b9*K0;C1=a9*K0+b13*K1;Cinf=a9*K0+a13*K1+sq(3)*K2/2
    require(Cinf.lo>max(C0.hi,C1.hi),'tail not dominant')
    require(C0.lo>max((b13*K1).hi,(b7*K2).hi),'root space not dominant')
    require(Cinf.hi<F(30492,1000),'safe time coefficient failed')
    require(C0.hi<F(28854,1000),'safe space coefficient failed')
    return {'C0_space':C0.decimal_enclosure(),'C1':C1.decimal_enclosure(),'C_infinity_time':Cinf.decimal_enclosure(),'safe_eventual_time':'30.492','safe_eventual_space':'28.854'}

if __name__=='__main__':
    result={'method':'four-plan exact integer support certificate; no incoming code executed','scale':L,'certificates':[certify4(r) for r in (9,13)],'retuned_schedule':schedule4()}
    print(json.dumps(result,indent=2,sort_keys=True))
