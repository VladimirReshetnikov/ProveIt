#!/usr/bin/env python3
"""Verify the skew example's global face cover using only exact finite inequalities.

SymPy builds the explicit rational quadratic polynomials. All box tests use
integer Bernstein coefficients, and none of the proof checks calls Z3.
"""
from collections import Counter
from fractions import Fraction as Q
import sympy as s
from skew_global import symbolic_routes, u, v

D=5*2**13
cutoff=Q(183,20)

def integer_coefficients(expr):
    p=s.Poly(expr,u,v)
    assert p.is_zero or p.total_degree() <= 2
    den,z=p.clear_denoms()
    return tuple(int(z.coeff_monomial(m)) for m in (u*u,u*v,v*v,u,v,1)),int(den)

def positive_on_box(poly,box):
    """Nonnegative degree-(2,2) Bernstein coefficients suffice on the box."""
    a,b,c,d,e,f=poly
    x,X,y,Y=box; dx=X-x;dy=Y-y
    p=4*((a*x+b*y+d*D)*x+(c*y+e*D)*y+f*D*D)
    if p<0:return False
    h=2*dx*(2*a*x+b*y+d*D); k=2*dy*(b*x+2*c*y+e*D)
    hh=4*a*dx*dx; hk=b*dx*dy; kk=4*c*dy*dy
    return all(p+i*h+j*k+(hh if i==2 else 0)+(kk if j==2 else 0)+i*j*hk>=0
               for i in range(3) for j in range(3))

def cover(axis,boxes):
    rows=[]
    for idx,(w,f,(guard,conditions)) in enumerate(symbolic_routes(axis,True)):
        if len(w)>4 or guard=="false":continue
        polys=[integer_coefficients(z)[0] for z in conditions if s.sympify(z).free_symbols]
        rows.append((integer_coefficients(cutoff-f)[0],polys,idx))
    counts=Counter()
    def test(box,depth):
        counts["visited"]+=1
        x,X,y,Y=box
        for bd,guards,idx in rows:
            if positive_on_box(bd,box) and all(positive_on_box(z,box) for z in guards):
                counts["single_strip"]+=1
                print("box",axis,*(str(Q(z,D)) for z in box),"word",idx)
                return
        assert depth<2 and not ((x+X)%2 or (y+Y)%2),("depth",axis,box,depth)
        mx,my=(x+X)//2,(y+Y)//2
        for a,b in ((x,mx),(mx,X)):
            for c,d in ((y,my),(my,Y)):test((a,b,c,d),depth+1)
    for b in boxes:test(b,0)
    return counts

def main():
    for a in (0,1):
        print(a,dict(cover(a,[(0,D,0,D)])),flush=True)
    boxes=[(0,D//4,D//2,D),(D//2,D,D//2,D),(D//4,D//2,D//2,3*D//5),
           (D//4,D//2,4*D//5,D)]
    print(2,dict(cover(2,boxes)),flush=True)
    box=(D//4,D//2,3*D//5,4*D//5)
    rows=symbolic_routes(2,True)
    for i in (6,20,2):
        guard,conds=rows[i][2]
        assert guard!="false" and all(positive_on_box(integer_coefficients(z)[0],box) for z in conds)
        for index in ([0] + list(range(5,len(conds),6))):
            assert positive_on_box(integer_coefficients(conds[index]-Q(1,1000))[0],box)
    f6,f20,f2=[rows[i][1] for i in (6,20,2)]
    for z in (s.diff(f6,v),-s.diff(f20,u),s.diff(f2,u),-s.diff(f2,v)):
        assert positive_on_box(integer_coefficients(z-Q(1,1000))[0],box)
    print("All three local words and four strict derivative signs certified.")

if __name__=="__main__":main()
