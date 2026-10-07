#!/usr/bin/env python3
"""Exact finite checks of the coset inequalities; no floating point.

Run from the extracted package root:
    python3 code/verify_cosets.py --output data/coset_checks.json

The nonlinear puncture tests fix the canonical outer coset C throughout.
They minimize only over holes D that are cosets contained in that C; they
make no claim about minimizing over all possible punctured outer cosets.
"""
from itertools import product
from pathlib import Path
import json
import argparse

if not __debug__:
    raise RuntimeError("Run without -O: this exact verifier requires assertions.")

COUNTS={"cyclic_subsets":0,"high_energy_cases":0,"equality_cases":0,
        "positive_equality_cases":0,"puncture_cases":0,"product_cases":0,
        "nonlinear_puncture_cases":0,
        "nonlinear_puncture_positive_budget_cases":0,
        "nonlinear_puncture_beyond_old_cutoff_cases":0,
        "nonlinear_puncture_minimum_checks":0,
        "nonlinear_puncture_equality_cases":0,
        "nonlinear_puncture_strict_cases":0,
        "nonlinear_puncture_positive_equality_cases":0,
        "nested_hole_closed_form_cases":0,
        "outlier_closed_form_cases":0}

FORMULA_REPORTS={}

def energy(A,add,neg):
    r={}
    for a in A:
        for b in A:
            d=add(a,neg(b));r[d]=r.get(d,0)+1
    return sum(v*v for v in r.values())

def subcoset(A,add,neg):
    if not A:return False
    c=next(iter(A));H={add(a,neg(c)) for a in A}
    return all(add(a,neg(b)) in H for a in H for b in H)

def check_canonical(A,r,add,neg,allcosets=None):
    m=len(A);E=sum(v*v for v in r.values());D=m**3-E
    assert all(m*v*(m-v)<=2*D for v in r.values())
    if 9*D>=m**3:return
    COUNTS["high_energy_cases"]+=1
    H={d for d,v in r.items() if 2*v>m}
    assert all(add(x,neg(y)) in H for x in H for y in H)
    Cs={frozenset(add(a,h) for h in H) for a in A}
    C=set(max(Cs,key=lambda c:len(c&A)))
    A0=A&C;K=C-A;T=A-C;b=len(A0);u=len(K);t=len(T)
    d=u+t
    assert 2*d<m
    assert d*m*(m-d)<=D
    if allcosets is not None:
        distances=[(len(A^c),c) for c in allcosets]
        md=min(z[0] for z in distances)
        closest=[z[1] for z in distances if z[0]==md]
        assert md==d and closest==[C]
    E0=energy(A0,add,neg);EK=energy(K,add,neg)
    assert E<=E0+6*b*t*t+5*t**3
    assert E0==b**3-b*u*(b-u)-(u**3-EK)
    exact_rhs=d*m*(m-d)+t*(2*m*m+d*d-(8*m+d)*t+2*t*t)+(u**3-EK)
    assert D>=exact_rhs
    excess=D-d*m*(m-d)
    assert excess>=t*m*m+(u**3-EK)
    eq=excess==0
    classified=(d==0) or (t==0 and subcoset(K,add,neg) and len(C)>=9*len(K))
    assert eq==classified
    if eq:
        COUNTS["equality_cases"]+=1
        if d:COUNTS["positive_equality_cases"]+=1
    if d and 16*excess<=d**3:
        COUNTS["puncture_cases"]+=1
        assert u
        rK={}
        for a in K:
            for b1 in K:
                z=add(a,neg(b1));rK[z]=rK.get(z,0)+1
        HK={z for z,v in rK.items() if 2*v>u}
        Ds={frozenset(add(a,z) for z in HK) for a in K}
        hole=set(max(Ds,key=lambda S:len(S&K)))
        edited=len(A^(C-hole))
        assert edited*d*d<=2*excess

    # Sharper puncture theorem.  Assumptions:
    #   9*(m^3-E)<m^3; C is the canonical closest coset above;
    #   d=|A symmetric_difference C|>0;
    #   Jint=m^3-E-d*m^2+d^2*m, with 0<=9*Jint<d^3.
    # If j=min_{D coset, D subset C}|A symmetric_difference (C-D)|,
    # then j/d <= tau(Jint/d^3).  The radical-free equivalent is
    # 2*j<=d and d*j*(d-j)<=Jint.  No outer coset is varied here.
    Jint=excess
    assert Jint==m**3-E-d*m*m+d*d*m
    if d and 9*Jint<d**3:
        COUNTS["nonlinear_puncture_cases"]+=1
        if Jint:
            COUNTS["nonlinear_puncture_positive_budget_cases"]+=1
        if 16*Jint>d**3:
            COUNTS["nonlinear_puncture_beyond_old_cutoff_cases"]+=1
        assert u>0
        assert 9*(u**3-EK)<u**3
        rK={}
        for a in K:
            for b1 in K:
                z=add(a,neg(b1));rK[z]=rK.get(z,0)+1
        HK={z for z,v in rK.items() if 2*v>u}
        assert all(add(a,neg(b1)) in HK for a in HK for b1 in HK)
        candidates={frozenset(add(a,z) for z in HK) for a in K}
        hole=set(max(candidates,key=lambda S:len(S&K)))
        assert hole<=C
        edited=len(A^(C-hole))
        assert edited==t+len(K^hole)

        # When the ambient finite coset list is supplied, independently
        # minimize over EVERY allowed hole, not merely the one produced
        # by the canonical construction on K.
        allowed=None
        if allcosets is not None:
            allowed=[Dhole for Dhole in allcosets if Dhole<=C]
            assert allowed
            minimum=min(len(A^(C-Dhole)) for Dhole in allowed)
            assert edited==minimum
            COUNTS["nonlinear_puncture_minimum_checks"]+=1
        assert 2*edited<=d
        assert d*edited*(d-edited)<=Jint

        equality=d*edited*(d-edited)==Jint
        if equality:
            COUNTS["nonlinear_puncture_equality_cases"]+=1
        else:
            COUNTS["nonlinear_puncture_strict_cases"]+=1
        if Jint>0:
            # Positive-budget equality has no outer outliers and the
            # actual hole K is itself D-J for nested cosets J subset D
            # subset C, with [D:J]>=9.  Empty J is excluded here.
            def nested_model(Dhole):
                Jhole=Dhole-K
                return (K<=Dhole and bool(Jhole)
                        and subcoset(Jhole,add,neg)
                        and len(Dhole)>=9*len(Jhole))
            classified=(t==0 and nested_model(hole))
            if allowed is not None:
                exhaustive_classification=(t==0 and any(
                    nested_model(Dhole) for Dhole in allowed))
                assert classified==exhaustive_classification
            assert equality==classified
            if equality:
                COUNTS["nonlinear_puncture_positive_equality_cases"]+=1

def cyclic_cosets(n):
    cosets=[]
    for h in range(1,n+1):
        if n%h==0:
            step=n//h
            cosets.extend({c+step*j for j in range(h)} for c in range(step))
    return cosets

def cyclic():
    for n in range(2,17):
        mask=(1<<n)-1
        add=lambda x,y,n=n:(x+y)%n
        neg=lambda x,n=n:(-x)%n
        cosets=cyclic_cosets(n)
        for bits in range(1,1<<n):
            A={i for i in range(n) if bits>>i&1};m=len(A)
            rs=[(bits&(((bits<<d)|(bits>>(n-d)))&mask)).bit_count() for d in range(n)]
            r={d:v for d,v in enumerate(rs) if v}
            COUNTS["cyclic_subsets"]+=1
            check_canonical(A,r,add,neg,cosets)

def larger():
    # Nonzero outlier examples, exact equality with nontrivial hole,
    # and punctured holes at the scale required by the stability theorem.
    for n,h,k,returned,extra in [(256,128,4,0,1),(1024,512,16,0,1),
                                 (120,120,12,0,0),(160,160,16,1,0),
                                 (320,320,32,1,0),(640,640,64,1,0),
                                 (90,90,9,1,0),(100,100,10,1,0),
                                 (250,250,25,2,0)]:
        step=n//h;H={i*step for i in range(h)}
        L={i*(n//k) for i in range(k)}
        K=set(L)
        if returned:K.difference_update(sorted(L)[:returned])
        A=H-K
        if extra:A.add(1)
        add=lambda x,y,n=n:(x+y)%n
        neg=lambda x,n=n:(-x)%n
        r={}
        for a in A:
            for b in A:
                d=add(a,neg(b));r[d]=r.get(d,0)+1
        check_canonical(A,r,add,neg,cyclic_cosets(n))

def nonlinear_closed_form_families():
    # Nested-hole equality family, without enumerating a large group.
    # H=Z/(r*v)Z, D its subgroup of order v, J={0}, K=D-J,
    # A=H-K.  Here r>=10 and v>=9 are sufficient for both defects
    # to lie in the strict 1/9 ranges.  Put u=v-1 and m=r*v-u.
    # E(K)=u^3-u*(u-1); the exact complement identity gives E(A).
    # The fixed canonical C is H because 3*m>2*|H|.  D is a
    # one-edit hole model.  Zero edits would make K a coset, ruled
    # out by E(K)<u^3.  Thus the minimum j is exactly one.
    outer_indices=(10,11,12,16,31,64,127)
    inner_indices=tuple(range(9,65))+(97,101,127,256,1024)
    for r in outer_indices:
        for v in inner_indices:
            h=r*v;u=v-1;m=h-u;d=u;j=1
            EK=u**3-u*(u-1)
            E=m**3-m*u*(m-u)-(u**3-EK)
            D=m**3-E
            Jint=D-d*m*m+d*d*m
            assert r>=10 and v>=9
            assert 3*m>2*h
            assert 0<9*D<m**3
            assert 0<Jint and 9*Jint<d**3
            assert Jint==u*(u-1)
            assert 2*j<=d
            assert d*j*(d-j)==Jint
            # Hence s=Jint/d^3=(u-1)/u^2 and tau(s)=1/u.
            assert EK<u**3
            COUNTS["nested_hole_closed_form_cases"]+=1
    FORMULA_REPORTS["nested_hole_family"]={
        "outer_indices":outer_indices,
        "inner_indices":inner_indices,
        "ambient":"H cyclic of order r*v; D subgroup of order v; J={0}",
        "set":"A=H\\(D\\J), canonical C=H",
        "u":"v-1", "m":"r*v-u", "d":"u", "minimum_edit":1,
        "Jint":"u*(u-1)", "s":"(u-1)/u^2",
        "equality":"d*j*(d-j)=Jint", "inner_index_minimum":9,
        "method":"Exact closed complement and subgroup formulas; no large-group enumeration"
    }

    # Strict cases with an outer outlier.  Work in Z/hZ x Z/2Z,
    # C=Z/hZ x {0}, L subgroup of C of order u, h=r*u,
    # B=C-L, and A=B union {(0,1)}.  With b=|B|=(r-1)*u,
    # E(B)=b^3-b*u*(b-u) and E(A)=E(B)+6*b+1.
    # The latter follows by splitting differences inside/outside C;
    # the added point has order two and B=-B.  The nearest fixed-C
    # puncture C-L differs by exactly its one unavoidable outlier.
    # Large u puts Jint/d^3 below 1/9, but all arithmetic remains
    # finite closed-form integer arithmetic rather than set enumeration.
    parameters=[]
    for r in (10,11,16,31,64,127):
        for offset in (0,1,7):
            u=100*(2*(r-1)**2+1)+offset
            h=r*u;b=h-u;m=b+1;d=u+1;t=1;j=1
            EB=b**3-b*u*(b-u)
            E=EB+6*b+1
            D=m**3-E
            Jint=D-d*m*m+d*d*m
            assert 3*b>2*h
            # Every correlation outside C is at most two, whereas
            # correlations on C are at least 2*b-h>m/2.
            assert 2*(2*b-h)>m and 4<m
            assert 0<9*D<m**3
            assert 0<9*Jint<d**3
            assert Jint==2*b*b-4*b+u*u+u
            assert 2*j<=d and d*j*(d-j)<Jint
            assert t==1
            COUNTS["outlier_closed_form_cases"]+=1
            parameters.append({"r":r,"u":u,"m":m,"d":d,"Jint":Jint})
    FORMULA_REPORTS["outlier_family"]={
        "ambient":"Z/(r*u)Z x Z/2Z",
        "set":"A=(C\\L) union {(0,1)}, C=Z/(r*u)Z x {0}, |L|=u",
        "minimum_edit":1, "outliers":1,
        "equality":False, "Jint":"2*b^2-4*b+u^2+u, b=(r-1)*u",
        "parameters":parameters,
        "method":"Exact closed energy formula; fixed canonical outer coset"
    }

def cube_tests():
    for p,q in [(2,3),(3,3),(2,5)]:
        G=list(product(range(p),range(q)));n=len(G)
        add=lambda x,y:( (x[0]+y[0])%p,(x[1]+y[1])%q )
        neg=lambda x:(-x[0]%p,-x[1]%q)
        for bits in range(1,1<<n):
            A={x for i,x in enumerate(G) if bits>>i&1};m=len(A)
            Q=0
            for h in G:
                bases=0
                for x in A:
                    verts={(x[0],x[1]),((x[0]+h[0])%p,x[1]),
                           (x[0],(x[1]+h[1])%q),add(x,h)}
                    bases+=verts<=A
                Q+=bases*bases
            COUNTS["product_cases"]+=1
            E=energy(A,add,neg)
            assert Q<=E
            if 9*(m**3-Q)>=m**3:continue
            r={}
            for a in A:
                for b in A:
                    d=add(a,neg(b));r[d]=r.get(d,0)+1
            H={d for d,v in r.items() if 2*v>m}
            H1={x[0] for x in H};H2={x[1] for x in H}
            assert H==set(product(H1,H2))
            Cs={frozenset(add(a,h) for h in H) for a in A}
            C=set(max(Cs,key=lambda c:len(c&A)));d=len(A^C)
            if (m**3-Q)==d*m*(m-d) and d:
                assert Q==E and A<=C
                A1={x[0] for x in A};A2={x[1] for x in A}
                C1={x[0] for x in C};C2={x[1] for x in C}
                assert A==set(product(A1,A2))
                assert (A1!=C1)+(A2!=C2)==1

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,
                        default=Path(__file__).resolve().parents[1]/"data"/"coset_checks.json")
    args=parser.parse_args()
    cyclic();larger();cube_tests();nonlinear_closed_form_families()
    out={"status":"PASS","counts":COUNTS,
         "scope":"Exact finite checks supplement the general written proofs.",
         "tested_exact_polynomial_remainder":True,
         "tested_nonlinear_puncture_bound":{
             "outer_coset":"fixed canonical C",
             "assumptions":"9*(m^3-E)<m^3; d>0; 0<=9*Jint<d^3",
             "Jint":"m^3-E-d*m^2+d^2*m",
             "minimum":"j=min over cosets D contained in C of |A symmetric_difference (C\\D)|",
             "integer_conclusion":["2*j<=d","d*j*(d-j)<=Jint"],
             "positive_budget_equality":"t=0 and K=D\\J for nested cosets J subset D subset C, [D:J]>=9"
         },
         "closed_form_reports":FORMULA_REPORTS}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
