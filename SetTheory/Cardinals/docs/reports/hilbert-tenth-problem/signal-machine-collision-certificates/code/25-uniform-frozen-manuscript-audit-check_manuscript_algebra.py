#!/usr/bin/env python3
"""Fresh Report 51 manuscript algebra check. No upstream code is imported.
Finite fixtures supplement, and do not prove, the all-natural-fiber argument.
"""
import hashlib, itertools, json
from collections import defaultdict
from pathlib import Path
import sympy as sp

counts = {}
# Signed-input sign-cell fixture, built directly from the manuscript formulas.
# m=1, J=2, k_0=k_1=1, I=2, H_0=0, ell=1.
xp,xm,yp,ym,t = sp.symbols('xp xm yp ym t')
e0,e1,p0,m0,p1,m1,n0,n1,s0,s1 = sp.symbols('e0 e1 p0 m0 p1 m1 n0 n1 s0 s1')
X0,X1=p0-m0,p1-m1
w=(e0,e1,p0,m0,p1,m1,n0,n1,s0,s1)
res=[e0+e1-1,p0-e0*xp,m0-e0*xm,p1-e1*xp,m1-e1*xm,
     X0-s0,-X1-e1-s1,
     t-(X0**2+X0*n0+n0**2+X1**2+X1*n1+n1**2+e1),
     yp-ym-(X0+n0+X1-n1),
     (1-e0)*(p0+m0+n0+s0),(1-e1)*(p1+m1+n1+s1)]
assert len(w)==3*1*2+2+2 == 10
assert len(res)==1+2*1*2+2+0+(1+1)+2 == 11
poly=sp.Poly(sum(r*r for r in res),xp,xm,yp,ym,t,*w)
assert poly.total_degree()==4
assert all(sp.Poly(r,xp,xm,yp,ym,t,*w).total_degree()<=2 for r in res)
full=sp.Poly(poly.as_expr()+(xp*xm)**2+(yp*ym)**2,xp,xm,yp,ym,t,*w)
assert full.total_degree()==4
assert sp.Poly((t-(xp*n0+n0**2+e0*xp**2))**2,t,xp,n0,e0).total_degree()==6
counts['signed_fixture_symbolic_degree_and_ledger_checks']=5

# Exhaust every natural witness tuple in [0,2]^10 for every natural input pair
# in [0,2]^2; add the optional canonical-input residual. No witness equation
# is solved in advance for this enumeration.
counts['natural_witness_tuples']=0
counts['canonical_input_cases']=0
counts['noncanonical_input_cases']=0
counts['singleton_fibers_in_box']=0
counts['empty_sample_fibers_in_box']=0
for ap,am in itertools.product(range(3), repeat=2):
    fibers=defaultdict(list)
    for E0,E1,P0,M0,P1,M1,N0,N1,S0,S1 in itertools.product(range(3), repeat=10):
        counts['natural_witness_tuples']+=1
        a0,a1=P0-M0,P1-M1
        pre=(E0+E1-1, P0-E0*ap, M0-E0*am, P1-E1*ap, M1-E1*am,
             a0-S0,-a1-E1-S1,(1-E0)*(P0+M0+N0+S0),
             (1-E1)*(P1+M1+N1+S1),ap*am)
        if any(pre):
            continue
        T=a0*a0+a0*N0+N0*N0+a1*a1+a1*N1+N1*N1+E1
        Y=a0+N0+a1-N1
        assert T>=0
        fibers[(T,Y)].append((E0,E1,P0,M0,P1,M1,N0,N1,S0,S1))
    x=ap-am
    if ap*am:
        counts['noncanonical_input_cases']+=1
        assert not fibers
    else:
        counts['canonical_input_cases']+=1
        expected={(x*x+x*n+n*n+int(x<0),x+n if x>=0 else x-n) for n in range(3)}
        assert set(fibers)==expected
        assert all(len(v)==1 for v in fibers.values())
        counts['singleton_fibers_in_box']+=len(fibers)
        for T,Y in itertools.product(range(16),range(-5,6)):
            if (T,Y) not in expected:
                assert (T,Y) not in fibers
                counts['empty_sample_fibers_in_box']+=1
counts['canonical_output_pair_checks']=0
for y in range(-6,7):
    reps=[(p,m) for p,m in itertools.product(range(7),repeat=2) if p-m==y and p*m==0]
    assert reps==[(max(y,0),max(-y,0))]
    counts['canonical_output_pair_checks']+=1

# Two-input quotient fixture, exact pooled rational outputs and all ledger slots.
# H=2. Gap g=2u+r, with r=0 or 1. Two evolutions n,j and two inequalities.
a,b,T,Y1,Y2=sp.symbols('a b T Y1 Y2')
e=sp.symbols('e0:2'); vp=sp.symbols('p0:4'); vm=sp.symbols('m0:4')
u=sp.symbols('u0:2'); n=sp.symbols('n0:2'); j=sp.symbols('j0:2')
s=sp.symbols('s0:4'); aP,aM,bP,bM=sp.symbols('aP aM bP bM')
w2=(*e,*vp,*vm,*u,*n,*j,*s)
r2=[sum(e)-1]; outs=[0,0,0]
for h in range(2):
    xx=vp[2*h]-vm[2*h]; zz=vp[2*h+1]-vm[2*h+1]; g=zz-xx
    copies=(vp[2*h]-e[h]*aP,vm[2*h]-e[h]*aM,
            vp[2*h+1]-e[h]*bP,vm[2*h+1]-e[h]*bM)
    r2.extend(copies)
    r2.extend((g-e[h]-s[2*h],g-j[h]-e[h]-s[2*h+1],g-2*u[h]-h*e[h]))
    # Constant term h is lifted to h*e_h; numerical rational coefficient 1/2
    # is cleared only after the two outputs are pooled.
    outs[0]+=xx**2+(g-h)*n[h]/2+n[h]**2+j[h]**2+h*e[h]
    outs[1]+=xx+n[h]
    outs[2]+=zz+n[h]+j[h]
    Z=sum(vp[2*h:2*h+2])+sum(vm[2*h:2*h+2])+u[h]+n[h]+j[h]+sum(s[2*h:2*h+2])
    r2.append((1-e[h])*Z)
r2.extend((2*(T-outs[0]),Y1-outs[1],Y2-outs[2]))
assert len(w2)==3*2*2+4+4==20
assert len(r2)==1+2*2*2+4+2+(2+1)+2==20
p2=sp.Poly(sum(r*r for r in r2),aP,aM,bP,bM,T,Y1,Y2,*w2)
assert p2.total_degree()==4
assert all(v.q==1 for v in p2.coeffs())
counts['quotient_fixture_symbolic_degree_and_ledger_checks']=4
counts['quotient_fixture_constructive_chart_points']=0
for x1 in range(-5,6):
    for gap in range(1,12):
        x2=x1+gap; h=gap%2; q=gap//2
        for N in range(4):
            for J in range(gap):
                values={v:0 for v in w2}
                values.update({aP:max(x1,0),aM:max(-x1,0),bP:max(x2,0),bM:max(-x2,0)})
                values[e[h]]=1
                values[vp[2*h]]=max(x1,0);values[vm[2*h]]=max(-x1,0)
                values[vp[2*h+1]]=max(x2,0);values[vm[2*h+1]]=max(-x2,0)
                values[u[h]]=q;values[n[h]]=N;values[j[h]]=J
                values[s[2*h]]=gap-1;values[s[2*h+1]]=gap-1-J
                values[T]=x1*x1+q*N+N*N+J*J+h
                values[Y1]=x1+N;values[Y2]=x2+N+J
                # Exact numerical substitution by a lambdified residual evaluator.
                if 'evaluate' not in globals():
                    variables=tuple(sorted(set().union(*(r.free_symbols for r in r2)),key=str))
                    evaluate=sp.lambdify(variables,r2,'math')
                assert all(z==0 for z in evaluate(*(values[z] for z in variables)))
                counts['quotient_fixture_constructive_chart_points']+=1

# Residue pullbacks, denominator-before-slack and zero-net cross term controls.
counts['congruence_pullback_cases']=0
for d in range(1,8):
    for M in range(1,8):
        for value in range(-100,101):
            if value%d: continue
            for rho in range(M):
                assert ((value//d)%M==rho)==((value-d*rho)%(d*M)==0)
                counts['congruence_pullback_cases']+=1
assert sp.Rational(1,2)>=0 and sp.Rational(1,2).q!=1
D,N,A,C=sp.symbols('D N A C')
clock=N*(A*D+C)
assert sp.Poly(clock.subs({A:3,C:5}),D,N).total_degree()==2
assert sp.diff(clock,D,N)==A
counts['negative_controls']=3

out={'status':'PASS','scope':'Independent finite algebra fixtures only; not a CA implementation or all-natural proof',
     'counts':counts,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'executed_upstream_code':False,'executed_saved_schedules':False}
Path(__file__).with_name('CHECK-RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
