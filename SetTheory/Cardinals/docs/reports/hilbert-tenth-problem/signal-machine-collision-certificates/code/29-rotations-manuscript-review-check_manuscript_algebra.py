#!/usr/bin/env python3
"""Independent read-only exact checks of Report 59's displayed formulas.

No author module is imported or executed. This file reads frozen JSON as data,
uses closed block formulas, and writes only its new review receipt.
"""
from pathlib import Path
from fractions import Fraction as F
from math import ceil, gcd, lcm
from collections import Counter
import hashlib
import json
import sympy as s

HERE = Path(__file__).resolve().parent
SRC = Path('/workspace/shared/five-signal-rotation-family59-20261004')
D = (F(1), F(0), F(0))
def add(*rows):
    return tuple(sum(v, F(0)) for v in zip(*rows))
def times(k, row):
    return tuple(k*v for v in row)
def minus(a,b):
    return add(a,times(-1,b))
def row(v):
    return tuple(map(F,v))
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

summary=[]
totals=Counter()
for path in sorted((SRC/'evidence').glob('a*_scale*.json')):
    data=json.loads(path.read_text())
    par=data['parameters']; a,b,c=(par[k] for k in ('a','b','c'))
    lam=F(par['lambda']); tx=F(-b,c+a); ty=F(b,c)
    nx=max(1,ceil(4*abs(tx))); ny=max(1,ceil(4*abs(ty)))
    K=2*nx+ny
    assert a*a+b*b==c*c and gcd(gcd(a,b),c)==1
    assert (nx,ny)==(par['Nx'],par['Ny'])
    x=(F(1,3),F(1),F(0)); y=(F(2,3),F(0),F(1))
    wanted=[]; duration=times(2,D)
    for axis,n,delta,name in [('x',nx,tx/nx,'A1'),('y',ny,ty/ny,'B'),('x',nx,tx/nx,'A2')]:
        t,z=(x,y) if axis=='x' else (minus(D,y),minus(D,x))
        step=times(delta,minus(z,times(F(2,3),D)))
        wanted.extend([(name+'_fixed_lower',z),(name+'_fixed_upper',minus(D,z))])
        for i in range(2*n+1):
            point=add(t,times(i//2,step),times(delta*(i%2),z))
            wanted.extend([(f'{name}_endpoint{i}_lower',point),(f'{name}_endpoint{i}_upper',minus(z,point))])
        near=2*(1+1/(1-delta)); far=2*(1+1/(1+F(2,3)*delta))
        sum_even=add(times(n,t),times(F(n*(n-1),2),step))
        duration=add(duration,times(near+far,sum_even),times(n*far*delta+2*n,z),times(2*n,D))
        endpoint=add(t,times(n,step))
        if axis=='x': x=endpoint
        else: y=minus(D,endpoint)
    assert wanted==[(g['name'],row(g['row'])) for g in data['guards']]
    assert minus(x,times(F(1,3),D))==(F(0),F(a,c),F(-b,c))
    assert minus(y,times(F(2,3),D))==(F(0),F(b,c),F(a,c))
    if lam!=1: duration=add(duration,times(2*(1+lam),add(x,y,D)))
    assert duration==row(data['duration_row'])
    actual_counts=data['counts']
    expected={'events':18*K+6+24*(lam!=1), 'meta_signals':22*K+10+27*(lam!=1), 'temporary_labels':4*K+3*(lam!=1),'guards':4*K+12}
    for key,val in expected.items(): assert actual_counts[key]==val
    assert len(data['rules'])==expected['events']
    assert len(data['speeds'])==expected['meta_signals']
    distances=[]
    for name,(h,u,v) in wanted:
        assert h>0
        norm=u*u+v*v
        if norm: distances.append((h*h/norm,(-h*u/norm,-h*v/norm),name))
    rho=min(q[0] for q in distances)
    nearest=[q for q in distances if q[0]==rho]
    points=sorted({q[1] for q in nearest})
    assert rho==F(data['rho_squared'])
    assert [(F(d),row(p),name) for d,p,name in data['nearest_guards']]==nearest
    assert list(map(row,data['tangent_points']))==points
    assert len(points)==actual_counts['distinct_nearest_points']==1
    for p in points:
        assert sum(v*v for v in p)==rho
        assert all(h+u*p[0]+v*p[1]>=0 for name,(h,u,v) in wanted)
    expected_matrix=[[lam*F(z,3*c) for z in r] for r in [[c+2*a-b,c-a-b,c-a+2*b],[c-a+3*b,c+2*a,c-a-3*b],[c-a-2*b,c-a+b,c+2*a+b]]]
    assert expected_matrix==[list(row(r)) for r in data['return_gap_matrix']]
    speeds={k:F(v) for k,v in data['speeds'].items()}
    for rule in data['rules']:
        assert len(rule['in'])==len(rule['out'])==2
        assert len({speeds[k] for k in rule['in']})==2
        assert len({speeds[k] for k in rule['out']})==2
    totals.update(rules=len(data['rules']),guards=len(wanted),phases=len(data['phases']))
    summary.append({'fixture':path.name,'sha256':sha(path),'rho_squared':str(rho),'contacts':[[str(v) for v in p] for p in points],'status':'PASS'})
assert len(summary)==45
assert dict(totals)=={'rules':13572,'guards':3336,'phases':2976}

# Independent generic matrix/shear and primitive algebra, modulo the sole
# Pythagorean relation. No finite fixture is used for these identities.
a,b,c,lam=s.symbols('a b c lam')
tx=-b/(c+a); ty=b/c
Sx=s.Matrix([[1,tx],[0,1]]); Sy=s.Matrix([[1,0],[ty,1]])
R=s.Matrix([[a,-b],[b,a]])/c
for e in Sx*Sy*Sx-R:
    num=s.together(e).as_numer_denom()[0]
    assert s.rem(num,a*a+b*b-c*c,b)==0
Q=s.Matrix([[1,1,1],[s.Rational(2,3),-s.Rational(1,3),-s.Rational(1,3)],[s.Rational(1,3),s.Rational(1,3),-s.Rational(2,3)]])
M=lam*s.Matrix([[c+2*a-b,c-a-b,c-a+2*b],[c-a+3*b,c+2*a,c-a-3*b],[c-a-2*b,c-a+b,c+2*a+b]])/(3*c)
N=s.diag(lam,1,1); N[1:3,1:3]=lam*R
assert (Q*M-N*Q).applyfunc(s.simplify)==s.zeros(3)
z,u,t,v=s.symbols('z u t v')
assert s.simplify(z+(u-1)/(u+1)*(2*z+u*z-z)-u*z)==0
tprime=v*t+(1-v)*z
assert s.simplify(t+(1-v)/(1+v)*(2*z-tprime-t)-tprime)==0

# Explicit residual total degrees, treating caller base as affine in P and
# m0 as base*out, after affine adapters (which do not increase degree).
names='out w M g xp yp up vp sp tp qb qv Jp alpha beta dwb dwk dyk a1 a2 s1 s2 t1 t2 r1 r2 P e'
leaves=s.symbols(names); V=dict(zip(names.split(),leaves))
globals().update(V)
B0=3+4*(4*P+11); k0=e+1; m0=B0*out
polys=[xp*xp-1-(alpha*alpha-1)*yp*yp,up*up-1-(alpha*alpha-1)*vp*vp,sp*sp-1-(beta*beta-1)*tp*tp,beta-1-4*yp*qb,beta+up*a1-alpha-up*a2,vp-yp*yp*qv,sp+up*s1-xp-up*s2,tp+4*yp*t1-k0-4*yp*t2,yp-k0-dyk,w-B0-dwb,w-k0-dwk,M-m0-Jp,alpha*alpha-1-((w+1)**2-1)*(w*g)**2,2*alpha*B0-M-B0*B0-1,xp+M*r1-yp*(alpha-B0)-m0-M*r2]
degrees=[s.Poly(p,*leaves).total_degree() for p in polys]
assert degrees==[4,4,4,2,2,3,2,2,1,1,1,2,6,2,2]
assert s.Poly(polys[12],*leaves).coeff_monomial(w**4*g**2)==-1
assert 13+2+11==26 and 6+6+16+2*26==80 and 13+2*15==43

triples=set()
for aa,bb,cc in [(3,4,5),(5,12,13),(16,63,65),(33,56,65),(119,120,169)]:
    for aa,bb in [(aa,bb),(bb,aa)]:
        for sa in (-1,1):
            for sb in (-1,1): triples.add((sa*aa,sb*bb,cc))
arithmetic=0
for a,b,c in sorted(triples):
    C,S=1,0
    for n in range(31):
        P=c**n; radix=4*P+2*c+1
        assert lcm(F(C,P).denominator,F(S,P).denominator)==P
        if n: assert gcd(C,c)==gcd(S,c)==1
        assert C*C+S*S==P*P
        assert abs(C)<=P and abs(S)<=P
        assert a+abs(b)*radix>2
        assert 2*P*(1+radix)<radix*radix+1
        # S here uses signed b, unlike the manuscript's absolute-b S.
        absS=S if b>0 else -S
        assert (pow(a+abs(b)*radix,n,radix*radix+1)-C-radix*absS)%(radix*radix+1)==0
        arithmetic+=1
        C,S=a*C-b*S,b*C+a*S

receipt={'status':'PASS','scope':'Fresh independent exact displayed-formula checks; no author/upstream code, physical simulation, event selection, or Pell-witness instantiation','fixtures':summary,'totals':dict(totals),'generic_symbolic_checks':['shear factorization modulo a^2+b^2=c^2','QM=NQ','L restoration world line','H restoration world line'],'power_residual_degrees':degrees,'power_leaves':26,'outer_leaves':28,'native_witnesses':'1+80J','native_equations':'1+43J','sos_degree':12,'signed_ordered_triples':len(triples),'denominator_radix_cases':arithmetic,'exponents':[0,30],'checker_sha256':sha(Path(__file__))}
(HERE/'ALGEBRA_RECEIPT.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='fixtures'},indent=2,sort_keys=True))
