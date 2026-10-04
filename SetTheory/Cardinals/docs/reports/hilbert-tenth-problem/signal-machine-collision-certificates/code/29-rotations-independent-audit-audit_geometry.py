#!/usr/bin/env python3
"""Fresh exact identities and synthetic boundary-degeneracy checks only.

No physical execution, saved chronology, author code, or numerical tolerance.
The synthetic polygon is an algebraic test of the general geometric lemma,
not a claim that the physical constructor emits this polygon.
"""
from fractions import Fraction as F
from math import gcd,lcm
from pathlib import Path
import hashlib,json
import sympy as s

OUT=Path(__file__).resolve().parent
identities=[]
def zero(name,expr):
    assert s.factor(expr)==0,(name,s.factor(expr))
    identities.append(name)

z,u,t,v,e,Z=s.symbols('z u t v e Z',real=True)
h=(u-1)/(u+1)
zero('L restoration worldline',z+h*(z+u*z)-u*z)
hp=(1-v)/(1+v)
end=v*t+(1-v)*Z
zero('H restoration worldline',t+hp*(2*Z-end-t)-end)
zero('translation endpoint',(1-e)*(t/(1-e))+e*Z-(t+e*Z))
zero('translation L speed',((1/(1-e)-1)/(1/(1-e)+1))-e/(2-e))
zero('translation H speed',((1-(1-e))/(1+(1-e)))-e/(2-e))
zero('translation intermediate-start',t/(1-e)-t-e*t/(1-e))
zero('translation end-intermediate',t+e*Z-t/(1-e)-e*((1-e)*Z-t)/(1-e))
a,b,c=s.symbols('a b c',real=True)
tx=-b/(c+a);ty=b/c
Rx=s.Matrix([[1,tx],[0,1]]);Ry=s.Matrix([[1,0],[ty,1]])
rot=Rx*Ry*Rx-s.Matrix([[a,-b],[b,a]])/c
constraint=a*a+b*b-c*c
for i in range(2):
    for j in range(2):
        num=s.fraction(s.factor(rot[i,j]))[0]
        remainder=s.rem(s.Poly(num,b),s.Poly(constraint,b)).as_expr()
        zero(f'shear identity entry {i}{j} modulo Pythagorean relation',remainder)
n,d,k=s.symbols('n d k',integer=True)
x,y,D=s.symbols('x y D',real=True)
tk=x+k*d*(y-s.Rational(2,3)*D)
zero('micro pair increments once',tk+d*y-s.Rational(2,3)*d*D-(x+(k+1)*d*(y-s.Rational(2,3)*D)))
zero('closed duration start sum',s.summation(tk,(k,0,n-1))-(n*x+d*n*(n-1)*(y-s.Rational(2,3)*D)/2))

def dot(x,y):return sum((a*b for a,b in zip(x,y)),F(0))
def cmul(x,y):return(x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def cpow(base,n):
    if n<0:base=(base[0],-base[1]);n=-n
    result=(F(1),F(0))
    for _ in range(n):result=cmul(result,base)
    return result
R=(F(3,5),F(4,5))
p=(F(1,6),F(-1,6))
rho=dot(p,p)
contacts=[p,cmul(cpow(R,2),p),cmul(cpow(R,-3),p),(-p[0],-p[1])]
triangle=[(F(1,3),F(1),F(0)),(F(1,3),F(-1),F(1)),(F(1,3),F(0),F(-1))]
rows=triangle+[(rho,-q[0],-q[1]) for q in contacts]+[(2*rho,-2*p[0],-2*p[1])]
nearest=[]
for alpha,v,w in rows:
    dist=alpha*alpha/(v*v+w*w)
    if dist==rho:nearest.append((-alpha*v/(v*v+w*w),-alpha*w/(v*v+w*w)))
assert len(nearest)==6 and len(set(nearest))==4 and set(nearest)==set(contacts)
assert all(dot(q,q)==rho and all(dot(row,(F(1),)+q)>=0 for row in rows) for q in contacts)

def quotient(w,q):
    norm=dot(q,q)
    return((w[0]*q[0]+w[1]*q[1])/norm,(w[1]*q[0]-w[0]*q[1])/norm)
def inverse_power_match(eta):
    den=lcm(eta[0].denominator,eta[1].denominator)
    rem=den; exponent=0
    while rem%5==0:
        rem//=5;exponent+=1
    if rem!=1:return False
    return eta==cpow((F(3,5),F(-4,5)),exponent)
def valid(w):
    norm=dot(w,w)
    if norm<rho:return True
    if norm>rho:return False
    return not any(inverse_power_match(quotient(w,q)) for q in set(nearest))
def gaps(w):return(F(1,3)+w[0],F(1,3)+w[1]-w[0],F(1,3)-w[1])
boundary_checks=0; initial_face_hits=[]
for k in range(-50,51):
    w=cmul(cpow(R,k),p)
    assert valid(w)==(k>2)
    assert all(g>=0 for g in gaps(w))
    if not all(g>0 for g in gaps(w)):initial_face_hits.append(k)
    boundary_checks+=1
assert initial_face_hits==[0]
assert valid((F(0),F(0)))
assert not valid((F(1),F(1)))

# Number theoretic stress cases are separate exact integer identities.
# Include both distinct-prime composite c=65 and prime-square c=169.
triples=[]
for A,B,C in [(3,4,5),(5,12,13),(33,56,65),(119,120,169)]:
    for aa,bb in [(A,B),(B,A)]:
        for sa in (-1,1):
            for sb in (-1,1):triples.append((sa*aa,sb*bb,C))
power_checks=0; extraction_checks=0
for a,b,c in triples:
    Cn,Sn=1,0
    for n in range(21):
        P=c**n
        assert gcd(gcd(abs(Cn),abs(Sn)),P)==1
        if n>0: assert gcd(Cn,c)==gcd(Sn,c)==1
        assert Cn*Cn+Sn*Sn==P*P
        brad=4*P+2*c+1
        base=a+abs(b)*brad
        assert base>=2
        # Use |b| orientation for the radix extraction.
        Sabs=Sn if b>0 else -Sn
        assert (pow(base,n,brad*brad+1)-Cn-brad*Sabs)%(brad*brad+1)==0
        assert 2*P*(1+brad)<brad*brad+1 and 2*P<brad
        assert abs(Cn)<=P and abs(Sn)<=P
        power_checks+=1;extraction_checks+=1
        Cn,Sn=a*Cn-b*Sn,b*Cn+a*Sn

def encode(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return{k:encode(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)):return[encode(x) for x in v]
    return v
result={'status':'PASS','scope':'new exact symbolic identities, synthetic multi-contact polygon, and signed/composite-denominator arithmetic; no physical trajectory simulation',
        'symbolic_identity_count':len(identities),'identities':identities,
        'synthetic_polygon':{'radius_squared':rho,'supplied_rows':len(rows),'nearest_rows':len(nearest),'distinct_contacts':len(set(nearest)),'contacts':contacts,'shared_orbit_indices':[-3,0,2],'maximal_forbidden_index':2,'duplicate_contact_rows':3,'initial_face_contact':p,'boundary_checks':boundary_checks,'zero_gap_orbit_indices_in_test':initial_face_hits},
        'signed_ordered_triples':len(triples),'exponents_per_triple':21,'denominator_checks':power_checks,'radix_extraction_checks':extraction_checks,
        'scope_limits':['The synthetic polygon is not asserted to be emitted by the family constructor.','Finite checks support, but do not replace, the arbitrary-parameter conventional proof.']}
(OUT/'GEOMETRY_INDEPENDENT_RECEIPT.json').write_text(json.dumps(encode(result),indent=2)+'\n')
print(json.dumps(encode(result),indent=2))
