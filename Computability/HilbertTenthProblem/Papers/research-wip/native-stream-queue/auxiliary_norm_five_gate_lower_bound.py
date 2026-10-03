#!/usr/bin/env python3
"""Exact symbolic audit of a five-gate lower bound at three independent ports.
The general circuit-normal-form argument is in the companion note.
"""
import argparse, hashlib, json
from pathlib import Path
import sympy as s

def need(value,message):
    if not value: raise ValueError(message)

def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) is list: return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def verify():
    K,V,y,c=s.symbols('K V y c')
    P=K*V**2+(1-K)*y**2
    cubic=s.Poly(sum(a*K**m[0]*V**m[1]*y**m[2] for m,a in s.Poly(P,K,V,y).terms() if sum(m)==3),K,V,y)
    need(s.expand(cubic.as_expr()-K*(V-y)*(V+y))==0,'actual cubic part')
    need(s.Poly(P,K,V,y).total_degree()==3,'degree three')
    need(s.gcd(s.Poly(V**2-y**2,V,y),s.Poly(y**2,V,y)).as_expr()==1,'primitive linear K polynomial')
    need(s.Poly(P,K,V,y).is_irreducible,'independent irreducibility check')
    planes=[]
    for name,replacement,expected,variables in [
        ('K=c',{K:c},c*V**2+(1-c)*y**2,(V,y)),
        ('V=y+c',{V:y+c},2*c*K*y+c*c*K+y*y,(K,y)),
        ('V=-y+c',{V:-y+c},-2*c*K*y+c*c*K+y*y,(K,y))]:
        restricted=s.expand(P.subs(replacement))
        need(s.expand(restricted-expected)==0,'exact affine-plane restriction')
        poly=s.Poly(restricted,*variables)
        quad={str(m):str(a) for m,a in poly.terms() if sum(m)==2}
        coefficients=[a for m,a in poly.terms() if sum(m)==2]
        # No value of c over Qbar can make all quadratic coefficients vanish.
        ideal=s.groebner(coefficients,c)
        need(list(ideal)==[1],'all affine offsets excluded symbolically')
        planes.append(dict(plane=name,restriction=str(restricted),quadratic_coefficients=quad,coefficient_ideal_basis=[str(z) for z in ideal]))
    A,B,C,D,E,a,b,u,v,z=s.symbols('A B C D E a b u v z')
    Q=A*B
    normal=(a*Q+u)*v+b*Q+z
    reduced=(Q+u/a)*(a*v+b)+z-b*u/a
    need(s.expand(normal-reduced)==0,'two-product affine normal form, a nonzero')
    # Both second-product operands containing Q would have this nonzero quartic.
    need(s.Poly((a*Q+u)*(b*Q+v),A,B).coeff_monomial(A*A*B*B)==a*b,'uncancellable fourth degree')
    rows=[['V2','*','V','V'],['y2','*','y','y'],['difference','-','V2','y2'],['weighted','*','K','difference'],['output','+','weighted','y2']]
    env={'K':K,'V':V,'y':y}
    for n,op,x,t in rows:
        env[n]=env[x]*env[t] if op=='*' else env[x]+env[t] if op=='+' else env[x]-env[t]
    need(s.expand(env['output']-P)==0,'actual five-gate attainment')
    terms=[dict(exponents=list(m),coefficient=int(a)) for m,a in s.Poly(P,K,V,y).terms()]
    need(len(terms)==3,'three nonzero monomials preclude a binomial')
    return dict(status='PASS_SHARP_ABSTRACT_COMPONENT_BOUND',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        independent_ports=['K','V','y'],polynomial_terms=terms,degree=3,
        primitive_linear_coefficient_gcd='1',irreducible_over_Q=True,
        affine_hyperplane_restrictions=planes,two_multiplication_normal_form_checked=True,
        lower_bounds=dict(multiplications=3,additions_subtractions=2,total=5),
        attaining_source=rows,attaining_ledger=dict(M=3,A=2,total=5),
        scope='Straight-line exact polynomial computation over Q from independent K,V,y and fixed constants, with binary +,-,* and reuse. No divisions, tests, algebraic relations, other paid ports or coordinate changes. General normal-form/irreducibility arguments in the note establish the lower bounds; symbolic checks audit their identities. No lower bound on the complete universal circuit or supplied-square specializations.')

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify()
    if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact receipt')
    if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:r[k] for k in ('status','lower_bounds','attaining_ledger')}))
if __name__=='__main__':main()
