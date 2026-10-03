#!/usr/bin/env python3
"""Reproduce exact checks and three horizon-free quartic certificates.

All probability and algebra tests use exact integers or SymPy rationals.
Finite testing complements, but does not replace, the manuscript's proofs.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from math import factorial,gcd
from pathlib import Path
import json
import platform
import random
import sys
import sympy as sp
from quantum_loops import (example_data,group_inverse,normalized_factorial_moments,
                           stopped_pgf,regulator_mean)
from quartic import Circuit,group_core,full_certificate,all_moments_certificate
from verify_certificate import check as independently_check,evaluate

ROOT=Path(__file__).resolve().parents[1]
COUNTS=Counter()


def require(condition,category):
    COUNTS[category]+=1
    if not condition:
        raise AssertionError(f'Failed check in {category}')


def matrix_strings(m):
    return [[str(m[i,j]) for j in range(m.cols)] for i in range(m.rows)]


def canonical_checks():
    for n in range(-20,21):
        for d in range(1,13):
            c=Circuit(); w=c.rational('q',Fraction(n,d))
            require(all(r.evaluate(c.values)==0 for r in c.residuals),'canonical_fraction')
            nn=w.value.numerator; dd=w.value.denominator
            us=[u for u in range(dd) if (nn*u-1)%dd==0]
            require(len(us)==1,'bounded_bezout_uniqueness')
    rng=random.Random(20261002)
    for _ in range(180):
        a=Fraction(rng.randint(-20,20),rng.randint(1,12))
        b=Fraction(rng.randint(-20,20),rng.randint(1,12))
        c=Circuit(); aw=c.rational('a',a,True); bw=c.rational('b',b,True)
        cw=c.add(aw,bw); dw=c.add(aw,bw,True); ew=c.mul(aw,bw)
        require((cw.value,dw.value,ew.value)==(a+b,a-b,a*b),'rational_gate_values')
        require(all(r.evaluate(c.values)==0 for r in c.residuals),'rational_gate_residuals')
        c.stats(); require(True,'rational_gate_counts')


def matrix_checks():
    data={}; z,eps=sp.symbols('z epsilon')
    for name,ex in example_data().items():
        t=ex['T']; x=ex['x']; e=ex['exits']; ell=ex['ell']; D=t.rows
        g,p=group_inverse(t); a=sp.eye(D)-t
        for identity in (a*g+p==sp.eye(D),g*a+p==sp.eye(D),a*p==sp.zeros(D),g*p==sp.zeros(D)):
            require(identity,'group_inverse_equations')
        if 'K' in ex:
            k,h=ex['K'],ex['H']
            require(k.conjugate().T*k+h.conjugate().T*h==sp.eye(k.rows),'kraus_normalization')
            require(ex['rho'].trace()==1 and ex['rho'].is_positive_semidefinite,'initial_density')
        require(ell*t+sum((e[i,:] for i in range(e.rows)),sp.zeros(1,D))==ell,
                'trace_conservation')
        f=stopped_pgf(t,x,e,z); moments=normalized_factorial_moments(t,x,e,max(5,D-1))
        for j in range(e.rows):
            for k in range(6):
                derivative=sp.cancel(sp.diff(f[j],z,k).subs(z,1)/factorial(k))
                require(derivative==moments[j,k],'pgf_derivative_moments')
        w=sp.cancel((ell*p*x)[0])
        require(sp.cancel(sum(f)-0).subs(z,1)==1-w,'total_exit_probability')
        for n in range(10):
            coefficient=sp.diff(f[0],z,n).subs(z,0)/factorial(n)
            require(sp.cancel(coefficient-(e*t**n*x)[0])==0,'finite_word_probabilities')
        mean=regulator_mean(t,x,ell,eps)
        require(sp.cancel(mean-w/eps-(ell*g*(sp.eye(D)+eps*t*g).inv()*x)[0])==0,
                'exact_regulator_resolvent')
        analytic=sp.cancel(mean-w/eps)
        for k in range(4):
            coefficient=sp.diff(analytic,eps,k).subs(eps,0)/factorial(k)
            require(sp.cancel(coefficient-(-1)**k*(ell*g*(t*g)**k*x)[0])==0,
                    'regulator_laurent_coefficients')
        require(sp.limit(eps*mean,eps,0,dir='+')==w,'regulator_scaled_first_moment')
        u=sp.symbols('u')
        hh=t*g; q=sp.expand((sp.eye(D)-u*hh).det())
        for j in range(e.rows):
            series=sum(moments[j,k]*u**k for k in range(D))
            numerator=sp.series(q*series,u,0,D).removeO()
            require(sp.cancel(f[j].subs(z,1+u)-numerator/q)==0,'all_moments_rational_recurrence')
        if D <= 4:
            tt=sp.symbols('t'); r=len(a.nullspace())
            if r:
                det=sp.Poly((a+tt*sp.eye(D)).det(),tt)
                h0=det.nth(r); h1=det.nth(r+1)
                adj=(a+tt*sp.eye(D)).adjugate()
                B0=adj.applyfunc(lambda v: sp.Poly(v,tt).nth(r-1))
                B1=adj.applyfunc(lambda v: sp.Poly(v,tt).nth(r))
                require(B0/h0==p,'rank_stratum_projection_formula')
                require((B1*h0-B0*h1)/h0**2==g,'rank_stratum_inverse_formula')
        data[name]=dict(dimension=D,T=matrix_strings(t),G=matrix_strings(g),P=matrix_strings(p),
                        initial=matrix_strings(x),exits=matrix_strings(e),
                        nontermination=str(w),pgf=str(f[0]),moments=matrix_strings(moments),
                        mean_resolvent_finite_part=str((ell*g*x)[0]),regulator_mean=str(mean))
    ex=example_data()['rotating_dark_qutrit']
    t=ex['T']; x=ex['x']; ell=ex['ell']; w=sp.Rational(5,9)
    for n in range(20):
        require((ell*t**n*x)[0]==w+sp.Rational(4,9)*sp.Rational(9,25)**n,'dark_rotation_survival')
    require((t**2*x-t*x)[:2]!=[0,0],'dark_rotation_is_nonstationary')
    try:
        group_inverse(sp.eye(2)-sp.Matrix([[0,1],[0,0]]))
    except ValueError:
        require(True,'nonsemisimple_rejection')
    else:
        require(False,'nonsemisimple_rejection')
    pvar=sp.symbols('p',positive=True)
    aa=pvar*sp.Matrix([[1,-1],[-1,1]])
    pp=sp.ones(2)/2; gg=sp.Matrix([[1,-1],[-1,1]])/(4*pvar)
    hh=gg+sp.exp(pvar)*pp
    require((aa*hh*aa-aa).applyfunc(sp.simplify)==sp.zeros(2),'nonrational_generalized_inverse')
    require((gg*pp)==sp.zeros(2),'canonical_counterexample_inverse')
    for D in (1,2,4):
        t=sp.diag(*[sp.Rational(i+1,2*(D+1)) for i in range(D)])
        g,p=group_inverse(t); c,*_=group_core(t,g,p)
        require(c.stats()['natural_variables']==88*D**3+9*D**2+14,'dense_core_variable_count')
        require(c.stats()['quadratic_residuals']==72*D**3+7*D**2+10,'dense_core_residual_count')
    return data


def certificate_checks():
    reports={}
    for name in ('scalar_geometric','partial_qubit','coherent_qubit','coherent_qubit_all_moments'):
        path=ROOT/'examples'/f'{name}_certificate.json'
        cert=(all_moments_certificate(example_data()['coherent_qubit'],path)
              if name.endswith('_all_moments') else full_certificate(example_data()[name],3,path))
        checked=independently_check(json.loads(path.read_text()))
        require(True,'independent_certificate_check')
        # Change every single witness coordinate by +1. Check only incident
        # residuals; this is exact and avoids repeated full-file scans.
        incident=[[] for _ in cert['witness']]
        for residual in cert['residuals']:
            for i in set(i for _,ids in residual for i in ids):
                incident[i].append(residual)
        values=cert['witness'].copy()
        for i in range(len(values)):
            values[i]+=1
            require(any(evaluate(r,values)!=0 for r in incident[i]),'single_coordinate_mutation_rejected')
            values[i]-=1
        reports[name]=dict(file=path.name,bytes=path.stat().st_size,
                           statistics=cert['statistics'],independent_check=checked)
    return reports


def geometric_checks():
    # Exact word normalization for a concrete complete, nontrivial 2-outcome
    # instrument. The general undecidability construction uses the cited
    # 15-dimensional theorem, not this decidable test device.
    import itertools
    A0=sp.Matrix([[1,0],[0,0]]); A1=sp.Matrix([[0,0],[0,1]])
    rho=sp.eye(2)/2; r2=sp.Rational(9,25); s2=sp.Rational(16,25)
    for n in range(7):
        total=0
        for word in itertools.product((A0,A1),repeat=n):
            product=sp.eye(2)
            for a in word:
                product=a*product
            original=sp.trace(product*rho*product.T)
            wrapped=s2*r2**n*original
            require((original==0)==(wrapped==0),'geometric_support_preservation')
            total+=wrapped
        require(total==s2*r2**n,'geometric_total_law')


def main():
    (ROOT/'examples').mkdir(exist_ok=True); (ROOT/'verification').mkdir(exist_ok=True)
    canonical_checks(); data=matrix_checks(); geometric_checks(); reports=certificate_checks()
    (ROOT/'examples'/'exact_results.json').write_text(json.dumps(data,indent=2)+'\n')
    result=dict(status='PASS',python=platform.python_version(),sympy=sp.__version__,
                assertions_total=sum(COUNTS.values()),assertions_by_category=dict(COUNTS),
                certificate_reports=reports,
                scope='Exact finite tests; general theorems rest on manuscript proofs. No Lean build.')
    (ROOT/'verification'/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    text='PASS: '+str(result['assertions_total'])+' exact assertions\n'
    text+='\n'.join(f'{k}: {v}' for k,v in COUNTS.items())+'\n'
    text+='\nCertificate summaries:\n'+json.dumps(reports,indent=2)+'\n'
    (ROOT/'verification'/'results.txt').write_text(text)
    print(text)


if __name__=='__main__':
    main()
