"""Exact character tails and independent precision-refined ordinary moments.

The x-integrals use the preserved EM balanced kernel and analytically
integrated, exact-rational tail coefficients. This is NOT interval evidence.
Run from any working directory; all output stays beside this script.
"""
from pathlib import Path
from functools import lru_cache
from math import factorial, gcd, prod
import importlib.util
import json
import sys
import mpmath as mp
import sympy as sp

HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'.git').exists())
sys.dont_write_bytecode=True
SOURCE=ROOT/'Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/balanced-stieltjes-moments/code/balanced.py'
spec=importlib.util.spec_from_file_location('preserved_balanced_character',SOURCE)
balanced=importlib.util.module_from_spec(spec); spec.loader.exec_module(balanced)
PARAMS={3:(3,()),5:(5,()),21:(3,(7,)),273:(3,(7,13))}


def character(f,r):
    r%=f
    if not r: return 0
    if f==3: return 1 if r==1 else -1
    if f==5: return 1 if r in (1,4) else -1
    raise ValueError(f)


@lru_cache(None)
def Lnegative(d,k):
    f,removed=PARAMS[d]
    base=-sp.Rational(f)**k/sp.Integer(k+1)*sum(
        character(f,r)*sp.bernoulli(k+1,sp.Rational(r,f)) for r in range(1,f))
    return sp.factor(base*prod(1-character(f,p)*sp.Integer(p)**k for p in removed))


def asmp(x):
    x=sp.Rational(x)
    return mp.mpf(int(x.p))/int(x.q)


def exact_audit():
    rows=[]
    for d,(f,removed) in PARAMS.items():
        parity=1 if f==3 else 0
        zeros=[]
        for k in range(9):
            value=Lnegative(d,k)
            expected=(k%2==parity) or (k==0 and bool(removed))
            assert bool(value==0)==expected
            zeros.append({'k':k,'L_minus_k':str(value),'expected_zero':expected,'pass':True})
        # Recompute directly at the imprimitive modulus, not via Euler factors.
        dictionary=[]
        for k in range(9):
            direct=-sp.Rational(d)**k/sp.Integer(k+1)*sum(
                (character(f,r) if gcd(r,d)==1 else 0)*sp.bernoulli(k+1,sp.Rational(r,d))
                for r in range(1,d))
            assert sp.factor(direct-Lnegative(d,k))==0
            dictionary.append({'k':k,'pass':True})
        rows.append({'modulus':d,'conductor':f,'removed_primes':list(removed),
                     'tails':zeros,'direct_modulus_checks':dictionary})
    # Symbolic Euler polynomial gcd diagnostics complement the cited general theorem.
    a=sp.symbols('a')
    euler=[]
    for q in range(1,17):
        g=sp.factor(sp.gcd(sp.euler(q-1,a),sp.euler(q,a)))
        assert sp.expand(g-(a*a-a-1 if q==5 else 1))==0
        euler.append({'q':q,'gcd':str(g),'pass':True})
    return {'character_records':rows,'finite_euler_gcd_checks':euler}


def run(dps,n,r,base_cutoff,tail_order):
    mp.mp.dps=dps
    threshold=mp.mpf('1e-30')
    kernels={q:balanced.Kernel(q,n,r) for q in (0,1,2)}

    @lru_cache(None)
    def primitive(f,q,x):
        if q==0:
            return -mp.fsum(character(f,j)*mp.digamma((x+j)/f)
                            for j in range(1,f))/f
        return mp.fsum(character(f,j)*kernels[q](x/f,mp.mpf(j)/f)
                       for j in range(1,f))/f

    def kernel(d,q,x):
        f,removed=PARAMS[d]
        result=mp.mpf(0)
        for mask in range(1<<len(removed)):
            selected=[p for j,p in enumerate(removed) if mask>>j&1]
            scale=prod(selected)
            coefficient=(-1)**len(selected)*prod(character(f,p) for p in selected)
            result+=mp.mpf(coefficient)/scale*primitive(f,q,x/scale)
        return result

    def integral(d,q,m):
        f,removed=PARAMS[d]
        T=mp.mpf(base_cutoff*prod(removed))
        # Prove each forbidden coefficient zero exactly; no tolerance deletion.
        for k in range(q,m):
            assert Lnegative(d,k)==0
        def integrand(x):
            if not x: return mp.mpf(0)
            return x**(m-1)*kernel(d,q,x)
        core=mp.quad(lambda t:4*t**3*integrand(t**4),[0,1])
        points=sorted(set(map(mp.mpf,(1,8,base_cutoff,T))))
        core+=mp.quad(integrand,points)
        tail=mp.mpf(0)
        for k in range(max(q,m),tail_order+1):
            coefficient=((-1)**k*asmp(Lnegative(d,k))*factorial(q)
                         *balanced.pochhammer_coefficients(k,q)[q]/mp.factorial(k))
            tail+=coefficient*T**(m-k-1)/(k+1-m)
        return core+tail,core,tail,T

    L2=mp.dirichlet(2,[0,1,-1])
    L3=mp.dirichlet(3,[0,1,-1,-1,1])
    primitive3=-3*mp.sqrt(3)/(4*mp.pi)*L2
    primitive5=-25*mp.sqrt(5)/(4*mp.pi**2)*L3
    cases=[(3,1,2,primitive3),(5,2,3,primitive5),
           (21,0,1,mp.log(7)/3),(21,0,2,9*mp.sqrt(3)/(2*mp.pi)*L2),
           (21,1,2,9*mp.sqrt(3)/(2*mp.pi)*L2),
           (273,0,1,mp.mpf(0)),(273,0,2,-54*mp.sqrt(3)/mp.pi*L2)]
    records=[]; values={}
    for d,q,m,rhs in cases:
        lhs,core,tail,T=integral(d,q,m)
        error=abs(lhs-rhs); values[d,q,m]=lhs
        record={'modulus':d,'q':q,'m':m,'lhs':mp.nstr(lhs,dps),
                'rhs':mp.nstr(rhs,dps),'core':mp.nstr(core,dps),'tail':mp.nstr(tail,dps),
                'cutoff':str(T),'absolute_error':mp.nstr(error,12),
                'pass':bool(error<threshold)}
        records.append(record)
        print('moment',dps,d,q,m,mp.nstr(error,8),flush=True)
    difference=abs(values[21,0,2]-values[21,1,2])
    records.append({'kind':'vanishing_combination','formula':'M(21,0,2)-M(21,1,2)',
                    'absolute_error':mp.nstr(difference,12),'pass':bool(difference<threshold)})

    # Defining finite generalized-Stieltjes sum, separate from dilation and EM.
    x=mp.mpf(3)/2
    fixed=[]
    for d,q in ((3,1),(5,2),(21,0),(21,1),(273,0)):
        f,_=PARAMS[d]
        L=mp.log(x/d)
        def C(a):
            # Laurent subtraction term sums to zero for these characters.
            return mp.fsum((-1)**j*sp.binomial(q,j)*L**(q-j)*
                           (-mp.digamma(x/d+a) if j==0 else mp.stieltjes(j,x/d+a))
                           for j in range(q+1))
        direct=mp.fsum((character(f,j) if gcd(j,d)==1 else 0)*C(mp.mpf(j)/d)
                       for j in range(1,d) if gcd(j,d)==1)/d
        err=abs(direct-kernel(d,q,x))
        fixed.append({'modulus':d,'q':q,'x':'3/2','absolute_error':mp.nstr(err,12),
                      'pass':bool(err<threshold)})
        print('fixed',dps,d,q,mp.nstr(err,8),flush=True)

    # Deliberately wrong controls: missing i, missing conductor power, omitted Euler factor.
    controls=[('missing_odd_phase_i',abs(values[3,1,2]-primitive3/mp.j)),
              ('missing_conductor_power',abs(values[5,2,3]-primitive5/25)),
              ('dropped_imprimitive_Euler_factor',abs(values[21,1,2]-primitive3))]
    controls=[{'kind':name,'wrong_formula_residual':mp.nstr(err,12),'rejected':bool(err>mp.mpf('1e-4'))}
              for name,err in controls]
    return {'precision':dps,'em_n':n,'em_r':r,'tail_order':tail_order,
            'absolute_tolerance':'1e-30','moments':records,'fixed_stieltjes':fixed,
            'negative_controls':controls,'status':'PASS' if all(z['pass'] for z in records+fixed)
             and all(z['rejected'] for z in controls) else 'FAIL'}


def nonreal_audit(dps):
    """Test phase and conjugation using a quartic primitive character mod5.

    This supplements, rather than replaces, the ordinary quadratures above.
    The left side differentiates the defining finite Hurwitz L-function;
    the right side evaluates its positive-order functional-equation value.
    """
    mp.mp.dps=dps
    chi=[mp.mpc(0),mp.mpc(1),mp.j,-mp.j,mp.mpc(-1)]
    conjugate=[mp.conj(c) for c in chi]
    tau=mp.fsum(chi[r]*mp.exp(2*mp.pi*mp.j*r/5) for r in range(1,5))
    def hurwitz_L(s):
        return mp.power(5,-s)*mp.fsum(chi[r]*mp.zeta(s,mp.mpf(r)/5)
                                     for r in range(1,5))
    rows=[]
    for q in (1,3):
        n=(q-1)//2
        lhs=(-1)**q*mp.diff(hurwitz_L,-q)
        factor=(-1)**n*mp.j*tau*mp.factorial(q)*mp.power(5,q)/(2*mp.power(2*mp.pi,q))
        rhs=factor*mp.dirichlet(q+1,conjugate)
        wrong=factor*mp.dirichlet(q+1,chi)
        err=abs(lhs-rhs)
        rejection=abs(lhs-wrong)
        row={'modulus':5,'character_residues':['0','1','i','-i','-1'],'q':q,
             'lhs_minus1_power_q_times_Lprime':mp.nstr(lhs,dps),
             'rhs_with_conjugate_character':mp.nstr(rhs,dps),
             'gauss_sum':mp.nstr(tau,dps),'absolute_error':mp.nstr(err,12),
             'wrong_unconjugated_residual':mp.nstr(rejection,12),
             'pass':bool(err<mp.mpf('1e-30')),
             'wrong_conjugation_rejected':bool(rejection>mp.mpf('1e-4'))}
        rows.append(row)
        print('quartic_phase',dps,q,mp.nstr(err,8),'wrong_conjugation',mp.nstr(rejection,8),flush=True)
    return {'precision':dps,'kind':'functional-equation phase/conjugation diagnostics, not ordinary quadrature',
            'records':rows,'status':'PASS' if all(z['pass'] and z['wrong_conjugation_rejected']
                                               for z in rows) else 'FAIL'}


if __name__=='__main__':
    exact=exact_audit()
    output={'evidence':'Exact rational finite checks plus NONINTERVAL precision-refined quadrature',
            'exact':exact,'runs':[]}
    path=Path(__file__).with_suffix('.json')
    for args in ((50,40,34,64,64),(65,56,44,80,80)):
        output['runs'].append(run(*args))
        path.write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    output['nonreal_phase']=[nonreal_audit(dps) for dps in (50,65)]
    output['status']='PASS' if all(r['status']=='PASS' for r in output['runs']+output['nonreal_phase']) else 'FAIL'
    path.write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    assert output['status']=='PASS'
    print('PASS: exact character tails, Euler-factor dictionaries, gcd diagnostics, and both numerical refinements',flush=True)
