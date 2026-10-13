"""Noninterval checks of the logarithmic identities and positive kappa integral.

The order-15 point is established by exact algebraic evidence, not quadrature.
Here its universal coefficient is evaluated two ways, and low-order ordinary
kernel moments check the signs independently. All EM tails are truncated.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
from functools import lru_cache
import mpmath as mp
import sympy as sp

HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'.git').exists())
SOURCE=ROOT/'Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/balanced-stieltjes-moments/code/balanced.py'
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('balanced_for_logarithms',SOURCE)
balanced=importlib.util.module_from_spec(spec)
spec.loader.exec_module(balanced)

def normhash(path):
    return hashlib.sha256(path.read_text(encoding='utf-8').replace('\r\n','\n').encode('utf-8')).hexdigest()

def coefficients(dps):
    mp.mp.dps=dps
    z=sp.Symbol('z')
    rows=[]
    for q in (1,4,15):
        p=sp.Poly(sp.prod(1+k*z for k in range(1,q+1)),z)
        finite=(q+1)*mp.fsum((-1)**r*int(p.nth(r))*mp.zeta(r+2) for r in range(q+1))
        positive=mp.quad(lambda t:(t/mp.expm1(t))**(q+1) if t else mp.mpf(1),[0,1,4,mp.inf])
        error=abs(finite-positive)
        rows.append({'q':q,'finite_zeta':mp.nstr(finite,dps),
                     'positive_integral':mp.nstr(positive,dps),'absolute_error':mp.nstr(error,12),
                     'pass':bool(error<mp.mpf('1e-30'))})
    return {'precision':dps,'records':rows,'status':'PASS' if all(r['pass'] for r in rows) else 'FAIL'}

def moments(dps,n,r,T,tail_order):
    mp.mp.dps=dps
    a=mp.mpf(1)/2
    T=mp.mpf(T)
    kernels={q:balanced.Kernel(q,n,r) for q in (1,2)}
    @lru_cache(maxsize=None)
    def colored(q,x):
        return (kernels[q](x/2,a/2)-kernels[q](x/2,(a+1)/2))/2
    def A(k):
        if k%2: return mp.mpf(0) # exact Euler parity at a=1/2
        return (mp.bernpoly(k+1,a)-2**(k+1)*mp.bernpoly(k+1,a/2))/(k+1)
    def integral(q,log_power):
        def f(x):
            if not x:return mp.mpf(0)
            return x*mp.log(x)**log_power*colored(q,x)
        core=mp.quad(lambda t:4*t**3*f(t**4),[0,1])+mp.quad(f,[1,8,T])
        tail=mp.mpf(0)
        for k in range(2,tail_order+1):
            Ak=A(k)
            coefficient=(-1)**k*Ak*mp.factorial(q)*balanced.pochhammer_coefficients(k,q)[q]/mp.factorial(k)
            factor=T**(1-k)/(k-1)
            if log_power:factor*=mp.log(T)+1/mp.mpf(k-1)
            tail+=coefficient*factor
        return core+tail,core,tail
    phi=lambda s:2**(-s)*(mp.zeta(s,a/2)-mp.zeta(s,(a+1)/2))
    first=mp.diff(phi,-1)
    second=mp.diff(phi,-1,2)
    alpha=mp.zeta(2)-1
    kappa=2*(mp.zeta(2)-mp.zeta(3))
    cases=((1,0,-first),(1,1,-alpha*first+second/2),(2,0,mp.mpf(0)),(2,1,-kappa*first))
    rows=[]
    controls=[]
    for q,j,rhs in cases:
        lhs,core,tail=integral(q,j)
        err=abs(lhs-rhs)
        rows.append({'q':q,'log_power':j,'a':'1/2','omega':'-1','weight':'x',
                     'lhs':mp.nstr(lhs,dps),'rhs':mp.nstr(rhs,dps),'core':mp.nstr(core,dps),
                     'tail':mp.nstr(tail,dps),'absolute_error':mp.nstr(err,12),
                     'pass':bool(err<mp.mpf('1e-30'))})
        if q==2 and j==1:
            for label,wrong in (('wrong sign of logarithmic relation',kappa*first),
                                ('omitted kappa factor',-first)):
                residual=abs(lhs-wrong)
                controls.append({'name':label,'wrong_formula_residual':mp.nstr(residual,12),
                                 'rejected':bool(residual>mp.mpf('1e-4'))})
        print('ordinary logarithmic check',dps,q,j,mp.nstr(err,8),flush=True)
    return {'precision':dps,'em_n':n,'em_r':r,'cutoff':str(T),'tail_order':tail_order,
            'records':rows,'negative_controls':controls,
            'status':'PASS' if all(r['pass'] for r in rows) and all(c['rejected'] for c in controls) else 'FAIL'}

if __name__=='__main__':
    out={'evidence':'NONINTERVAL precision refinement; the defining EM and asymptotic tails are truncated.',
         'verifier_sha256_lf':normhash(Path(__file__)),
         'kernel_source_sha256_lf':normhash(SOURCE),
         'coefficient_runs':[coefficients(p) for p in (50,65)],'ordinary_runs':[]}
    path=Path(__file__).with_suffix('.json')
    for args in ((50,32,30,64,72),(65,44,38,80,84)):
        out['ordinary_runs'].append(moments(*args))
        path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    out['status']='PASS' if all(r['status']=='PASS' for r in out['coefficient_runs']+out['ordinary_runs']) else 'FAIL'
    path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    if out['status']!='PASS':raise SystemExit('FAIL: see recorded residuals')
    print('PASS: six positive-coefficient checks and eight ordinary logarithmic moments',flush=True)
