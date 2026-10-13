"""Independent diagnostic computations, not interval certificates."""
import json, math, pathlib, sys, importlib.util
import mpmath as mp
sys.dont_write_bytecode=True
repo=next(parent for parent in pathlib.Path(__file__).resolve().parents
          if (parent/'Analysis/Polylogarithms/docs').is_dir())
src=repo/'Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/balanced-stieltjes-moments/code/balanced.py'
spec=importlib.util.spec_from_file_location('bsm_source',src)
bsm=importlib.util.module_from_spec(spec); spec.loader.exec_module(bsm)
out=pathlib.Path(__file__).with_suffix('.json')
mp.mp.dps=36
tolerance=mp.mpf('1e-28')

def J(p,s,a):
    Q=1 if p==0 else (mp.digamma(s)+mp.euler if p==1 else (mp.digamma(s)+mp.euler)**2+mp.polygamma(1,s)-mp.zeta(2))
    return mp.pi/mp.sin(mp.pi*s)*mp.zeta(1-s,a)*Q

def check(p,q,v,a,b):
    v,a,b=map(mp.mpf,(v,a,b))
    fp=(lambda x:mp.log(x)-mp.digamma(x+a)) if p==0 else bsm.Kernel(p,n=40,r=27)
    fq=(lambda x:mp.log(x)-mp.digamma(x+b)) if q==0 else bsm.Kernel(q,n=40,r=27)
    cp=lambda x:fp(x) if p==0 else fp(x,a)
    cq=lambda x:fq(x) if q==0 else fq(x,b)
    f=lambda x:x**(v-1)*cp(x)*cq(x)
    lhs=mp.quad(lambda t:4*t**3*f(t**4),[0,1])+mp.quad(f,[1,4,16,mp.inf])
    c=v/2
    g=lambda t:mp.re(J(p,c+1j*t,a)*J(q,v-c-1j*t,b))/mp.pi
    rhs=mp.quad(g,[0,1,2,4,8,16,24])
    error=abs(lhs-rhs)
    row=dict(p=p,q=q,v=str(v),a=str(a),b=str(b),direct=mp.nstr(lhs,34),barnes=mp.nstr(rhs,34),absolute_error=mp.nstr(error,8),spectral_cutoff=24,diagnostic_pass=bool(error<tolerance))
    print(row,flush=True)
    return row
rows=[check(*case) for case in [(0,0,'1','1','1'),(0,1,'1','1','0.5'),(1,1,'2.5','0.75','1.25')]]
gram=[]
for p,q in [(0,0),(1,0),(1,1),(2,1),(3,2)]:
    a=mp.mpf('1.25')
    f=lambda x:mp.log(x/(x+a))**(p+q)/(x+a)**2
    lhs=mp.quad(lambda t:4*t**3*f(t**4),[0,1])+mp.quad(f,[1,5,mp.inf])
    rhs=(-1)**(p+q)*mp.factorial(p+q)/a
    error=abs(lhs-rhs)
    gram.append(dict(p=p,q=q,a=str(a),direct=mp.nstr(lhs,34),exact=mp.nstr(rhs,34),absolute_error=mp.nstr(error,8),diagnostic_pass=bool(error<tolerance)))
import sympy as sp
matrix_checks=[]
for N in range(7):
    M=sp.Matrix(N+1,N+1,lambda i,j:sp.factorial(i+j))
    target=sp.prod(sp.factorial(j)**2 for j in range(N+1))
    matrix_checks.append(dict(N=N,determinant=str(M.det()),target=str(target),pass_exact=M.det()==target))
passed=all(row['diagnostic_pass'] for row in rows+gram) and all(row['pass_exact'] for row in matrix_checks)
payload=dict(status='PASS' if passed else 'FAIL',diagnostic_absolute_tolerance=str(tolerance),precision=mp.mp.dps,evidence_kind='noninterval independent quadrature plus exact finite determinants',barnes=rows,factorial_gram=gram,determinants=matrix_checks)
out.write_text(json.dumps(payload,indent=2)+'\n')
if not passed:
    raise SystemExit('FAIL: a numerical diagnostic or exact finite identity failed')
print('PASS: 8 noninterval diagnostics and 7 exact finite determinants',flush=True)
