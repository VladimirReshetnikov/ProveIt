#!/usr/bin/env python3
"""Exact and numerical regression tests. mpmath is NOT interval arithmetic."""
import argparse,csv,json,sys,time
from pathlib import Path
from fractions import Fraction as F
import mpmath as mp
import sympy as sp
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'/'stieltjes_tower'))
import tower as T

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--full',action='store_true');args=ap.parse_args()
 out=ROOT/'data'/'stieltjes_tower';out.mkdir(parents=True,exist_ok=True)
 mp.mp.dps=55;start=time.time();report={'status':'running','precision_digits':55,'full':args.full,'categories':{},'interval_certificates':False,'hurwitz_guard_digits':'10 + ceil((k+1)*max(0,log10(a)))','fourier_order_derivative':'40-point Cauchy trapezoid, radius 1/16'}
 def save(): (out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
 def done(name,cases,**kw):
  report['categories'][name]={'cases':cases,'status':'passed',**kw};save();print(name,cases,kw,flush=True)
 def close(a,b,tol=mp.mpf('1e-40')):
  e=abs(a-b)/max(1,abs(a),abs(b));assert e<tol,(mp.nstr(a,18),mp.nstr(b,18),mp.nstr(e,8));return e
 cases=checks=0
 for q in range(2,61 if args.full else 25):
  for s in [2,3,7]:
   uq,E=T.extension_matrix(q,s)
   for i,a in enumerate(uq):assert E[a]==[F(int(i==j)) for j in range(len(uq))]
   assert all(x==E[0][0] for x in E[0]) and E[0][0]!=0
   for row in T.distribution_rows(q,s):
    nz=[(a,x) for a,x in enumerate(row) if x]
    for j in range(len(uq)):
     assert sum((F(x)*E[a][j] for a,x in nz),F(0))==0;checks+=1
   cases+=1
 done('exact_distribution_extensions',cases,coefficient_equalities=checks)
 cases=0
 for q in range(2,25 if args.full else 13):
  for s in [2,3]:
   D=sp.Matrix(T.distribution_rows(q,s));assert D.rank()==q-len(T.units(q));assert D[:,1:].rank()==q-len(T.units(q));cases+=1
 done('independent_exact_matrix_ranks',cases)
 z,w=sp.symbols('z w');C=[]
 for j in range(5):
  ex=sum(w**l*(z**l/sp.Integer(l)+z**(l+1)/sp.Integer(l+1)) for l in range(1,j+1))
  C.append(sp.expand(sp.series(sp.exp(ex),w,0,j+1).removeO()).coeff(w,j))
 assert C[1]==z+z**2/2;assert sp.expand(C[2]-(z**2+5*z**3/6+z**4/8))==0
 (out/'central_moment_operators.json').write_text(json.dumps([str(c) for c in C],indent=2)+'\n');done('symbolic_central_moment_operators',5)
 cases=0;err=mp.mpf(0)
 for n in range(4):
  for k in [1,2,4]:
   for a in [mp.mpf('0.7'),mp.mpf('2.3')]:
    err=max(err,close(T.normalized_stieltjes(n,k,a),T.normalized_integral(n,k,a)));cases+=1
 done('independent_mellin_integrals',cases,max_relative_residual=mp.nstr(err,8))
 cases=0;err=mp.mpf(0)
 for n in range(3):
  a=mp.mpf('1.25');v=mp.diff(lambda x:mp.stieltjes(n,x),a)
  err=max(err,close(v,T.stieltjes_derivative(n,1,a)));cases+=1
 done('direct_stieltjes_parameter_derivatives',cases,max_relative_residual=mp.nstr(err,8))
 cases=0;ratio=mp.mpf(0)
 for n in range(5):
  for k in [2,5,12]:
   for a in [mp.mpf('0.5'),mp.mpf(2)]:
    error=abs(T.finite_sum(n,k,a,30)-T.stieltjes_derivative(n,k,a));bound=T.tail_bound(n,k,a,30,mp.mpf('0.7'))
    assert error<bound;ratio=max(ratio,error/bound);cases+=1
 done('analytic_tail_bound_crosschecks',cases,max_error_over_bound=mp.nstr(ratio,8))
 cases=0;err=mp.mpf(0)
 for rho in [mp.mpf(0),mp.mpf('0.5')]:
  for n in range(4):
   k=3;a=mp.mpf('1.7');v=T.finite_sum(n,k,a,300,rho)*(-1)**(n+k)*a**(k+1)/mp.factorial(k)
   err=max(err,close(v,T.normalized_integral(n,k,a,rho)));cases+=1
 done('lerch_kernel_generalization',cases,max_relative_residual=mp.nstr(err,8))
 cases=0;err=mp.mpf(0)
 chars=[('chi3',[0,1,-1]),('chi4',[0,1,0,-1]),('chi5quad',[0,1,-1,-1,1]),('chi5quartic',[0,1,mp.j,-mp.j,-1])]
 for name,chi in chars:
  q=len(chi);eps=0 if chi[-1]==1 else 1
  for k in [1,2,3]:
   delta=int(eps==k%2);R=3
   pos=mp.taylor(lambda t:T.lseries(k+1+t,chi),0,R);bar=[mp.conj(x) for x in chi]
   neg=mp.taylor(lambda t:T.lseries(-k+t,bar),0,R+delta)
   if delta:assert abs(neg[0])<mp.mpf('1e-45');neg=neg[1:]
   lp=T.log_coefficients(pos,R);lv=T.log_coefficients(neg,R)
   for r in range(1,R+1):
    lhs=mp.factorial(r)*(lp[r]+(-1)**(r+1)*lv[r]);rhs=T.bridge_cumulant(r,k,q,delta)
    err=max(err,close(lhs,rhs,mp.mpf('1e-38')));cases+=1
 done('regularized_functional_equation_cumulants',cases,max_relative_residual=mp.nstr(err,8))
 cases=0;err=mp.mpf(0)
 for q in [3,4]:
  k=n=a=1;root=mp.exp(2*mp.pi*mp.j/q);vals=[]
  for b in range(q):
   z=root**b if b else mp.mpf(1);f=lambda s:mp.polylog(s,z)
   # A fixed Cauchy trapezoid avoids tiny-step order differentiation at integers.
   R=mp.mpf(1)/16;N=40
   derivative=mp.fsum(f(k+1+R*mp.exp(2*mp.pi*mp.j*j/N))*mp.exp(-2*mp.pi*mp.j*j/N) for j in range(N))/(N*R)
   vals.append(derivative+(mp.harmonic(k)+mp.log(q))*f(k+1))
  rhs=(-1)**(n+k)*mp.factorial(k)*q**k*sum(root**(-a*b)*vals[b] for b in range(q))
  err=max(err,close(rhs,T.stieltjes_derivative(n,k,mp.mpf(a)/q),mp.mpf('1e-36')));cases+=1
 done('polylog_order_jet_fourier_bridge',cases,max_relative_residual=mp.nstr(err,8))
 cases=0
 for k in range(1,13):
  lo=mp.exp(mp.harmonic(k-1));hi=mp.exp(mp.harmonic(k))
  assert T.normalized_stieltjes(1,k,lo)>0 and T.normalized_stieltjes(1,k,hi)<0
  assert abs(T.finite_sum(1,k,hi,1,0))<mp.mpf('1e-45');cases+=1
 done('first_zero_harmonic_brackets',cases)
 rows=[];cases=0;err=mp.mpf(0);quaderr=mp.mpf(0);quadcases=0
 for rho in [mp.mpf(0),mp.mpf('0.5'),mp.mpf(1)]:
  x,c,d=T.zero_slopes(1,rho)[0];g=rho/(mp.exp(1/c)-rho)
  b=c/24+g*(g+1)/c-g*(g+1)*(2*g+1)/(2*c*c)
  close(T.zero_next_coefficient(1,x,c,d,rho),b)
 done('first_zero_third_coefficient',3)
 for n in range(1,5):
  for j,(x,c,d) in enumerate(T.zero_slopes(n),1):
   b1=T.zero_next_coefficient(n,x,c,d)
   for k in [10,40,160]:
    predicted=k*c+d
    a=mp.findroot(lambda a:T.normalized_stieltjes(n,k,a),(predicted-mp.mpf('.025'),predicted+mp.mpf('.025')),tol=mp.mpf('1e-42'))
    residual=abs(T.normalized_stieltjes(n,k,a));assert residual<mp.mpf('1e-38') and a>0,(n,j,k,mp.nstr(residual,8));err=max(err,residual)
    if (n,j,k) in [(1,1,40),(2,2,160),(4,4,40),(4,4,160)]:
     qe=abs(T.normalized_concentration(n,k,a));assert qe<mp.mpf('1e-40'),(n,j,k,mp.nstr(qe,8));quaderr=max(quaderr,qe);quadcases+=1
    rows.append([n,j,k,*[mp.nstr(v,40) for v in [x,c,d,b1,a,predicted,predicted+b1/k,k*(a-predicted),k*k*(a-predicted-b1/k)]]]);cases+=1
 with (out/'zero_asymptotics.csv').open('w',newline='') as f:
  cw=csv.writer(f);cw.writerow(['n','root','k','appell_root','slope','offset','coefficient_b1','observed_zero','two_term_prediction','three_term_prediction','k_times_error','k_squared_three_term_error']);cw.writerows(rows)
 done('zero_locations_and_two_term_asymptotics',cases,max_normalized_residual=mp.nstr(err,8))
 done('scale_first_quadrature_at_large_order_zeros',quadcases,max_normalized_residual=mp.nstr(quaderr,8))
 report.update(status='passed',total_cases=sum(v['cases'] for v in report['categories'].values()),elapsed_seconds=round(time.time()-start,3),versions={'python':sys.version.split()[0],'mpmath':mp.__version__,'sympy':sp.__version__})
 save();print('ALL CHECKS PASSED',report['total_cases'],report['elapsed_seconds'],flush=True)
if __name__=='__main__':
 try:
  main()
 except Exception as exc:
  path=ROOT/'data'/'stieltjes_tower'/'verification.json'
  data=json.loads(path.read_text()) if path.exists() else {}
  data.update(status='failed',exception=repr(exc));path.write_text(json.dumps(data,indent=2)+'\n')
  raise
