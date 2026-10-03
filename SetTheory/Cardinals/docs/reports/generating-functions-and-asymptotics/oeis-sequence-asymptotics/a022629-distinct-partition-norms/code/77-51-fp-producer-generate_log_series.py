#!/usr/bin/env python3
"""Exact formal coefficients; asymptotic validity is proved separately."""
import argparse,json,pathlib,time
if not __debug__: raise SystemExit('Run without -O; assertions are required.')
import sympy as s

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=pathlib.Path,default=pathlib.Path(__file__).parent);ap.add_argument('--order',type=int,default=6);args=ap.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
 start=time.time();h,P,x=s.symbols('h P x');K=args.order
 if K<3: ap.error('--order must be at least 3')
 def tr(f,n=K+2): return s.series(f,h,0,n).removeO().expand()
 R={1:1/(x-1)}
 for j in range(1,K+2):R[j+1]=s.factor((R[j]+x*s.diff(R[j],x))/(x-1))
 T=0
 for j in range((K+1)//2):
  C=s.simplify(2*(1-s.Rational(1,2)**(2*j+1))*s.zeta(2*j+2)).subs(s.pi**2,P)
  T+=C*R[2*j+1]
 # Expand T in v=1/x before substitution, making all subsequent work polynomial.
 Tv=tr(T.subs(x,1/h),K+2)
 def evalT(L): return tr(Tv.subs(h,tr(1/L)),K+2)
 rho=s.Integer(1);rho_coeff={}
 for k in range(2,K+2):
  c=s.Symbol('c');rr=rho+c*h**k;L=1/h+tr(s.log(rr))
  lhs=tr(h*s.Rational(1,2)*(1-tr(rr**-2))*(L-1)+h*(evalT(L)+tr(s.diff(T,x).subs(x,L))),k+1)
  eq=s.expand(lhs).coeff(h,k);sol=s.solve(eq,c)[0];rho+=sol*h**k;rho_coeff[k]=s.factor(sol)
  print('rho',k,s.factor(sol),flush=True)
 L=1/h+tr(s.log(rho));Q=tr((tr(1/rho)+rho)*L/2-rho+rho*evalT(L),K+1)
 d={j:s.factor(Q.coeff(h,j)) for j in range(1,K+1)}
 assert d[1]==P/6 and d[2]==P/6
 assert s.expand(d[3]-(P/6-P**2/72))==0
 tau=s.Integer(1);tau_coeff={}
 D=sum(d[j]*h**j for j in d)
 for k in range(2,K+2):
  c=s.Symbol('c');rr=tau+c*h**k;L=1/h+tr(s.log(rr))
  rhs=tr(h*(rr*(L-1+tr(D.subs(h,tr(1/L))))-(1/h-1)),k+1)
  sol=s.solve(rhs.coeff(h,k),c)[0];tau+=sol*h**k;tau_coeff[k]=s.factor(sol)
  print('tau',k,s.factor(sol),flush=True)
 inv=tr(tau**2,K+2);b={j:s.factor(inv.coeff(h,j)) for j in range(2,K+2)}
 receipt={'order':K,'symbol':'P=pi^2','log_coefficients':{str(j):str(v) for j,v in d.items()},'saddle_ratio_coefficients':{str(j):str(v) for j,v in rho_coeff.items()},'inverse_squared_ratio_coefficients':{str(j):str(v) for j,v in b.items()},'seconds':time.time()-start}
 (args.output_dir/'log_series_verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
