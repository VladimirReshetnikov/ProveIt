#!/usr/bin/env python3
"""Exact first-factor branch counterexamples; not full modified-graph zeros."""
import json,sys
if sys.flags.optimize: raise SystemExit('optimized Python refused')
def need(x,m):
 if not x: raise RuntimeError(m)
def check(s,w,K,rprime,sign):
 J=1; beta=2; F=1; alpha=1; eta=1; zeta=1; MC=1; MF=1
 b=J*beta;q=1+b;X=q*w;Y=q**3*s;k=eta+zeta;Q=X*Y*Y;ell=Q*k
 C=q-F-alpha;Bt=q*(C*(K+w)-F);Z=b*(ell+k+rprime-k*Bt)-Bt
 first=2*Q+1
 need(all(x>0 for x in (J,beta,F,alpha,eta,zeta,s,w,rprime,K)),'positive input')
 need(MC<beta and MF<2*beta and F+alpha<q,'basic port/gap assumptions')
 need(first*first==1+ell*(ell+k),'first norm')
 need(Z==sign*b*first,'signed root')
 need(Z*Z==b*b*(1+ell*(ell+k)),'first residual')
 need(Bt>0 and Bt%b==0 and rprime<=s,'claimed branch properties')
 R=(alpha+(q-F)*b)*(q*q-1)+J*(MC+MF*q)
 return {'branch':sign,'b':b,'q':q,'s':s,'w':w,'K':K,'rprime':rprime,'X':X,'Y':Y,
  'k':k,'Q':Q,'ell':ell,'Bt':Bt,'first':first,'Z':Z,'R':R,
  'rank_remainder':abs((R+1)-k)%(q**4),'first_pell_index':1}
print(json.dumps({'status':'PASS','examples':[check(14,2,1,14,1),check(3,2,20995,3,-1)],
 'scope':'first-factor equations only; neither full modified graph nor the rank congruence is asserted'},indent=2))
