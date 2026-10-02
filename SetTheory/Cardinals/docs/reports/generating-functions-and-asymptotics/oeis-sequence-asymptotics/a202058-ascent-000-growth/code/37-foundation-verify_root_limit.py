#!/usr/bin/env python3
"""Corroborate the explicit bounded-shift calculus; no numerical proof claim."""
import mpmath as mp
import json, hashlib
from pathlib import Path
mp.mp.dps=60
P=Path(__file__).resolve().parent
T=3*mp.pi**2/8
def p(q):return (q+mp.log(2-mp.exp(-q)))/2
def b(q):return mp.exp(p(q))*(-mp.expm1(-q))/q
def t(q):return T-mp.quad(lambda x:1/b(x),[q,mp.inf])
def d(q):return 1/(t(q)*b(q))
def dp(q):return 1/(2-mp.exp(-q))
def dlogb(q):return dp(q)+1/mp.expm1(q)-1/q
def dd(q):return d(q)*(-d(q)-dlogb(q))
rows=[]
for q in [5,10,20,40,80]:
 M=dp(q)/d(q)
 vals=[]
 for v in [-1,-.5,0,.5,1]:
  v=mp.mpf(v)
  pp=-mp.exp(-(q+v))/(2-mp.exp(-(q+v)))**2
  Hpp=pp-M*dd(q+v)
  Md=M*d(q+v)
  assert abs(Hpp)<1
  assert Md>mp.mpf(1)/4
  vals.append({'v':str(v),'Hpp':str(Hpp),'Hpp_limit':str(mp.exp(-v/2)/4),'Md':str(Md),'Md_limit':str(mp.exp(-v/2)/2)})
 rows.append({'q':q,'t':str(t(q)),'M':str(M),'values':vals})
out={'scope':'Finite numerical corroboration of explicit differentiations; not a proof substitute.','article_sha256':hashlib.sha256((P/'a202058-report.tex').read_bytes()).hexdigest(),'calculus':rows}
(P/'verify_root_limit.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: bounded-shift calculus on 25 parameter pairs')
