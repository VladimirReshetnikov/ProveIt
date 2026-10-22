#!/usr/bin/env python3
"""Owned finite transcription check; standard library, no received code imports.
The formula lists below transcribe the three displayed systems in the report.
They are compared algebraically with the literal JSON residuals, up to sign.
"""
import ast, json, hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
if not (ROOT/'quadratic').is_dir():
 ROOT=HERE.parent/'evidence/diophantine_zfc_round2'
# A sparse monomial is a sorted tuple of variable names, with repeats.
def c(n): return {():n} if n else {}
def add(p,q):
 r=p.copy()
 for m,v in q.items():
  r[m]=r.get(m,0)+v
  if not r[m]:del r[m]
 return r
def neg(p):return {m:-v for m,v in p.items()}
def mul(p,q):
 r={}
 for m,v in p.items():
  for n,w in q.items():
   k=tuple(sorted(m+n));r[k]=r.get(k,0)+v*w
 return {m:v for m,v in r.items() if v}
def power(p,n):
 r=c(1)
 for _ in range(n):r=mul(r,p)
 return r
mapping={'J':'Jrep','z':'transport_quotient','T':'auxiliary_quotient','tau':'tau_root','t':'tau_tail','y':'y_aux','beta':'Bm1','K0':'Kconstant','MC':'MC','MFs':'MF','C2':'C2','F2':'F2','V0':'V0','Ba':'Baux'}
def parse(s,env=None):
 env=env or {}
 def rec(x):
  if isinstance(x,ast.Constant) and isinstance(x.value,int):return c(x.value)
  if isinstance(x,ast.Name):return env.get(x.id,{(mapping.get(x.id,x.id),):1})
  if isinstance(x,ast.UnaryOp) and isinstance(x.op,ast.USub):return neg(rec(x.operand))
  if isinstance(x,ast.BinOp):
   if isinstance(x.op,ast.Add):return add(rec(x.left),rec(x.right))
   if isinstance(x.op,ast.Sub):return add(rec(x.left),neg(rec(x.right)))
   if isinstance(x.op,ast.Mult):return mul(rec(x.left),rec(x.right))
   if isinstance(x.op,ast.Pow) and isinstance(x.right,ast.Constant):return power(rec(x.left),x.right.value)
  raise ValueError(ast.dump(x))
 return rec(ast.parse(s,mode='eval').body)
env={}
for k,v in [('q','beta*J+1'),('k','eta+zeta'),('H','4*a+3'),('C','q-F-alpha')]:env[k]=parse(v,env)
systems={
'ordinary_quartic33':[
'L-(q*q-1)','N-q*(L+1)','X-w*q','a-E-s*N','E-X*(a-E)','c-k*(a-E)-eta','P-E*(c-eta)-k','tau*tau-P*(P-k)-1','D-X-a*c-gamma*H','Delta-a*a-H','C2-c*c','D*D-Delta*C2-1','k-R-1-h*E','G-(q-1)*(q-F)-alpha','R-G*L-(MC+q*MFs)*J','(K0+w)*C+q-F-z*(q-1)-1','F2-f*f','V0-T*f+1','V-c*V0+R*F2','g-y*y+V*V','I-i*C2','Ba-I*I','Ba-Delta*(F2-1)','y*y-Ba*g-1'],
'start_only_sextic25':[
'L-q*q+1','a-E-s*q*(L+1)','E-w*q*(a-E)','c-k*(a-E)-eta','t*t+E*(c-eta)*(2*t-k)-1','D-w*q-a*c-gamma*H','Delta-a*a-H','D*D-1-Delta*c*c','k-R-1-h*E','R-L*((q-1)*(q-F)+alpha)-(MC+q*MFs)*J','(K0+w)*C+q-F-z*(q-1)-1','V-c*(T*f-1)+R*f*f','I-i*(D*D-1)','Ba-I*I','Ba-Delta*(f*f-1)','y*y-Ba*(y*y-V*V)-1'],
'ordinary_octic20':[
'a-E-s*q**3','E-w*q*(a-E)','c-k*(a-E)-eta','tau*tau-E*(c-eta)*(E*(c-eta)+k)-1','(w*q+a*c+gamma*H)**2-Delta*c*c-1','R-((q-1)*(q-F)+alpha)*(q*q-1)-(MC+q*MFs)*J','(K0+w)*C+q-F-z*(q-1)-1','V-c*(T*f-1)+R*f*f','I-i*c*c','I*I-Delta*(f*f-1)','I*I*(V*V-y*y)+y*y-1']}
results={}
for name,forms in systems.items():
 e=env.copy()
 if name=='ordinary_octic20':
  e['Delta']=parse('a*a+H',e);e['R']=parse('k-1-h*E',e)
 p=ROOT/'quadratic'/f'{name}.json';data=json.loads(p.read_text())
 if len(forms)!=len(data['residual_polynomials']):raise ValueError('residual count')
 for i,(f,g) in enumerate(zip(forms,data['residual_polynomials']),1):
  a,b=parse(f,e),parse(g)
  if a!=b and a!=neg(b):raise ValueError((name,i))
 results[name]={'displayed_residuals':len(forms),'all_residuals_identical_up_to_sign':True,'json_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
receipt={'scope':'Exact standard-library sparse-polynomial comparison of manually transcribed report equations with literal final JSON; no semantic/Pell/compiler theorem is established by this check.','results':results}
(HERE/'REPORT_EQUATION_CHECK.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
