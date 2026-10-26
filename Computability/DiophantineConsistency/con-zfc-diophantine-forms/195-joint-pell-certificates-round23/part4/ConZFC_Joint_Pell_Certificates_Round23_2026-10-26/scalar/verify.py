#!/usr/bin/env python3
"""Independent exact free-ring cuts, full defect collection, native payloads.
Does not import build.py or any producer. Uses retained attributed sparse ring.
"""
from pathlib import Path
from collections import Counter
import argparse,ast,copy,hashlib,json
from polynomial import Poly
ROOT=Path(__file__).resolve().parent
INPUTS=['J','F','alpha','i','T','w','s','n','eta','zeta'];PORTS=['beta','K0','MC','MF']
def need(x,msg):
 if not x:raise ValueError(msg)
def formulas(mode):
 d={'q':'beta*J+1','C':'q-F-alpha','X':'q*w','k':'eta+zeta','c':'k*s+eta','Am1':'q*s*(X+1)','Hp':'4*Am1-1','Delta':'Am1*(Am1+2)','sixq7':'6*q**7','Dtau':'1+(X*q*q*s*s)*(X*q*q*s*s+1)*k*k','R':'(bJ*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J','Bt':'(K0+w)*C-F','U':'i*c*c','DpI2':'Delta*U*U*Dtau','Df':'DpI2+1','trace_f':'1+2*DpI2','Q':'4*Delta*DpI2*(1+DpI2)','cTR':'c*T-R','V':'trace_f*cTR-c','Kpos':'X*(3*c-2*X)+2','Dg':'Dtau*Df','Mtot':'bJ*sixq7*Hp','eclear':'6*(k-R-1-q**4*s)-(X*q*q*s*s)*k*(k*k-4)','pc_S':'(k*qY)*(V0kk-(k*qY)*(qY+1))'}
 if mode=='scalar':
  d['pc_center']='2*(Am1+1)*U*Dtau-U*pc_S';omega='pc_center*V';weight='cTR*V';scale=4
 else:
  d['pc_center']='U*(2*pc_S*(U*U*cTR*(3*Dtau+(k*qY)**2)-(cTR-c))+(Am1+1)*(4*Dtau*V-U*U*cTR*(4*Dtau**2+3*pc_S**2+(k*qY)**4)))';omega='pc_center';weight='U*Dtau*cTR*cTR';scale=16
 d['Znum']=f'bJ*sixq7*(Hp*(n-({weight})*Bt-({omega}))+Kpos)-Hp*(sixq7*Bt+bJ*eclear)'
 d['RG']=f'{scale}*Mtot*Mtot*Dg'
 d['N']=f'Q*(Znum*Znum-{scale}*Mtot*Mtot*Dg*V*V)+({scale}*Mtot*Mtot*Dg-Znum*Znum)'
 return d

def audit_cuts(g,mode,mutant=False):
 need(g['domain']=='strictly positive integers','domain');need(g['witnesses']==INPUTS,'variables');need(g['fixed_numerals']==PORTS,'ports')
 table={};known=set(INPUTS+PORTS)
 for name,op,a,b in g['source']:
  need(name not in known and op in ['+','-','*'],'ordinary unique gate');need(all(type(x)is int or x in known for x in [a,b]),'topology');table[name]=(op,a,b);known.add(name)
 live=set()
 def mark(x):
  if type(x)is int or x in live:return
  live.add(x)
  if x in table:
   _,a,b=table[x];mark(a);mark(b)
 mark(g['output']);need(live==known,'all gates inputs ports live')
 count=99 if mode=='scalar' else 120
 need(len(table)==count==g['operations'],'operation count')
 if not mutant:need(dict(sorted(Counter(r[1] for r in g['source']).items()))==g['operation_breakdown'],'operation classes')
 covered=set();cuts=[]
 for name,formula in formulas(mode).items():
  names={n.id for n in ast.walk(ast.parse(formula,mode='eval')) if isinstance(n,ast.Name)}
  env={n:Poly.v(n) for n in names};memo=env.copy()
  def expand(x):
   if type(x)is int:return Poly(x)
   if x in memo:return memo[x]
   need(x in table,'unbound cut '+x);covered.add(x);op,a,b=table[x];a,b=expand(a),expand(b);r=a+b if op=='+' else a-b if op=='-' else a*b;memo[x]=r;return r
  need(expand(name)==eval(formula,{'__builtins__':{}},env),'free-ring cut '+name)
  cuts.append(name)
 need(covered==set(table),'uncovered gates '+str(set(table)-covered))
 return {'operations':count,'cut_names':cuts,'all_gates_covered':True}

def quotient(p,j):
 out={}
 for m,v in p.d.items():
  d=dict(m);e=d.get('A',0)
  if e<j:continue
  if e==j:d.pop('A')
  else:d['A']=e-j
  out[tuple(sorted(d.items()))]=v
 return Poly(out)
def degree_top(p,weights):
 need(bool(p.d),'nonzero polynomial');scores={m:sum(weights.get(n,0)*e for n,e in m) for m in p.d};d=max(scores.values());return d,Poly({m:c for m,c in p.d.items() if scores[m]==d})
def subst(p,env):
 out=Poly()
 for m,c in p.d.items():
  t=Poly(c)
  for n,e in m:t=t*env[n]**e
  out=out+t
 return out

def algebra(mode):
 A,N,k,U,b,c=map(Poly.v,['A','N','k','U','b','c'])
 ell=N*(A-N-1)*k;E=1+ell*(ell+k);D=A*A-1;G=E*(1+D*U*U*E);V=(1+2*D*U*U*E)*b-c
 S=quotient(E,1);e0=1+k*k*N*(N+1)*(N*(N+1)-1)
 need(E==A*S+e0,'complete E division')
 need(S==k*N*(ell+k-k*N*(N+1)),'S evaluator')
 weights=dict(zip(['A','N','k','U','b','c'],[4,2,1,5,4,2]))
 if mode=='scalar':
  center=2*A*U*E-U*S;defect=center*center-4*G
  need(defect==4*U*U*E*e0+U*U*S*S-4*E,'scalar exact defect')
  expected=4*U*U*A*A*N**6*k**4
  cd,ct=degree_top(center,weights);dd,dt=degree_top(defect,weights)
  need((cd,dd)==(23,34),'scalar weighted degrees');need(dt==expected,'scalar full defect leader')
 else:
  F=E*V;q1,q3=quotient(F,1),quotient(F,3);need(all(v%2==0 for v in q3.d.values()),'Q3 even');half=Poly({m:v//2 for m,v in q3.d.items()})
  center=U*(4*A*F-2*q1-half);theta=U*U*b;e2=k*k*N*N
  literal=U*(2*S*(theta*(3*E+e2)-(b-c))+A*(4*E*V-theta*(4*E*E+3*S*S+e2*e2)))
  need(center==literal,'all center monomials quotient equality')
  defect=center*center-16*G*V*V
  cd,ct=degree_top(center,weights);dd,dt=degree_top(defect,weights)
  need((len(center.d),len(defect.d),cd,dd)==(84,594,59,94),'whole complete counts/degrees')
  expected=8*A**6*N**8*k**8*U**6*b*b*(A*A-6*N**4);need(dt==expected,'whole defect leader')
 # Actual dependent leading substitution in all ten coordinates, beta weight zero.
 beta,J,w,s,i,eta,zeta,F0=map(Poly.v,['beta','J','w','s','i','eta','zeta','F']);q=beta*J;kk=eta+zeta
 aa=q*q*w*s;nn=q*s;uu=i*(kk*s)**2;bb=-q**3*(q-F0);ee=(q**3*w*s*s*kk)**2
 qq=4*aa**6*uu**4*ee**2;mm=24*q**8*aa;vv=2*aa*aa*uu*uu*ee*bb
 actual=qq*mm*mm*subst(dt,{'A':aa,'N':nn,'k':kk,'U':uu,'b':bb,'c':kk*s})
 if mode=='scalar':
  actual=actual*vv*vv;expect=9*2**12*q**80*w**22*s**56*i**10*kk**32*(q-F0)**2;targetdegree=202;other=[72+108,72+12+23+36+54,24+46,2*(12+23+36)]
 else:
  expect=9*2**11*q**74*w**18*s**52*i**10*kk**32*(q-F0)**2*(w*w-6*s*s);targetdegree=190;other=[72+82,72+12+59+41,24+46,2*(12+59)]
 need(actual==expect,'actual entire output leader');ad,at=degree_top(actual,{n:1 for n in INPUTS});need(ad==targetdegree and at==actual,'actual degree');need(max(other)<targetdegree,'strict dominant term')
 return {'exact_degree':targetdegree,'center_monomials':len(center.d),'defect_monomials':len(defect.d),'center_weighted_degree':cd,'defect_weighted_degree':dd,'actual_leading_terms':len(actual.d),'actual_leading_form':actual.serial(),'full_defect_leader':dt.serial(),'other_output_degree_bounds':other,'formal_quotient_exact':True}

def authenticate(g):
 parentpath=ROOT/'inherited_positive10/start4127_positive10_degree214_ops87.json';need(g['parent']=={'path':str(parentpath.relative_to(ROOT)),'sha256':hashlib.sha256(parentpath.read_bytes()).hexdigest()},'frozen graph parent hash');parent=json.loads(parentpath.read_text());binding=copy.deepcopy(parent['coefficient_binding']);binding['path']='inherited_positive10/native4127/start_only_ports/';binding['certificate']='inherited_positive10/native4127/start_only_certificate.json';need(g['coefficient_binding']==binding,'same whole native tuple')
 cert=ROOT/binding['certificate'];need(hashlib.sha256(cert.read_bytes()).hexdigest()==binding['certificate_sha256'],'native certificate hash')
 receipt={};total=0
 for name,data in binding['ports'].items():
  raw=(ROOT/binding['path']/data['file']).read_bytes();sha=hashlib.sha256(raw).hexdigest();need(sha==data['sha256'],'port hash '+name);total+=len(raw);receipt[name]={'bytes':len(raw),'sha256':sha}
 need(total==97046,'whole tuple raw size');return {'raw_bytes':total,'ports':receipt,'whole_certificate_bound':True}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--mutations',action='store_true');ap.add_argument('--receipt',type=Path);a=ap.parse_args();out=[]
 for mode,deg,ops in [('scalar',202,99),('whole',190,120)]:
  p=ROOT/f'start4127_positive10_degree{deg}_ops{ops}.json';g=json.loads(p.read_text());r={'mode':mode,'status':'pass','graph_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'cuts':audit_cuts(g,mode),'algebra':algebra(mode),'coefficient_authentication':authenticate(g)}
  if a.mutations:
   rejected=0
   for j,row in enumerate(g['source']):
    for op in ['+','-','*']:
     if op==row[1]:continue
     mutant=copy.deepcopy(g);mutant['source'][j][1]=op
     try:audit_cuts(mutant,mode,True)
     except ValueError:rejected+=1
     else:raise ValueError('undetected operator mutation '+row[0])
   need(rejected==2*ops,'mutation total');r['operator_mutations_rejected']=rejected
  out.append(r)
 if a.receipt:a.receipt.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps([{k:v for k,v in r.items() if k not in ['algebra','coefficient_authentication','cuts']}|{'operations':r['cuts']['operations'],'exact_degree':r['algebra']['exact_degree'],'actual_leading_terms':r['algebra']['actual_leading_terms'],'coefficient_raw_bytes':r['coefficient_authentication']['raw_bytes']} for r in out],indent=2))
if __name__=='__main__':main()
