#!/usr/bin/env python3
"""Seven fully paid fixed-input original-frame first-hit quartics; stdlib only."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

BASE='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/'
PINS={
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_original_frame_first_hit30_intake.md':'96d0e1fef873ea4d2ef8fcf8139fb047a52b4535786e7860183de882b27c33a6',
 BASE+'19-mass-four-zd-timed-PROOF.md':'103fe38f7c6d941995e579d7d73dd42ab3836a012666ba16858b158ff698d4c5',
 BASE+'20-orbit-geometry-original-frame-PROOF.md':'385c455537ee7c4631fd5400918b57602bc08c26383fe71f99b3345791964a8f',
 BASE+'20-orbit-geometry-first-visit-PROOF.md':'3247951ca7afa4d65bd3eb90d99bfb48fcb43dbf0eaa067c3e9380cdfbcebbda',
 BASE+'20-orbit-geometry-geometry-PROOF.md':'3f05b484cd3c0035422df431f571bb2b56c85a31d5f49ae681033ffb2ca6e4fa'}
EXTERNAL=['Lx','Ly','Hx','Hy','Rx','Ry','phase']
COMMON=['e','sEn','sEj','sEk','sWn','sWj','sWk','t']
MODES=('generic_square','shared_cycle','direct_clock')
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def typed(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(typed(a[k],b[k]) for k in a)
 if type(a) is list:return len(a)==len(b) and all(typed(x,y) for x,y in zip(a,b))
 return a==b
class Circuit:
 def __init__(self,ports):self.ports=ports;self.rows=[]
 def op(self,op,a,b):
  if type(a) is int and type(b) is int:return a+b if op=='+' else a-b if op=='-' else a*b
  if op=='+' and a==0:return b
  if op in ('+','-') and b==0:return a
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  n='r'+str(len(self.rows));self.rows.append([n,op,a,b]);return n
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def sq(self,a):return self.mul(a,a)
 def sum(self,xs):
  z=0
  for x in xs:z=self.add(z,x)
  return z

def build(mode,project_phase=False):
 need(mode in MODES,'mode');w=[x for x in COMMON if x!='e' or not project_phase]+(['U'] if mode=='generic_square' else ['N'] if mode=='shared_cycle' else [])
 c=Circuit(EXTERNAL+w)
 e=c.sub(1,'phase') if project_phase else 'e'
 f='phase' if project_phase else c.sub(1,e)
 a=c.sub('Rx',4);b=c.add(a,1);h=c.sub('Hx',1)
 v=c.sub(c.sub('Rx','Hx'),1);wlo=c.sub(v,1)
 n0=c.add(a,e);base_y=c.add('t',n0)
 residuals=[c.mul(e,c.sub(e,1))]
 for selector,affine,slack in [(e,b,'sEn'),(e,h,'sEj'),(e,v,'sEk'),(f,a,'sWn'),(f,wlo,'sWj'),(f,h,'sWk')]:
  residuals.append(c.sub(c.mul(selector,affine),slack))
 residuals.extend(['Lx',c.sub('Hy','Ly'),c.sub('Ly',base_y),c.sub(c.sub('Ry','Ly'),f)])
 if not project_phase:residuals.append(c.sub('phase',f))
 common_end=len(c.rows)
 if mode=='shared_cycle':
  residuals.append(c.sub('N',n0))
  kW=c.sub(c.add(a,'Rx'),'Hx')
  kval=c.add(kW,c.mul(e,c.sub(h,kW)))
  polynomial=c.add(c.add(c.sq('N'),c.mul(3,'N')),kval)
  residuals.append(c.sub('t',polynomial))
 else:
  signed_head=c.mul(c.sub(e,f),'Hx')
  if mode=='generic_square':
   residuals.append(c.sub('U',c.sq('Rx')))
   quadratic=c.sub('U',c.mul(3,'Rx'))
  else:quadratic=c.mul('Rx',b)
  residuals.append(c.add(c.sub(c.sub('t',quadratic),signed_head),e))
 final_start=len(c.rows);output=c.sum(c.sq(r) for r in residuals)
 return dict(mode=mode,project_phase=project_phase,external=EXTERNAL.copy(),witnesses=w,source=c.rows,residuals=residuals,common_end=common_end,final_start=final_start,output=output)

def build_unified():
 c=Circuit(EXTERNAL+['j','r','t']);e=c.sub(1,'phase')
 boolean=c.mul('phase',e);b=c.sub('Rx',3);n0=c.sub(b,'phase')
 left=c.sub(c.sub('Hx',1),'j');right=c.sub(c.add(c.sub(n0,'Hx'),2),'r')
 residuals=[boolean,left,right,'Lx',c.sub('Hy','Ly'),c.sub(c.sub('Ly','t'),n0),c.sub(c.sub('Ry','Ly'),'phase')]
 signed_head=c.mul(c.sub(e,'phase'),'Hx');quadratic=c.mul('Rx',b)
 residuals.append(c.add(c.sub(c.sub('t',quadratic),signed_head),e))
 final_start=len(c.rows);out=c.sum(c.sq(r) for r in residuals)
 return dict(mode='unified_direct',project_phase=True,external=EXTERNAL.copy(),witnesses=['j','r','t'],source=c.rows,residuals=residuals,common_end=None,final_start=final_start,output=out)

# Independent ordinary sparse polynomial ring, including exact rational tests.
def con(n):return {():n} if n else {}
def var(n):return {(n,):1}
def add(a,b,s=1):
 r=dict(a)
 for m,c in b.items():r[m]=r.get(m,0)+s*c
 return {m:c for m,c in r.items() if c}
def mul(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
 return {m:c for m,c in r.items() if c}
def sq(a):return mul(a,a)
def sc(n,p):return mul(con(n),p)
def sum_poly(xs):
 r={}
 for x in xs:r=add(r,x)
 return r

def reference(mode):
 e=var('e');f=add(con(1),e,-1);R=var('Rx');H=var('Hx');t=var('t')
 n0=sum_poly([R,con(-4),e])
 residuals=[mul(e,add(e,con(-1)))]
 aff=[add(R,con(-3)),add(H,con(-1)),sum_poly([R,sc(-1,H),con(-1)]),add(R,con(-4)),sum_poly([R,sc(-1,H),con(-2)]),add(H,con(-1))]
 for sel,A,s in zip([e,e,e,f,f,f],aff,COMMON[1:7]):residuals.append(add(mul(sel,A),var(s),-1))
 residuals.extend([var('Lx'),add(var('Hy'),var('Ly'),-1),sum_poly([var('Ly'),sc(-1,t),sc(-1,n0)]),sum_poly([var('Ry'),sc(-1,var('Ly')),sc(-1,f)]),add(var('phase'),f,-1)])
 direct=sum_poly([t,sc(-1,sq(R)),sc(3,R),sc(-1,mul(add(sc(2,e),con(-1)),H)),e])
 if mode=='direct_clock':residuals.append(direct)
 elif mode=='generic_square':
  J=add(var('U'),sq(R),-1);residuals.extend([J,add(direct,J,-1)])
 else:
  N=var('N');B=residuals[0];J=add(N,n0,-1)
  delta=add(B,mul(J,sum_poly([N,n0,con(3)])))
  residuals.extend([J,add(direct,delta,-1)])
 return residuals,sum_poly(sq(r) for r in residuals)

def reference_unified():
 p=var('phase');e=add(con(1),p,-1);R=var('Rx');H=var('Hx');t=var('t');n0=sum_poly([R,con(-3),sc(-1,p)])
 C=sum_poly([t,sc(-1,sq(R)),sc(3,R),sc(-1,mul(add(e,p,-1),H)),e])
 rows=[mul(p,e),sum_poly([H,con(-1),sc(-1,var('j'))]),sum_poly([R,sc(-1,H),con(-1),sc(-1,p),sc(-1,var('r'))]),var('Lx'),add(var('Hy'),var('Ly'),-1),sum_poly([var('Ly'),sc(-1,t),sc(-1,n0)]),sum_poly([var('Ry'),sc(-1,var('Ly')),sc(-1,p)]),C]
 return rows,sum_poly(sq(r) for r in rows)

def expand(p):
 env={n:var(n) for n in p['external']+p['witnesses']}
 for n,op,a,b in p['source']:
  a=con(a) if type(a) is int else env[a];b=con(b) if type(b) is int else env[b]
  env[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
 return env

def run(p,values):
 env=dict(values)
 for n,op,a,b in p['source']:
  a=a if type(a) is int else env[a];b=b if type(b) is int else env[b]
  env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return env

def audit(p):
 known=set(p['external']+p['witnesses']);defs={};cnt=Counter()
 need(len(known)==len(p['external'])+len(p['witnesses']),'unique supplied ports')
 for n,op,a,b in p['source']:
  need(n not in known and op in ('+','-','*'),'fresh valid instruction')
  need(all(type(x) is int or type(x) is str and x in known for x in (a,b)),'closed graph')
  known.add(n);defs[n]=(a,b);cnt['M' if op=='*' else 'A']+=1
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n) is int or n in live:continue
  live.add(n)
  if n in defs:todo.extend(defs[n])
 need(live==known,'all paid gates and supplied ports live')
 need(len(p['source'])-p['final_start']==2*len(p['residuals'])-1,'entire squares and final sum paid')
 return dict(M=cnt['M'],A=cnt['A'],operations=sum(cnt.values()),witnesses=len(p['witnesses']),residuals=len(p['residuals']),finalizer_operations=2*len(p['residuals'])-1)

# Literal single-head specialization of the four printed CA rewrite rules.
# F is obtained by applying G, then shifting every occupied site up one unit.
def step_F(state):
 heads=[(p,s) for p,s in state.items() if s in ('E','W')];need(len(heads)==1,'fixture single head')
 p,h=heads[0];x,y=p;s=dict(state)
 def label(q):return state.get(q,'0')
 if h=='E' and label((x+1,y))=='0':
  del s[p];s[x+1,y]='E'
 elif h=='E' and label((x+1,y))=='u' and label((x+2,y+1))=='0':
  s[p]='W';del s[x+1,y];s[x+2,y+1]='u'
 elif h=='W' and label((x-1,y))=='0':
  del s[p];s[x-1,y]='W'
 elif h=='W' and label((x-1,y))=='u' and label((x,y+1))=='0' and label((x-1,y+1))=='0':
  del s[p];del s[x-1,y];s[x,y+1]='E';s[x-1,y+1]='u'
 need(sum(1 if a=='u' else 2 for a in s.values())==4,'mass conserved on fixture')
 return {(x,y+1):v for (x,y),v in s.items()}

def chart(n,j,e):
 need(n>=0 and 0<=j<=n+1 and e in (0,1),'chart input')
 if e:
  t=n*n+3*n+j;H=1+j;R=n+3;dy=0;label='E'
 else:
  t=n*n+4*n+2+j;H=n+2-j;R=n+4;dy=1;label='W'
 points=[(0,n+t),(H,n+t),(R,n+t+dy)]
 need(points[0]<points[1]<points[2],'strict complete-target sorting')
 state=dict(zip(points,['u',label,'u']))
 ext=dict(zip(EXTERNAL,[*points[0],*points[1],*points[2],1-e]))
 w=dict(e=e,t=t,sEn=e*(R-3),sEj=e*(H-1),sEk=e*(R-H-1),sWn=(1-e)*(R-4),sWj=(1-e)*(R-H-2),sWk=(1-e)*(H-1))
 need(all(type(x) is int and x>=0 for x in w.values()),'natural canonical witnesses')
 return state,ext,w

def substitute(poly,maps):
 out={}
 for monomial,coefficient in poly.items():
  term=con(coefficient)
  for x in monomial:term=mul(term,maps.get(x,var(x)))
  out=add(out,term)
 return out

def verify(repo):
 for p,h in PINS.items():need(sha((repo/p).read_bytes())==h,'input pin '+p)
 packets=[];totals=Counter();refs={}
 for projected in (False,True):
  for mode in MODES:
   p=build(mode,projected);bill=audit(p);env=expand(p);rows,whole=reference(mode)
   if projected:
    maps={'e':add(con(1),var('phase'),-1)}
    rows=[substitute(r,maps) for i,r in enumerate(rows) if i!=11]
    whole=substitute(whole,maps)
   need([env[r] if type(r) is str else con(r) for r in p['residuals']]==rows,'all literal residual coefficients')
   need(env[p['output']]==whole,'full polynomial coefficients')
   top='phase' if projected else 'e'
   need(max(map(len,whole))==4 and whole[(top,)*4]==1,'exact degree-four coefficient')
   p['ledger']=bill;p['exact_degree']=4;p['monomials']=len(whole);p['coefficient_sha256']=sha(stable([[list(m),c] for m,c in sorted(whole.items())]));packets.append(p);refs[(mode,projected)]=whole
   totals.update(sources=1,live_gates=bill['operations'],residual_coefficient_proofs=len(rows),full_polynomial_proofs=1)
 for projected in (False,True):
  pp=[p for p in packets if p['project_phase']==projected]
  need(all(p['source'][:p['common_end']]==pp[0]['source'][:pp[0]['common_end']] for p in pp),'identical paid membership within each coordinate interface')
 for mode in MODES:
  old,new=[p for p in packets if p['mode']==mode]
  need(old['ledger']['operations']-new['ledger']['operations']==3 and old['ledger']['witnesses']-new['ledger']['witnesses']==1,'exact phase-coordinate projection saving')
  need(substitute(refs[(mode,False)],{'e':add(con(1),var('phase'),-1)})==refs[(mode,True)],'whole phase graph pullback')
 direct=refs[('direct_clock',False)];R=var('Rx');e=var('e');n0=sum_poly([R,con(-4),e]);B=mul(e,add(e,con(-1)))
 C=reference('direct_clock')[0][-1]
 J=add(var('U'),sq(R),-1);corr=add(sc(2,sq(J)),sc(2,mul(C,J)),-1)
 need(add(refs[('generic_square',False)],direct,-1)==corr,'generic full correction')
 L=add(var('N'),n0,-1);delta=add(B,mul(L,sum_poly([var('N'),n0,con(3)])))
 corr=sum_poly([sq(L),sq(delta),sc(-2,mul(C,delta))])
 need(add(refs[('shared_cycle',False)],direct,-1)==corr,'cycle full correction')
 need(substitute(refs[('generic_square',False)],{'U':sq(R)})==direct,'generic unconditional whole pullback')
 need(add(substitute(refs[('shared_cycle',False)],{'N':n0}),direct,-1)==add(sq(B),sc(2,mul(C,B)),-1),'cycle Boolean-qualified pullback')
 p=build_unified();bill=audit(p);env=expand(p);rows,whole=reference_unified()
 need([env[r] for r in p['residuals']]==rows and env[p['output']]==whole,'unified entire source coefficients')
 need(max(map(len,whole))==4 and whole[('phase',)*4]==1,'unified exact quartic')
 p['ledger']=bill;p['exact_degree']=4;p['monomials']=len(whole);p['coefficient_sha256']=sha(stable([[list(m),c] for m,c in sorted(whole.items())]));packets.append(p)
 totals.update(sources=1,live_gates=bill['operations'],residual_coefficient_proofs=len(rows),full_polynomial_proofs=1)
 for p in packets:
  whole=reference_unified()[1] if p['mode']=='unified_direct' else refs[(p['mode'],p['project_phase'])]
  for k in range(12):
   vv={n:Fraction((i+2*k)%11-5,3) if k>=8 else (i+2*k)%11-5 for i,n in enumerate(p['external']+p['witnesses'])}
   actual=run(p,vv)[p['output']];expected=sum(c*product(vv[x] for x in m) for m,c in whole.items());need(actual==expected,'signed/rational output')
  totals.update(offzero_values=12,rational_values=4)
 state={(0,0):'u',(1,0):'E',(3,0):'u'};fixtures=[];t=0
 for n in range(8):
  for ebit in (1,0):
   for j in range(n+2):
    want,ext,w=chart(n,j,ebit);need(w['t']==t and want==state,'exact own CA step versus half-open chart')
    zeros=[]
    for p in packets:
     ww={key:w[key] for key in p['witnesses'] if key in w}
     if p['mode']=='generic_square':ww['U']=ext['Rx']**2
     if p['mode']=='shared_cycle':ww['N']=n
     if p['mode']=='unified_direct':ww.update(j=ext['Hx']-1,r=ext['Rx']-ext['Hx']-1-ext['phase'])
     need(set(ww)==set(p['witnesses']) and all(v>=0 for v in ww.values()),'complete natural coordinate map')
     need(run(p,{**ext,**ww})[p['output']]==0,'complete natural zero')
     # Unified inverse to the original six natural branch slacks, proved n>=0.
     if p['mode']=='unified_direct':
      ee=1-ext['phase'];rr=ww['r'];jj=ww['j'];nn=ext['Rx']-3-ext['phase']
      restored=dict(e=ee,sEn=ee*nn,sEj=ee*jj,sEk=ee*rr,sWn=ext['phase']*nn,sWj=ext['phase']*rr,sWk=ext['phase']*jj,t=ww['t'])
      need(restored==w,'unified full old-coordinate inverse')
     zeros.append(dict(mode=p['mode'],project_phase=p['project_phase'],witness=ww))
    fixtures.append(dict(n=n,j=j,E_phase=ebit,external=ext,zeros=zeros))
    totals.update(genuine_configurations=1,genuine_zeros=len(packets));state=step_F(state);t+=1
 need(t==88 and state==chart(8,0,1)[0],'complete eight-cycle ownership and next section')
 boundaries=[];p=packets[-1]
 for phase in (0,1):
  # If n0=-1, all spatial equations can hold, but the only clock is negative.
  base=dict(Lx=0,Ly=-1,Hx=1,Hy=-1,Rx=2+phase,Ry=-1+phase,phase=phase,j=0,r=0,t=0)
  value=run(p,base)[p['output']];need(value==(2-phase)**2,'negative-index boundary rejected with natural time')
  signed=dict(base,t=phase-2,Ly=phase-3,Hy=phase-3,Ry=2*phase-3)
  need(run(p,signed)[p['output']]==0 and signed['t']<0,'signed-only boundary requires negative time')
  boundaries.append(dict(phase=phase,natural_time_zero_value=value,signed_zero=signed))
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,scope='Seven complete fixed-input first-hit quartics for the stated mass-four weighted CA orbit. No arbitrary CA compiler, universality, real-witness uniqueness, or global optimum claim.',counts=dict(totals),packets=packets,fixtures=fixtures,negative_index_boundaries=boundaries,corrections=dict(generic='2J^2-2CJ; J=U-Rx^2',cycle='L^2+Delta^2-2C*Delta; L=N-(Rx-4+e), Delta=e(e-1)+L(N+Rx-4+e+3)'))

def product(xs):
 z=1
 for x in xs:z*=x
 return z

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args()
 d=json.loads(json.dumps(verify(a.repo)))
 if a.output:a.output.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
 if a.expect:need(typed(d,json.loads(a.expect.read_text())),'exact typed receipt')
 print(json.dumps(dict(status='PASS',**d['counts']),sort_keys=True))
if __name__=='__main__':main()
