"""Bounded source-pinned obstruction to deleting the packed left range lane.

Read-only replay of actual saved full 505 packets. No native Pell witnesses are
materialized; this tests their exact bitwise interface and all five outer rows.
"""
import argparse, hashlib, json
from pathlib import Path
if not __debug__: raise RuntimeError('Run with assertions enabled')
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
PINS={WIP+'u15_packed_consumed_affine505.py':'a8716b7ca82f703944993a247da89fa2a9a70ccfb5db11521161014edc4a3533',WIP+'u15_packed_consumed_affine505.json':'6376193a420efc81cffbd7becd51d7b2f84d4d44fa3706e5996e06920e06bca5','SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/data/14-waterfall-UniversalTM15x2.tm.txt':'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae'}

def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def needed_evaluation(rows,assignment,outputs):
 needed=set(x for x in outputs if type(x) is str)
 chosen=[]
 for row in reversed(rows):
  if row[0] in needed:
   chosen.append(row);needed.update(x for x in row[2:] if type(x) is str)
 env=dict(assignment)
 for n,op,a,b in reversed(chosen):
  x=env[a] if type(a) is str else a;y=env[b] if type(b) is str else b
  env[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return env,len(chosen)

def verify(repo):
 repo=Path(repo)
 for path,h in PINS.items():
  if hashlib.sha256((repo/path).read_bytes()).hexdigest()!=h:raise ValueError('Changed source '+path)
 saved=json.loads((repo/(WIP+'u15_packed_consumed_affine505.json')).read_text())
 raw=[f['compiler'] for f in saved['forms'] if not f['compiler']['ordinary']]
 assert len(raw)==2
 table=(repo/list(PINS)[-1]).read_text().splitlines()[0]
 original=[(q,s,ord(t[2])-65,int(t[1]=='L'),int(t[0])) for q,row in enumerate(table.split('_')) for s in (0,1) if (t:=row[3*s:3*s+3])!='---']
 indices=[0,2,4,13,12,14,17]
 selected=[original[i] for i in indices]
 assert [(q,s) for q,s,*_ in selected]==[(0,0),(1,0),(2,0),(6,1),(6,0),(7,0),(8,1)]
 directions=[r[3] for r in selected];writes=[r[4] for r in selected]
 popped=[selected[j+1][1] if j<6 else 1 for j in range(7)]
 actual=[];q=s=L=R=0
 for j in range(7):
  actual.append([q,s,L,R]);rule=next(r for r in original if r[:2]==(q,s));_,_,q,d,w=rule
  if d:L,s=divmod(L,2);R=2*R+w
  else:R,s=divmod(R,2);L=2*L+w
 assert actual[-1]==[8,0,0,5] and q==0 and s==1
 records=[];outer_checks=0;source_gates=0
 for exponent in range(9,17):
  B=2**exponent;D=B//64;P=B**7;pack=lambda xs:sum(x*B**j for j,x in enumerate(xs))
  left=[0,0,1,0,0,B//2,B//4-1];right=[0,0,0,0,1,2,5]
  H=pack(left);G=pack(right);U=pack(popped)
  ZL=pack([d*x for d,x in zip(directions,left)]);ZR=pack([d*x for d,x in zip(directions,right)]);ZU=pack([d*x for d,x in zip(directions,popped)])
  J=sum(B**j for j in range(7));beta=P-H-G-ZL-ZR-ZU
  assert beta>0 and all(0<x<P for x in (H,G,U,ZL,ZR,ZU))
  assert all(x<D for x in right) and not all(x<D for x in left)
  E=[sum(B**j for j,i in enumerate(indices) if i==z) for z in range(29)]
  assignment={f'edge{i}':e+1 for i,e in enumerate(E)}
  assignment.update(L0=0,R0=0,height=D,H=H,G=G,U=U,ZL=ZL,ZR=ZR,ZU=ZU,Lfhat=B//8,Rf=11,bound=beta)
  assert all(type(x) is int and x>0 for k,x in assignment.items() if k not in ('L0','R0'))
  forms=[]
  for p in raw:
   r=p['registers'];tags=p['tag_registers'];outputs=[x for pair in p['comparisons'][:5] for x in pair]+[r[k] for k in ('B','D','P','J','Hjoin','Mjoin','Zjoin')]+list(tags.values())
   e,n=needed_evaluation(p['source'],assignment,outputs);source_gates+=n
   value=lambda a:e[a] if type(a) is str else a
   residuals=[value(a)-value(b) for a,b in p['comparisons'][:5]]
   assert residuals==[0]*5;outer_checks+=5
   assert (e[r['B']],e[r['D']],e[r['P']],e[r['J']])==(B,D,P,J)
   A,M,Z=(e[r[k]] for k in ('Hjoin','Mjoin','Zjoin'))
   # Only lane3 changes: permit all canonical base-B left digits. The right
   # range lane4, low selection lanes, and all29 controller lanes stay literal.
   delta=P**3*(B-D)*J
   relaxed=M+delta
   assert A&M!=Z and A&relaxed==Z
   assert value(tags['A'])&value(tags['M'])!=value(tags['Z'])
   assert value(tags['A'])&(value(tags['M'])+delta)==value(tags['Z'])
   assert all((A//P**lane)%P & (M//P**lane)%P == (Z//P**lane)%P for lane in range(34) if lane!=3)
   assert (H & ((D-1)*J))!=H and (G & ((D-1)*J))==G
   assert all(0<=v<P**34 for v in (A,M,Z,relaxed))
   assert all(0<=value(tags[k])<value(tags['cap']) for k in ('A','M','Z'))
   assert value(tags['M'])+delta<value(tags['cap'])
   forms.append(dict(ledger=p['ledger']['polynomial'],outer_residuals=residuals,outer_closure_gates=n,unaltered_lane_checks=33,left_only_relaxation_accepts=True))
  records.append(dict(B=B,D=D,P=P,left_digits=left,right_digits=right,popped=popped,Lf=B//8-1,Rf=11,beta=beta,forms=forms))
 return dict(status='PASS',pins=PINS,scope='Actual raw 505 source outer interface; hypothetical left range-lane deletion only. Existing compiler rejects. No full native Pell witnesses, no nonhalting claim, no ordinary decoder claim.',counts=dict(radices=len(records),raw_forms=len(raw),outer_residual_checks=outer_checks,actual_source_gates_evaluated=source_gates,unchanged_lane_checks=len(records)*len(raw)*33),controller_edge_indices=indices,actual_first_seven_configurations=actual,claimed_final_state=[9,1],actual_after_seven=[q,s,L,R],fixtures=records)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',required=True);ap.add_argument('--output',required=True);ap.add_argument('--expect');a=ap.parse_args();out=verify(a.repo)
 if a.expect and not exact(out,json.loads(Path(a.expect).read_text())):raise ValueError('Receipt mismatch')
 Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['counts'],sort_keys=True))
if __name__=='__main__':main()
