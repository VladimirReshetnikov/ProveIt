#!/usr/bin/env python3
"""Independently replay finite closed-graph obstructions to incoming reroutes.

For each removed state, candidate actions are precisely all individually
neutral finite-test actions in the supplied neutral-row file, filtered to
avoid that state. The graph permits a fresh choice on every visit, so it
overapproximates every fixed simultaneous incoming reroute. A finite graph
whose every edge reaches another graph node, with no required instruction
endpoint, certifies failure for the displayed concrete frame. This is a
limited obstruction to this family, not a state-minimality theorem.

This verifier uses sparse, unbounded tapes and exact Python configurations;
it independently reconstructs all graph nodes and literal connecting paths.
"""
from pathlib import Path
from collections import deque
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent

def read_table(path):
 T={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,t=line.split();T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
 return T

def addone(p):
 a=list(p);i=len(a)-1
 while i>=0 and a[i]=='1':a[i]='0';i-=1
 if i<0:return '',True
 a[i]='1';return ''.join(a),False

def strip(p,bit,count):
 i=len(p)
 while i and count:
  i-=1
  if p[i]==bit:count-=1
 return p[:i]

def paint(pc,span,regs,h):
 t={h-1,h+span};t.update(h+i for i,b in enumerate(pc) if b=='1')
 at=h+span+1
 for v in regs:t.update(range(at+1,at+v+2));at+=v+2
 return frozenset(t)

def frame(label):
 p,op,r,seed,branch=label.split();r,seed,branch=map(int,(r,seed,branch))
 phy=(6,2,0,4,3,7,8,5,1)
 R=[(i*3+seed)%7 if i<9 else seed%3 for i in range(11)]
 if op=='CD':R[phy[r]]=seed+1 if branch else 0
 h=128;span=40+seed;initial=paint(p,span,R,h);saved=R.copy();extra=0;overflow=False
 if op=='CI':R[phy[r]]+=1;R.append(1);pc,overflow=addone(p)
 elif op=='CD':
  if branch:R[phy[r]]-=1;extra=1;pc,overflow=addone(p)
  else:pc,overflow=addone(strip(p,'0',1))
 elif op=='CB':pc,overflow=addone(strip(p,'0',r))
 elif op=='CC':pc=strip(p,'1',r)
 else:raise ValueError('Only nonhalting obstruction cases are expected.')
 goal=(96,h-int(overflow),paint(pc,span+extra+int(overflow),R,h-int(overflow)))
 return (96,h,initial),goal,dict(pc=p,operation=op,logical_register=r,seed=seed,branch='positive' if branch else 'zero',physical_registers=saved,span=span,head=h)

def configuration(c):return dict(state=c[0],head=c[1],ones=sorted(c[2]))

def verify(T,neutral,record):
 removed=record['removed'];domains={}
 for e,a in T.items():
  if e[0]!=removed and a[2]==removed:
   domains[e]=[r for r in neutral.get(e,[]) if r[2]!=removed]
   assert domains[e],e
 choices=1
 for rows in domains.values():choices*=len(rows)
 assert choices==record['combinations']
 start,goal,fixture=frame(record['case'])
 def step(c,a):
  q,h,ones=c;w,d,t=a
  ss=set(ones)
  if w:ss.add(h)
  else:ss.discard(h)
  return t,h+d,frozenset(ss)
 def advance(c,after):
  seen=set();trace=[]
  while True:
   if after:assert c!=goal and c[0]!=254,('unexpected endpoint',c)
   q,h,ones=c;e=q,int(h in ones)
   if e in domains:return c,trace
   assert c not in seen,('interior cycle must be represented explicitly',c)
   assert len(trace)<100000,'advance bound reached; no certificate produced'
   seen.add(c);a=T[e];trace.append(dict(state=q,read=e[1],write=a[0],direction=a[1],target=a[2],head=h))
   c=step(c,a);after=True
 entry,entry_trace=advance(start,False);states=[entry];indices={entry:0};queue=deque([entry]);edges=[]
 while queue:
  c=queue.popleft();e=c[0],int(c[1] in c[2])
  for a in domains[e]:
   nxt,trace=advance(step(c,a),True)
   if nxt not in indices:indices[nxt]=len(states);states.append(nxt);queue.append(nxt)
   edges.append(dict(source=indices[c],action=list(a),target=indices[nxt],literal_steps=1+len(trace),connecting_trace=trace))
   assert len(states)<=10000,'graph bound reached; no certificate produced'
 assert len(states)==record['boundary_nodes'] and len(edges)==record['edges']
 assert record['rejects']==0
 return dict(removed=removed,family_size=choices,fixture=fixture,initial=configuration(start),required_endpoint=configuration(goal),
             entry_trace=entry_trace,nodes=[configuration(c) for c in states],edges=edges,
             statement='Every nondeterministic edge returns to the displayed finite graph in positive literal time, and no connecting path reaches the required endpoint or halt.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--machine',type=Path,default=HERE.parent/'reference/context246/machine/zfc_prefix246_old.tm');ap.add_argument('--neutral-rows',type=Path,default=HERE.parent/'data/neutral_rows.txt');ap.add_argument('--obstructions',type=Path,default=HERE.parent/'results/union-obstructions.json');ap.add_argument('--output',type=Path,default=HERE.parent/'results/union-graph-certificates.json');a=ap.parse_args()
 T=read_table(a.machine);neutral={}
 for line in a.neutral_rows.read_text().splitlines():
  q,b,w,d,t,n=map(int,line.split());neutral.setdefault((q,b),[]).append((w,d,t))
 certs=[verify(T,neutral,r) for r in json.loads(a.obstructions.read_text())]
 result=dict(status='PASS',method='Exact sparse-tape closure; independent of the C++ finite tape simulation',machine_sha256=hashlib.sha256(a.machine.read_bytes()).hexdigest(),neutral_rows_sha256=hashlib.sha256(a.neutral_rows.read_bytes()).hexdigest(),certificates=certs)
 a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',obstructions=len(certs),nodes=sum(len(c['nodes']) for c in certs),edges=sum(len(c['edges']) for c in certs),largest_family=max(c['family_size'] for c in certs)),indent=2))
if __name__=='__main__':main()
