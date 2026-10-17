#!/usr/bin/env python3
"""State deletion by per-incoming transition synthesis and local joining.

Each incoming edge may change its write, move, and destination. Every possible
abstract input window for that edge must exhibit the same complete local
configuration after positive steps. No comparison executes a later transition
into the removed state. The certificate therefore refers only to unchanged
rows after the initial rewritten edge. This does not prove global minimality.
"""
from __future__ import annotations
import argparse,json,sys,time,importlib.util
from pathlib import Path
from collections import defaultdict

def load(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def trace(m,q,head,pattern,radius,bound,avoid):
 out=[(q,head,pattern)]
 for _ in range(bound):
  if q==m.halt or not -radius<=head<=radius:break
  e=m.rows[q,(pattern>>(head+radius))&1]
  if e.target==avoid:break
  pattern=(pattern&~(1<<(head+radius)))|(e.write<<(head+radius));head+=e.move;q=e.target;out.append((q,head,pattern))
 return out

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--table',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--radius',type=int,default=4);p.add_argument('--steps',type=int,default=64);a=p.parse_args()
 au=load('table_audit',a.repo/'Computability/BusyBeaver/Research/ZFC/audit_tm.py');m=au.parse_table(a.table.read_text());t0=time.monotonic();wins=au.window_reachable(m,a.radius)
 incoming=defaultdict(dict)
 for (q,b),e in m.rows.items():
  if e.target==m.halt:continue
  ws=[pat for pat in wins.get(q,[]) if (pat>>a.radius)&1==b]
  if ws:incoming[e.target][q,b]=ws
 result={'source':str(a.table),'states':len(m.states),'radius':a.radius,'max_local_steps':a.steps,'abstract_configurations':sum(map(len,wins.values())),'candidate_states':0,'incoming_edge_tests':0,'transition_rewrites_tested':0,'survivors':[],'scope':'finite-window per-incoming transition synthesis; no global minimality claim'}
 for removed in m.states:
  if removed==m.start or (removed,0) in incoming[removed] or (removed,1) in incoming[removed]:continue
  result['candidate_states']+=1;routes={};certs={}
  for edgekey,patterns in incoming[removed].items():
   result['incoming_edge_tests']+=1;e=m.rows[edgekey]
   originals={}
   for pat in patterns:
    written=(pat&~(1<<a.radius))|(e.write<<a.radius)
    originals[pat]={c:i+1 for i,c in enumerate(trace(m,removed,e.move,written,a.radius,a.steps,removed)) if c[0]!=removed}
   success=None
   for w,d in [(e.write,e.move)]+[(w,d) for w in (0,1) for d in (-1,1) if (w,d)!=(e.write,e.move)]:
    for target in m.states:
     if target==removed:continue
     result['transition_rewrites_tested']+=1;cert=[]
     for pat in patterns:
      written=(pat&~(1<<a.radius))|(w<<a.radius);orig=originals[pat]
      for j,c in enumerate(trace(m,target,d,written,a.radius,a.steps,removed)):
       if c in orig:cert.append([pat,orig[c],j+1]);break
      else:break
     else:success=(w,d,target);break
    if success is not None:break
   if success is None:break
   routes[f'{edgekey[0]}/{edgekey[1]}']=success;certs[f'{edgekey[0]}/{edgekey[1]}']=cert
  else:
   result['survivors'].append({'removed':removed,'incoming_rewrites':routes,'certificates':certs});print('SURVIVOR',removed,routes,flush=True)
  if result['candidate_states']%40==0:print(json.dumps({k:result[k] for k in ('candidate_states','incoming_edge_tests','transition_rewrites_tested')}),flush=True)
 result['elapsed']=time.monotonic()-t0;a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='survivors'}),flush=True)
if __name__=='__main__':main()
