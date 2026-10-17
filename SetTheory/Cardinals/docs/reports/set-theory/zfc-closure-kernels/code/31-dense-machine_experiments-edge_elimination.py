#!/usr/bin/env python3
"""Try state elimination with separate routing for each incoming edge.

Unlike ordinary state merging, different incoming edges may choose different
replacement states. A candidate is accepted only when a finite-window local
join is found for every overapproximated window after every incoming edge.
No local comparison crosses a subsequent edge back to the eliminated state.
Thus all local transitions checked are identical in the patched machine.
The changed incoming edge itself supplies positive progress on both sides.
Finite-window reachability universally admits both unknown exterior symbols.
This is an executable certificate search with an elementary mathematical
argument, not a proof-assistant verification or a lower bound.
"""
from __future__ import annotations
import argparse, importlib.util, json, sys, time
from pathlib import Path
from collections import defaultdict

def load(path):
 s=importlib.util.spec_from_file_location('table_audit',path);m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m);return m

def trace(machine,start,pattern,radius,bound,avoid):
    head=0;q=start;out=[(q,head,pattern)]
    for step in range(bound):
        if q==machine.halt or not -radius<=head<=radius:break
        edge=machine.rows[q,(pattern>>(head+radius))&1]
        if edge.target==avoid:break
        pattern=(pattern&~(1<<(head+radius)))|(edge.write<<(head+radius));head+=edge.move;q=edge.target
        out.append((q,head,pattern))
    return out

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--table',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--radius',type=int,default=4);p.add_argument('--steps',type=int,default=64);a=p.parse_args()
    audit=load(a.repo/'Computability/BusyBeaver/Research/ZFC/audit_tm.py');m=audit.parse_table(a.table.read_text());t0=time.monotonic();wins=audit.window_reachable(m,a.radius)
    full=(1<<(2*a.radius+1))-1;incoming=defaultdict(dict)
    for (q,b),e in m.rows.items():
        if e.target==m.halt:continue
        ws=set()
        for pat in wins.get(q,[]):
            if (pat>>a.radius)&1!=b:continue
            written=(pat&~(1<<a.radius))|(e.write<<a.radius)
            shifted,unknown=((written>>1,1<<(2*a.radius)) if e.move==1 else ((written<<1)&full,1))
            ws.update((shifted,shifted|unknown))
        if ws:incoming[e.target][q,b]=ws
    result={'source':str(a.table),'states':len(m.states),'radius':a.radius,'max_local_steps':a.steps,'abstract_configurations':sum(map(len,wins.values())),'candidate_states':0,'incoming_edge_tests':0,'destination_tests':0,'survivors':[],'scope':'finite-window incoming-context edge redistribution; no global minimality claim'}
    for removed in m.states:
        if removed==m.start or (removed,0) in incoming[removed] or (removed,1) in incoming[removed]:continue
        result['candidate_states']+=1;routes={};certs={}
        for edgekey,patterns in incoming[removed].items():
            result['incoming_edge_tests']+=1
            allpatterns=sorted(patterns)
            originals={pat:{c:i for i,c in enumerate(trace(m,removed,pat,a.radius,a.steps,removed)) if c[0]!=removed} for pat in allpatterns}
            success=None
            for replacement in m.states:
                if replacement==removed:continue
                result['destination_tests']+=1;cert=[]
                for pat in allpatterns:
                    orig=originals[pat]
                    for j,c in enumerate(trace(m,replacement,pat,a.radius,a.steps,removed)):
                        if c in orig:
                            cert.append([pat,orig[c],j]);break
                    else:break
                else:success=replacement;break
            if success is None:break
            routes[f'{edgekey[0]}/{edgekey[1]}']=success;certs[f'{edgekey[0]}/{edgekey[1]}']=cert
        else:
            result['survivors'].append({'removed':removed,'incoming_routes':routes,'certificates':certs});print('SURVIVOR',removed,routes,flush=True)
        if result['candidate_states']%40==0:print(json.dumps({k:result[k] for k in ('candidate_states','incoming_edge_tests','destination_tests')}),flush=True)
    result['elapsed']=time.monotonic()-t0;a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='survivors'}),flush=True)
if __name__=='__main__':main()
