#!/usr/bin/env python3
"""Exact graph reachability and transition-preserving state bisimulation.

An equivalence here preserves write symbol, direction, and the successor
equivalence class separately for each read symbol. It therefore preserves
literal TM behavior from the same tape and head, for every tape.
"""
from pathlib import Path
import argparse,hashlib,json

def main():
    p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    rows={};start=None
    for line in a.table.read_text().splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,s=line.split();q,b,w,s=map(int,(q,b,w,s));assert (q,b) not in rows and b in(0,1) and w in(0,1) and d in('L','R');rows[q,b]=(w,d,s)
    states={q for q,b in rows};assert start in states and set(rows)=={(q,b) for q in states for b in (0,1)}
    halts={s for w,d,s in rows.values()}-states;assert len(halts)==1;halt=next(iter(halts))
    reachable={start};todo=[start]
    while todo:
        q=todo.pop()
        if q==halt:continue
        for b in (0,1):
            s=rows[q,b][2]
            if s not in reachable:reachable.add(s);todo.append(s)
    labels={q:0 for q in states};labels[halt]=1;rounds=0;history=[]
    while True:
        codes={};nxt={halt:0}
        for q in sorted(states):
            key=tuple((w,d,labels[s]) for b in (0,1) for w,d,s in [rows[q,b]])
            if key not in codes:codes[key]=len(codes)+1
            nxt[q]=codes[key]
        rounds+=1;history.append(len(codes))
        stable=all((labels[x]==labels[y])==(nxt[x]==nxt[y]) for x in states for y in states)
        labels=nxt
        if stable:break
    classes={}
    for q in sorted(states):classes.setdefault(labels[q],[]).append(q)
    for members in classes.values():
        first=members[0]
        for q in members:
            for b in (0,1):
                w,d,s=rows[q,b];v,e,t=rows[first,b]
                assert (w,d,labels[s])==(v,e,labels[t])
    result=dict(status='PASS_EXACT_GRAPH_AUDIT',working_states=len(states),working_states_graph_reachable=len(states&reachable),halt_graph_reachable=halt in reachable,unreachable_working_states=sorted(states-reachable),bisimulation_classes=len(classes),nontrivial_bisimulation_classes=[c for c in classes.values() if len(c)>1],refinement_rounds=rounds,class_counts=history,table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Graph reachability overapproximates actual tape reachability. The checked transition congruence is a universal same-tape state bisimulation; absence of a nontrivial class is not state minimality.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
