#!/usr/bin/env python3
"""Compare a complete table against current same-size corpus graphs.
The comparison is stronger than rooted isomorphism: all possible roots are
allowed. Reflection and simultaneous read/write complementation are optional
additional symmetries. Complementation does not preserve blank-zero semantics
by itself; it is included only to rule out cosmetic novelty.
"""
import argparse, hashlib, json
from pathlib import Path

def parse(b):
    rows={}
    for line in b.decode('ascii').splitlines():
        line=line.strip()
        if not line or line.startswith(('#','//',';')):continue
        q,r,w,d,t=line.split(); key=(int(q),int(r))
        assert key not in rows and r in ('0','1') and w in ('0','1') and d in ('L','R')
        rows[key]=(int(w),d,int(t))
    states={q for q,r in rows}; halts={t for w,d,t in rows.values()}-states
    assert set(rows)=={(q,r) for q in states for r in (0,1)} and len(halts)==1
    return rows,states,halts.pop()

def canon(rows,states,halt):
    answers=[]
    for root in sorted(states):
        labels={root:0}; todo=[root]; ans=[]
        for q in todo:
            pair=[]
            for bit in (0,1):
                w,d,t=rows[q,bit]
                if t==halt:k=-1
                else:
                    if t not in labels:labels[t]=len(todo);todo.append(t)
                    k=labels[t]
                pair.append([w,d,k])
            ans.append(pair)
        if len(todo)==len(states):answers.append(json.dumps(ans,separators=(',',':')).encode())
    assert answers,'No start reaches full working graph'
    return hashlib.sha256(min(answers)).hexdigest()

def main():
    a=argparse.ArgumentParser();a.add_argument('--candidate',type=Path,required=True);a.add_argument('--census',type=Path,default=Path(__file__).parent/'census/census.json');a.add_argument('--output',type=Path);args=a.parse_args()
    data=args.candidate.read_bytes();rows,states,halt=parse(data)
    corpus=json.loads(args.census.read_text()); existing={x['graph_hash']:x for x in corpus['classes'] if x['states']==len(states)}
    checks=[]
    for reflect in (False,True):
        for complement in (False,True):
            changed={(q,r^complement):(w^complement,('R' if d=='L' else 'L') if reflect else d,t) for (q,r),(w,d,t) in rows.items()}
            h=canon(changed,states,halt)
            checks.append(dict(reflect=reflect,complement=complement,graph_sha256=h,matches=existing.get(h,{}).get('occurrences',[])))
    result=dict(corpus_commit=corpus['summary']['commit'],candidate=str(args.candidate),candidate_sha256=hashlib.sha256(data).hexdigest(),working_states=len(states),transitions=len(rows),known_same_size_graph_classes=len(existing),comparison='All rooted action graphs, also allowing reflection and read/write complement',checks=checks,no_isomorphism_in_any_checked_orientation=all(not x['matches'] for x in checks))
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
