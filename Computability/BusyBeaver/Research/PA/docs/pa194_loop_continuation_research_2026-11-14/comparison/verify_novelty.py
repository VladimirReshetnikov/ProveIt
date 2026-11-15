#!/usr/bin/env python3
"""Exact broad structural comparison against all complete 194-state corpus graphs.
Reflection and symbol exchange are structural tests, not preservation claims for a fixed blank symbol.
"""
import argparse, json, hashlib
from pathlib import Path

def parse(path):
    rows={}
    for line in Path(path).read_text().splitlines():
        if not line.strip() or line.lstrip().startswith(('#','//',';')):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in rows
        rows[q,b]=(w,d,n)
    states={q for q,b in rows};halts={n for w,d,n in rows.values()}-states
    assert set(rows)=={(q,b) for q in states for b in (0,1)} and len(halts)==1
    return rows,states,next(iter(halts))

def form(rows,states,halt,start,mirror,swap):
    ids={start:0};todo=[start];out=[]
    for q in todo:
        for b in (0,1):
            w,d,n=rows[q,b^swap]
            if n==halt:out.append((0,'R',-1));continue
            if n not in ids:ids[n]=len(ids);todo.append(n)
            out.append((w^swap,('R' if d=='L' else 'L') if mirror else d,ids[n]))
    return tuple(out) if len(todo)==len(states) else None

def canonical(path):
    rows,states,halt=parse(path);best=None
    for mirror,swap in [(False,False),(True,False),(False,True),(True,True)]:
        for q in sorted(states):
            f=form(rows,states,halt,q,mirror,swap)
            if f is not None and (best is None or f<best):best=f
    return len(states),best

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--corpus',type=Path,required=True);ap.add_argument('--candidate',type=Path);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    corpus=json.loads(args.corpus.read_text());reps=args.corpus.parent/'representatives';groups={};refs=[]
    for r in corpus['classes']:
        if r['states']!=194:continue
        p=reps/(r['graph_hash']+'.tm');n,f=canonical(p);assert n==194 and f is not None
        refs.append((r,f));groups.setdefault(f,[]).append(r['table_class'])
    result={'snapshot':corpus['summary']['snapshot'],'reference_graphs':len(refs),'broad_structural_classes':len(groups),'merged_classes':[v for v in groups.values() if len(v)>1],'symmetries':['arbitrary state renaming','any spanning root','global L/R reflection','global bit exchange','terminal-edge write/move ignored'],'comparison':'full canonical tuples compared, not hash equality'}
    if args.candidate:
        n,f=canonical(args.candidate);assert f is not None
        result.update(candidate=str(args.candidate),working_states=n,candidate_sha256=hashlib.sha256(args.candidate.read_bytes()).hexdigest(),canonical_sha256=hashlib.sha256(repr(f).encode()).hexdigest(),matches=[r['table_class'] for r,g in refs if f==g])
    args.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
