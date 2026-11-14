#!/usr/bin/env python3
"""Regenerate the exact conservative windows used by the bounded searches."""
from pathlib import Path
from collections import defaultdict
import argparse,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import symbolic as s
import check
ROOT=Path(__file__).resolve().parents[2]
W,R=7,3

def expand(xs,k):
    out=[]
    for t in xs:
        if t[0]=='b':out.append(t[1])
        elif t[0]=='r':
            out.extend([t[1]]*min(k-len(out),t[3]))
            if t[2] and len(out)<k:return tuple(out+[-1]*(k-len(out)))
        else:
            out.append(0)
            return tuple((out+[-1]*k)[:k])
        if len(out)>=k:return tuple(out[:k])
    return tuple(out+[0]*(k-len(out)))

def main():
    p=argparse.ArgumentParser()
    p.add_argument('machine',choices=['pa196','diagonal199'])
    p.add_argument('output',type=Path);args=p.parse_args()
    if args.machine=='pa196':M=s.rows;tree=s.TREE
    else:
        f=ROOT/'diagonal199';M=check.parse(f/'machine.native.tm')
        tree=check.tuplify(json.loads((f/'source.tree.json').read_text()))
    check.set_tree(tree);ctx=defaultdict(set)
    def observe(conf):
        q,on,left,right=conf
        ctx[q,right[0][1]].add(tuple(reversed(expand(left,W)))+expand(right,R))
    for case in s.CASES:
        assert s.run_case(M,case,observe)[0],('failed contract',case[0])
    steps=check.startup(M);assert steps==58154
    tape={};q=74;pos=0
    for _ in range(steps):
        b=tape.get(pos,0)
        ctx[q,b].add(tuple(tape.get(pos+j,0) for j in range(-W,R)))
        w,d,q=M[q,b];tape[pos]=w;pos+=1 if d=='R' else -1
    assert q==84
    labels=sorted({q for q,b in M});index={q:i for i,q in enumerate(labels)};index[254]=len(labels)
    data=[f'{len(labels)} {W} {R}'];protected=check.BOX|{84}
    for q in labels:
        data.append(f'{q} {int(q in protected)}')
        for b in (0,1):
            w,d,z=M[q,b];contexts=sorted(ctx[q,b])
            data.append(f'{w} {1 if d=="R" else -1} {index[z]} {len(contexts)}')
            data.extend(' '.join(map(str,c)) for c in contexts)
    args.output.write_text('\n'.join(data)+'\n')
    print(json.dumps({'machine':args.machine,'states':len(labels),
                      'contexts':sum(map(len,ctx.values())),
                      'window_left':W,'window_right':R,'output':str(args.output)},indent=2))

if __name__=='__main__':main()
