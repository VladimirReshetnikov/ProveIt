#!/usr/bin/env python3
"""Decoder layout beam for reducing the dispatch zero-run requirement.

Only closed-subroutine reassociations and commuting increments from source09
are used. This produces register programs, not certified smaller machines.
"""
from pathlib import Path
from functools import lru_cache
import argparse, hashlib, json, sys, time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'grammar_search'))
import cost_search as c

def metrics(nodes,root):
    @lru_cache(None)
    def m(e):
        if e[0]!='N':return 0,0,0
        a,b=map(m,nodes[e[1]])
        return 1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2])
    p,z,d=m(('N',root))
    bad=sum(max(0,m(('N',n))[0]-6) for n in nodes)
    return len(nodes),bad,z,d

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--width',type=int,default=12)
    ap.add_argument('--depth',type=int,default=8)
    ap.add_argument('--seconds',type=float,default=300)
    ap.add_argument('--output',type=Path,default=HERE/'short-zero-layout.json')
    args=ap.parse_args()
    initial=(c.NODES,c.ROOT,[]);beam=[initial];visited=set();found=[];rounds=[];began=time.monotonic()
    def key(nodes):return repr(tuple(nodes.values()))
    def score(t):
        n,b,z,d=metrics(t[0],t[1]);return (2.5*(n-203)+b,n,b,d)
    visited.add(key(c.NODES))
    for depth in range(args.depth):
        choices=[]
        for nodes,root,history in beam:
            for index,(n,e,kind) in enumerate(c.rot.options(nodes)):
                new,nr=c.rot.mutate(nodes,root,n,e);identity=key(new)
                if identity in visited:continue
                visited.add(identity);m=metrics(new,nr)
                if m[2]>7 or m[3]>38:continue
                hist=history+[[n,e,kind]];candidate=(new,nr,hist)
                choices.append(candidate)
                if m[2]<=6:
                    record={'metrics':m,'history':hist,'root':nr,'nodes':new}
                    if not found or m<found[0]['metrics']:
                        found.insert(0,record);print('SHORT ZERO',m,'depth',depth+1,flush=True)
        if not choices:break
        choices.sort(key=score);beam=choices[:args.width]
        record={'depth':depth+1,'states_examined':len(visited),'best_score':score(beam[0]),'best_metrics':metrics(beam[0][0],beam[0][1]),'candidates':len(choices)}
        rounds.append(record);print(record,flush=True)
        args.output.write_text(json.dumps({'scope':__doc__,'parameters':vars(args)|{'output':str(args.output)},
            'baseline':metrics(c.NODES,c.ROOT),'rounds':rounds,'short_zero_layouts':found[:5],
            'best':{'root':beam[0][1],'nodes':beam[0][0],'history':beam[0][2]},
            'elapsed_seconds':time.monotonic()-began},indent=2)+'\n')
        if time.monotonic()-began>=args.seconds:break

if __name__=='__main__':main()
