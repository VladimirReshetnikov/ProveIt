#!/usr/bin/env python3
"""Restrict source ancestors so that the first 37 primitive addresses are fixed."""
import argparse,json,functools
from pathlib import Path
from model import *
ap=argparse.ArgumentParser();ap.add_argument('--model',type=Path,required=True);ap.add_argument('--source',type=Path,default=BASE/'sites218.json');ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
m=json.loads(a.model.read_text());P=m['productions'];L={int(q):tuple(v)for q,v in m['leaves'].items()}
@functools.lru_cache(None)
def rep(q):return L[q]if q in L else(rep(P[q][0][0]),rep(P[q][0][1]))
ids={localg(rep(q)):q for q in range(len(P))};forced={}
def visit(n,start=0):
 if leaf(n)or start>=37:return
 q=ids[localg(n)];xy=[ids[localg(n[0])],ids[localg(n[1])]];assert xy in P[q];forced[q]=xy
 visit(n[0],start);visit(n[1],start+len(leaves(n[0])))
visit(parse(json.loads(a.source.read_text())))
for q,xy in forced.items():P[q]=[xy]
m['forced_prefix37']=forced
(a.output/'model.json').write_text(json.dumps(m,separators=(',',':'))+'\n')
with(a.output/'model.txt').open('w')as f:
 f.write(f"{len(P)} {len(L)} {len(m['base'])} 1\n")
 for row in [sorted(L),m['base'],[m['root']]]:f.write(' '.join(map(str,row))+'\n')
 for ps in P:f.write(str(len(ps))+' '+' '.join(f'{x} {y}'for x,y in ps)+'\n')
print('Forced',len(forced),'productions')
