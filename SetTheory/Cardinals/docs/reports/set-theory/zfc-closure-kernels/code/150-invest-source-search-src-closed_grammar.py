#!/usr/bin/env python3
"""Export the finite two-round shared grammar of closed source sequences."""
import argparse,functools,json
from pathlib import Path
from model import *
ap=argparse.ArgumentParser();ap.add_argument('--rounds',type=int,default=2);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--input',type=Path,default=BASE/'sites218.json');a=ap.parse_args();a.output.mkdir(exist_ok=True,parents=True)
rows=json.loads(a.input.read_text());t=parse(rows);ns=nodes(t)
@functools.lru_cache(None)
def serial(n):return not leaf(n)and all(boundary(c)==(0,0)for c in n)
@functools.lru_cache(None)
def atoms(n):return atoms(n[0])+atoms(n[1])if serial(n)else(n,)
atomlist=list(dict.fromkeys(x for n in ns for x in atoms(n)));aid={n:i for i,n in enumerate(atomlist)}
def word(n):return tuple(aid[x]for x in atoms(n))
D={word(n)for n in ns if boundary(n)==(0,0)};baseD=D.copy();required=set()
for n in ns:
 if not leaf(n)and not serial(n):
  for c in n:
   if len(word(c))>1:required.add(word(c))
if len(word(t))>1:required.add(word(t))
def productions(D):return {w:[(w[:i],w[i:])for i in range(1,len(w))if w[:i]in D and w[i:]in D]for w in D if len(w)>1}
for it in range(a.rounds):
 ps=productions(D);new=set()
 for w,ls in ps.items():
  for x,y in ls:
   for xx,xy in ps.get(x,[]):new.add(xy+y)
   for yx,yy in ps.get(y,[]):new.add(x+yx)
 D|=new
 print('saturate',it+1,'words',len(D),'new',len(new),flush=True)
ww=sorted(D,key=lambda w:(len(w),w));idx={w:i for i,w in enumerate(ww)};ps=productions(D)
atoms0=[i for i,w in enumerate(ww)if len(w)==1];base0=sorted(idx[w]for w in baseD if len(w)>1);req0=sorted(idx[w]for w in required)
with (a.output/'model.txt').open('w')as f:
 f.write(f'{len(ww)} {len(atoms0)} {len(base0)} {len(req0)}\n')
 for row in [atoms0,base0,req0]:f.write(' '.join(map(str,row))+'\n')
 for w in ww:
  pairs=[(idx[x],idx[y])for x,y in ps.get(w,[])]
  f.write(str(len(pairs))+' '+' '.join(f'{x} {y}'for x,y in pairs)+'\n')
(a.output/'model.json').write_text(json.dumps({'words':ww,'base':base0,'required':req0,'source':str(a.input)},separators=(',',':'))+'\n')
print('Exported',len(ww),'classes;',len(atoms0),'closed atoms;',len(base0),'active serial classes;',len(atomlist),'fixed original DAG nodes')
