#!/usr/bin/env python3
"""Bounded S6 exploratory relation system. All generated rows are exact integers."""
from word_algebra import *
from itertools import product
from pathlib import Path
from math import gcd
import json,time
W=7
base=Path(__file__).resolve().parent
start=time.monotonic()
def words(n): return [w for w in product(range(-1,4),repeat=n) if admissible(w)]
def encode(w):
    x=0
    for a in w:x=5*x+a+1
    return x
def primitive(row):
    g=0
    for c in row.values(): g=gcd(g,c)
    if row and row[min(row)]<0:g=-g
    return {encode(w):c//g for w,c in row.items()},g
rows=[];desc=[];seen=set()
for p in [1,2,3]:
    us=words(p)+([(0,)] if p==1 else [])
    vs=words(W-p)
    for u in us:
        for v in vs:
            if (u,v)>(conjugate(u),conjugate(v)):continue
            row=odd_projection(double_shuffle(u,v))
            if not row:continue
            row,g=primitive(row);key=tuple(sorted(row.items()))
            if key in seen:continue
            seen.add(key);rows.append(row);desc.append(['ds',u,v,g])
    print('factor_weight',p,'rows',len(rows),'seconds',time.monotonic()-start,flush=True)
for A in [(Z,)*5+(1,1),(1,)+(Z,)*5+(1,)]:
    row=odd_projection(plus({A:1},cayley(A),-1))
    rows.append({encode(w):c for w,c in row.items()});desc.append(['cayley',A])
# F7 is the exact primitive target from the pinned conjecture.
targ={}
for c,ind in [(642940,((6,1),(1,2))),(-237900,((6,1),(1,0))),(-48800,((4,1),(3,0))),(530944,((2,1),(5,0))),(-1032988,((7,1),))]:
    targ=plus(targ,{to_word(ind):c})
for c,a,b in [(15555,((2,1),),((5,0),)),(144753,((4,1),),((3,0),)),(-1285880,((6,1),),((1,2),))]:
    targ=plus(targ,shuffle(to_word(a),to_word(b)),c)
targ=odd_projection(targ)
rows.append({encode(w):c for w,c in targ.items()});desc.append(['target'])
cols=set().union(*(r.keys() for r in rows))
with (base/'rows.txt').open('w') as f:
    f.write(f'{len(rows)} {5**W}\n')
    for r in rows:
        f.write(str(len(r))+' '+' '.join(f'{a} {c}' for a,c in sorted(r.items()))+'\n')
(base/'descriptors.json').write_text(json.dumps(desc,separators=(',',':'))+'\n')
summary={'weight':W,'ds_rows':len(rows)-3,'cayley_rows':2,'target_terms':len(targ),'column_count':len(cols),'integer_entries':sum(map(len,rows)),'elapsed_seconds':time.monotonic()-start,'status':'No row membership calculation has yet been made.'}
(base/'generation.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
