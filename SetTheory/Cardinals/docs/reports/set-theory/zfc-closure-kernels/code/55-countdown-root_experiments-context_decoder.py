#!/usr/bin/env python3
"""Exact bounded symbolic semantics for two-way read-only decoder states."""
from decoder_semantics import rows,states,leaf,mux,nodes,intern
from functools import lru_cache
import json,time

# These states belong to runtime excursions, not the read-only decoder.
BOX={0,1,2,3,4,6,7,9,13,19,28,29,31,38,40,41,43,44,48,56,58,59,60,63,64,69,73,74,75,83,84,85,95,97,109,112,131}
pure={q for q in states if q not in BOX and all(rows[q,b][0]==b for b in(0,1))}
LIMIT=50
calls=0
def decode(q,h=0,env=None,visited=frozenset(),depth=0):
    global calls
    calls+=1
    if env is None:env={}
    if q not in pure or depth>=LIMIT:return leaf(q,h)
    # A read-only repeated configuration is permanently nonhalting.
    if (q,h) in visited:return intern(('leaf',-1,0))
    visited=visited|{(q,h)}
    if h in env:
        _,d,t=rows[q,env[h]]
        return decode(t,h+d,env,visited,depth+1)
    children=[]
    for b in(0,1):
        env[h]=b;_,d,t=rows[q,b]
        children.append(decode(t,h+d,env,visited,depth+1))
    del env[h]
    return mux(h,*children)

if __name__=='__main__':
    start=time.monotonic();groups={};means={}
    for q in states:
        m=decode(q);means[q]=m;groups.setdefault(m,[]).append(q)
    print(json.dumps({'states':len(pure),'bdd_nodes':len(nodes),'calls':calls,
          'time':time.monotonic()-start,'same':[x for x in groups.values()if len(x)>1]},indent=2),flush=True)
    # Incoming rows leave known predecessor symbol. Opposite movement can
    # therefore replace a continuation at offset +/-2, with all-tape proof.
    replacements=[]
    for(q,b),(w,d,t)in rows.items():
        if t not in pure:continue
        wanted=decode(t,d,{0:w})
        for r in states:
            if r==t:continue
            for nd in(-1,1):
                if decode(r,nd,{0:w})==wanted:
                    replacements.append({'entry':[q,b],'target':t,'new_target':r,'old_direction':d,'new_direction':nd})
    print('replacements',json.dumps(replacements),flush=True)
