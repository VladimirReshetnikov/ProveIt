#!/usr/bin/env python3
"""Syntactically closed source chunks and conservative fixed-root reuse tags.

A chunk is closed when every decrement exit, break and continue refers to a
branch within the chunk. Reassociating sequences of closed chunks preserves
resolved source instructions. Pure root readers do not inspect the predecessor.
Nonpure roots receive only their observed structural predecessor bits here;
any use at a new bit requires a separate physical proof.
"""
from pathlib import Path
import sys,json,collections
W=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(W/'verification'))
import symbolic as S

def closed(t):
    try:
        for p,op in S.flatten(t):
            if op[0]=='dec':S.cut(p,0,1)
            elif op[0]=='breakTo':S.cut(p,0,op[1])
            elif op[0]=='continueTo':S.cut(p,1,op[1])
        return True
    except ValueError:return False

def main():
    root,defs=S.source_tree();m=S.load_machine()
    nm=json.loads((W/'verification/node_map.json').read_text())
    names={t:n for n,t in defs.items() if n.startswith('node')}
    contexts=collections.defaultdict(set)
    def walk(t,p=()):
        if t[0]=='leaf':return
        contexts[t].add(p[-1] if p else 1)
        walk(t[0],p+(0,));walk(t[1],p+(1,))
    walk(root)
    out={}
    for name,t in defs.items():
        if not name.startswith('node') or int(name[4:])>150 or not closed(t):continue
        qs=nm[name]
        if len(qs)!=1:continue
        q=qs[0];pure=m[q,0][:2]==(0,1) and m[q,1][:2]==(1,1)
        kids=[names.get(x, {'leaf':x[1]} if x[0]=='leaf' else None) for x in t]
        out[name]=dict(state=q,leaves=len(S.flatten(t)),root_pure=pure,
            conservative_parent_tags=[0,1] if pure else sorted(contexts[t]),
            children=kids,children_closed=list(map(closed,t)),
            splittable=all(map(closed,t)),rows=[m[q,0],m[q,1]])
    (Path(__file__).with_name('macro_splits.json')).write_text(json.dumps(out,indent=2))
    for n,d in out.items():
        if d['splittable']:print(n,d['state'],d['children'],'tags',d['conservative_parent_tags'])
if __name__=='__main__':main()
