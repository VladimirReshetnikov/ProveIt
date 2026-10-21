#!/usr/bin/env python3
"""One-layer global subtree rotations with exact repaired-CFG checking."""
from pathlib import Path
import sys,json,time
from functools import cache
from search_open_rotations import s,relevel,internal,HERE,BASE

def main():
    root=s.tree(json.loads((BASE/'sites215.json').read_text()))
    expected=s.graph_intervals(s.sites((root,('CH',None))))
    unique={n for _,n in internal(root)}
    @cache
    def replace_all(root,node,new):
        if root==node:return new
        if s.leaf(root):return root
        return replace_all(root[0],node,new),replace_all(root[1],node,new)
    best=202;trials=valid=0;saved=[];start=time.monotonic()
    for node in sorted(unique,key=repr):
        candidates=[]
        if not s.leaf(node[1]):
            a,(b,c)=node;candidates.append(((a,b),c))
        if not s.leaf(node[0]):
            (a,b),c=node;candidates.append((a,(b,c)))
        for new in candidates:
            trials+=1;out=relevel(replace_all(root,node,new),expected)
            if out is None:continue
            valid+=1;m=s.metrics(out)
            if m['maximum_zero_run']>6:continue
            if m['dag_nodes']<=best:
                if m['dag_nodes']<best:best=m['dag_nodes'];saved=[]
                saved.append(out)
                raw=s.compact(s.sites(out))
                (HERE/f'global-open-best-{best}-{len(saved)-1}.json').write_bytes(raw)
                print('BEST',best,trials,m,flush=True)
    result={'trials':trials,'valid_new_graphs':valid,'best_DAG':best,'seconds':time.monotonic()-start,'saved':len(saved),'scope':'One global subtree rotation with exact guarded CFG preservation after CB/CC depth adjustment; no binary claim or optimality claim.'}
    (HERE/'global_open_result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
