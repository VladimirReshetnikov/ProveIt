#!/usr/bin/env python3
"""Replay the scoped eleven-atom source-helper association search, offline.

Usage: python helper_associations.py UPSTREAM_DIRECTORY ALIASES_JSON OUTPUT_JSON
The output is a source allocation estimate, not a physical machine theorem.
"""
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
import sys
from prepare_graph import source_rows,PINS
from compare_sources import graph,require

class Model:
    def __init__(self,text):
        self.store=[];self.intern={}
        root,definitions=source_rows(text,True)
        @lru_cache(None)
        def convert(t):
            return self.node(convert(t[1]),convert(t[2])) if t[0]=='node' else self.put(t)
        self.env={name:convert(t) for name,t in definitions.items()};self.root=convert(root)
    def put(self,row):
        if row not in self.intern:self.intern[row]=len(self.store);self.store.append(row)
        return self.intern[row]
    def node(self,a,b):return self.put(('node',a,b))
    def isnode(self,n):return self.store[n][0]=='node'
    def unique(self,n):
        seen=set();todo=[n]
        while todo:
            t=todo.pop()
            if t in seen:continue
            seen.add(t)
            if self.isnode(t):todo.extend(self.store[t][1:])
        return seen
    def rows(self,n):
        op={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
        def walk(t,p=''):
            row=self.store[t]
            if row[0]=='node':
                yield from walk(row[1],p+'0');yield from walk(row[2],p+'1')
            else:yield[p,op[row[0]],row[1]]
        return list(walk(n))

def main():
    upstream,aliaspath,out=map(Path,sys.argv[1:]);raw=(upstream/'PA196/Program.lean').read_bytes()
    require(sha256(raw).hexdigest()==PINS['PA196/Program.lean'],'wrong source')
    m=Model(raw.decode());e=m.env;oldgraph=graph(m.rows(m.root))
    aliasbytes=aliaspath.read_bytes();aliases=[{e[n] for n in row['source_nodes']} for row in json.loads(aliasbytes)]
    def cost(root):
        seen=m.unique(root);represented=set().union(*(a&seen for a in aliases))
        return 49+sum(bool(a&seen) for a in aliases)+sum(m.isnode(n) for n in seen-represented)
    require(cost(m.root)==196,'baseline cost changed')
    @lru_cache(None)
    def word(t):
        return (t,) if not m.isnode(t) else word(m.store[t][1])+word(m.store[t][2])
    @lru_cache(None)
    def trees(atoms):
        if len(atoms)==1:return atoms
        return tuple(m.node(a,b) for k in range(1,len(atoms)) for a in trees(atoms[:k]) for b in trees(atoms[k:]))
    def has_helper(root):
        for t in m.unique(root):
            if not m.isnode(t):continue
            _,a,b=m.store[t]
            if m.isnode(a) and m.isnode(b) and m.store[a][1]==e['node32'] and m.store[b][1]==e['node17']:return True
        return False
    names=['node32','node53','node55','node65','x5','x6','node17','node64','node65','x3','x15']
    atoms=tuple(e[n] for n in names);require(sum((word(x) for x in atoms),())==word(e['x17']),'wrong atom word')
    pair=m.node(e['node55'],e['node65']);new75=m.node(m.node(e['node32'],e['node53']),pair)
    new37=m.node(pair,m.node(m.node(e['x27'],e['x19']),e['x35']))
    counts=[];best=1000;best_rows=None
    for use75 in (False,True):
        count=0;localbest=1000;atleast=False
        for chosen in trees(atoms):
            substitutions={e['x37']:new37}
            if use75:substitutions[e['node75']]=new75
            @lru_cache(None)
            def rec(t):
                if t==e['x17']:return chosen
                t=substitutions.get(t,t)
                if not m.isnode(t):return t
                _,a,b=m.store[t];return m.node(rec(a),rec(b))
            root=rec(m.root)
            if not has_helper(root):continue
            count+=1;c=cost(root);localbest=min(c,localbest)
            if c<best:
                rows=m.rows(root);require(graph(rows)==oldgraph,'best witness CFG changed')
                best=c;best_rows=rows
        counts.append({'new_node75_outside_x17':use75,'helper_bearing_sources':count,'minimum_estimate':localbest})
    result={'atom_names':names,'binary_associations':len(trees(atoms)),
            'variants_considered':2*len(trees(atoms)),'branches':counts,
            'helper_bearing_sources':sum(x['helper_bearing_sources'] for x in counts),
            'minimum_state_estimate':best,'source_sha256':sha256(raw).hexdigest(),
            'alias_data_sha256':sha256(aliasbytes).hexdigest(),
            'limitations':['Fixed eleven atoms, fixed x37 rewrite, only two outside-node75 choices.',
                           'Only the specified pure-decoder helper shape is admitted.',
                           'A source allocation estimate is not a compiled transition-table state count.',
                           'No global lower bound or PA theorem is proved.']}
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
