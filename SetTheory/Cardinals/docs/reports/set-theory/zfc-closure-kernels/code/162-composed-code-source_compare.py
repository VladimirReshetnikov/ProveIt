#!/usr/bin/env python3
"""Independent complete source CFG comparison, with no register sampling.

A complete binary source tree gives implicit program order. A zero decrement
or a break exits the k-th enclosing left branch; a continue restarts the k-th
enclosing right branch. Fallthrough wraps at the whole-program boundary.
"""
from pathlib import Path
import argparse, hashlib, json

def require(b, m):
    if not b: raise ValueError(m)

def compact(x): return (json.dumps(x,separators=(',',':'))+'\n').encode()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def inspect(path):
    rows=json.loads(Path(path).read_text())
    require(isinstance(rows,list) and rows, 'Empty source')
    positions={}
    for i,row in enumerate(rows):
        require(isinstance(row,list) and len(row)==3, 'Malformed source row')
        p,op,arg=row
        require(isinstance(p,str) and p and set(p)<={'0','1'}, 'Invalid path')
        require(p not in positions, 'Duplicate path')
        require(op in ('CI','CD','CB','CC','CH'), 'Invalid primitive')
        require(arg is None if op=='CH' else type(arg) is int and (0<=arg<9 if op in ('CI','CD') else arg>=1), 'Invalid argument')
        positions[p]=i
    ranges={};nodes={};leaf_order=[]
    def tree(p):
        if p in positions:
            i=positions[p];leaf_order.append(i);ranges[p]=(i,i+1);nodes[p]=tuple(rows[i][1:]);return
        require(len(p)<max_depth, 'Incomplete binary tree')
        tree(p+'0');tree(p+'1')
        lo,mid=ranges[p+'0'];mid2,hi=ranges[p+'1']
        require(mid==mid2,'Noncontiguous leaf order')
        ranges[p]=(lo,hi);nodes[p]=(nodes[p+'0'],nodes[p+'1'])
    max_depth=max(map(len,positions))
    tree('')
    require(leaf_order==list(range(len(rows))), 'Source not ordered or overlapping')
    n=len(rows);graph=[]
    def escape(p,side,k):
        ancestors=[p[:j] for j in range(len(p)-1,-1,-1) if p[j]==side]
        if len(ancestors)<k:return 0
        lo,hi=ranges[ancestors[k-1]]
        return (hi%n) if side=='0' else lo
    for i,(p,op,arg) in enumerate(rows):
        after=(i+1)%n
        if op=='CI': successors=[after]
        elif op=='CD': successors=[escape(p,'0',1),after]
        elif op=='CB': successors=[escape(p,'0',arg)]
        elif op=='CC': successors=[escape(p,'1',arg)]
        else: successors=[]
        graph.append([op,arg,successors])
    metrics={'dag_nodes':len(set(nodes.values())), 'primitive_occurrences':n,
             'guarded_cases':sum(2 if op=='CD' else 1 for p,op,arg in rows),
             'guarded_successors':sum(len(g[2]) for g in graph),
             'maximum_depth':max_depth,
             'maximum_zero_run':max(len(run) for p in positions for run in p.split('1'))}
    return rows,graph,metrics

def main():
    ap=argparse.ArgumentParser();ap.add_argument('reference',type=Path);ap.add_argument('candidate',type=Path);ap.add_argument('output',type=Path);a=ap.parse_args()
    r,rg,rm=inspect(a.reference);c,cg,cm=inspect(a.candidate)
    require(len(r)==len(c),'Primitive count changed')
    require([x[1:]for x in r]==[x[1:]for x in c],'Primitive word changed')
    require(rg==cg,'Guarded control graph changed')
    record={'status':'ALL_NATURAL_STRONG_SOURCE_BISIMULATION',
        'reference_sha256':sha(a.reference),'candidate_sha256':sha(a.candidate),
        'reference_metrics':rm,'candidate_metrics':cm,
        'changed_addresses':sum(x[0]!=y[0]for x,y in zip(r,c)),
        'complete_guarded_graph_sha256':hashlib.sha256(compact(rg)).hexdigest(),
        'checker_sha256':sha(__file__),
        'relation':'Same primitive ordinal and same nine natural register values.',
        'theorem':'For each guard the identical primitive performs identical register updates and has identical successor ordinal. By induction the relation is a strong source bisimulation, preserving halting for every natural store and every source ordinal.',
        'scope':'Finite exact CFG proof. Does not certify a binary implementation or a consistency calibration.'}
    a.output.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
if __name__=='__main__':main()
