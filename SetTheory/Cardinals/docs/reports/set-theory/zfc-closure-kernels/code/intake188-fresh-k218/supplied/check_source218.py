#!/usr/bin/env python3
"""Reconstruct the K218 source and check its exact control graph against K219.

No search is run. The 205-node intermediate grammar is literal data. Equality
of the primitive-labelled control graphs gives a step-for-step simulation for
all register valuations, not just a finite test of selected executions.
"""
from pathlib import Path
import argparse,json,sys
from common import require,sha,dump,BASE_SOURCE_SHA,SOURCE_SHA
import source_language as sl
HERE=Path(__file__).resolve().parent
DAG_SHA='5b9f6c502ff0990bea4d0fa7065146241cd7e56cf342438eeb1645355a0c9e71'
PATHS_SHA='1cafe59d7f11ab442f9567711324391c37d2544f3fb2432e17327f4c43ac2dce'
LIB_SHA='4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f'

def load_pinned(name,digest):
    raw=(HERE/name).read_bytes();require(sha(raw)==digest,'Pinned construction input differs: '+name)
    return json.loads(raw)

def decode_dag(data):
    built=[];unique=set()
    for row in data['nodes']:
        require(isinstance(row,list) and row,'Malformed DAG node')
        if row[0]=='leaf':
            require(len(row)==3,'Malformed leaf node');node=tuple(row[1:])
        else:
            require(row[0]=='pair' and len(row)==3,'Malformed pair node')
            a,b=row[1:];require(type(a)is int and type(b)is int and 0<=a<len(built) and 0<=b<len(built),'DAG is not topological')
            node=(built[a],built[b])
        require(node not in unique,'DAG has duplicate nodes');unique.add(node);built.append(node)
    require(type(data['root'])is int and data['root']==len(built)-1,'DAG root convention')
    root=built[data['root']];require(sl.tree(sl.sites(root))==root,'DAG source syntax')
    require(sl.metrics(root)['dag_nodes']==len(built),'DAG contains unreachable nodes')
    return root

def construct(baseline):
    require(sha((HERE/'source_language.py').read_bytes())==LIB_SHA,'Source utility identity')
    oldraw=(baseline/'machine/sites219.json').read_bytes();require(sha(oldraw)==BASE_SOURCE_SHA,'Pinned K219 source differs')
    oldrows=json.loads(oldraw);oldtree=sl.tree(oldrows)
    stage=decode_dag(load_pinned('data/source205.dag.json',DAG_SHA));stagerows=sl.sites(stage)
    expected_paths=load_pinned('data/rotation_paths.json',PATHS_SHA)
    pattern=sl.subtree(stage,expected_paths[0]);require(not sl.leaf(pattern) and not sl.leaf(pattern[0]),'Rotation shape')
    A,B=pattern[0];C=pattern[1]
    require([len(sl.sites(x))for x in(A,B,C)]==[26,19,7],'Rotation component lengths')
    require(all(sl.boundary(x)==(0,0,False)for x in(A,B,C)),'Rotation components are not closed and halt-free')
    replacement=(A,(B,C));seen=[]
    def rotate(node,path=''):
        if node==pattern:seen.append(path);return replacement
        return node if sl.leaf(node)else(rotate(node[0],path+'0'),rotate(node[1],path+'1'))
    final=rotate(stage);require(seen==expected_paths,'Exact five occurrence paths')
    finalrows=sl.sites(final);raw=sl.compact(finalrows);require(sha(raw)==SOURCE_SHA,'Final source byte identity')
    word=lambda rows:[row[1:]for row in rows]
    require(word(oldrows)==word(stagerows)==word(finalrows),'Primitive word changed')
    graphs=[];checks=[]
    for rows in(oldrows,stagerows,finalrows):
        arithmetic,count=sl.graph_arithmetic(rows);interval=sl.graph_intervals(rows)
        require(arithmetic==interval,'Independent CFG resolvers disagree')
        graphs.append(arithmetic);checks.append(count)
    require(graphs[0]==graphs[1]==graphs[2],'Ordinal control graph changed')
    require(sl.metrics(oldtree)==dict(dag_nodes=206,leaf_occurrences=4744,maximum_depth=38,maximum_zero_run=6),'K219 source metrics')
    require(sl.metrics(stage)==sl.metrics(final)==dict(dag_nodes=205,leaf_occurrences=4744,maximum_depth=38,maximum_zero_run=6),'K218 source metrics')
    ranges=[]
    for prefix in seen:
        indices=[i for i,row in enumerate(stagerows)if row[0].startswith(prefix)]
        require(indices==list(range(indices[0],indices[0]+52)),'Rotation occurrence interval')
        ranges.append(dict(prefix=prefix,first_ordinal=indices[0],past_last_ordinal=indices[-1]+1))
    receipt=dict(status='EXACT_SOURCE_GRAPH_EQUIVALENCE_PASS',baseline_source_sha256=BASE_SOURCE_SHA,source_sha256=SOURCE_SHA,
        baseline_metrics=sl.metrics(oldtree),intermediate_metrics=sl.metrics(stage),final_metrics=sl.metrics(final),
        primitive_word_sha256=sha(sl.compact(word(finalrows))),control_graph_sha256=sha(sl.compact(graphs[2])),
        same_primitive_word=True,same_arithmetic_cfg=True,same_interval_cfg=True,successor_resolution_counts=checks,
        changed_codes_from_K219=sum(x[0]!=y[0]for x,y in zip(oldrows,finalrows)),
        changed_codes_in_final_rotation=sum(x[0]!=y[0]for x,y in zip(stagerows,finalrows)),
        final_rotation=dict(before='((A,B),C)',after='(A,(B,C))',component_leaf_counts=[26,19,7],
            component_boundaries=[list(sl.boundary(x))for x in(A,B,C)],occurrences=ranges),
        scope='Finite exact syntactic certificates imply all-register source control-graph equivalence by induction on primitive steps. Native runtime and blank initialization are separate certificates.')
    return final,raw,receipt

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline','--parent',dest='baseline',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
    tree,raw,receipt=construct(a.baseline);a.output.mkdir(parents=True,exist_ok=True)
    (a.output/'sites.json').write_bytes(raw);dump(a.output/'source.json',receipt);dump(a.output/'source_certificate.json',receipt)
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
