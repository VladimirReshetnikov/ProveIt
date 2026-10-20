#!/usr/bin/env python3
"""Deterministically reconstruct seed-G222 from the frozen seed-K223 source.

This constructor performs no search. The theory/emitter proof and full unbounded
binary runtime are independently checked by separate programs.
"""
from pathlib import Path
from functools import cache
import argparse,hashlib,json,sys

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--support-dir',type=Path,required=True)
    ap.add_argument('--baseline-source',type=Path,required=True)
    ap.add_argument('--baseline-table',type=Path,required=True)
    ap.add_argument('--baseline-grammar',type=Path,required=True)
    ap.add_argument('--output-dir',type=Path,required=True)
    args=ap.parse_args()
    sys.path.insert(0,str(args.support_dir.resolve()))
    import source_language as s
    import tm_tools as tm
    assert __debug__ and not sys.flags.optimize
    sha=lambda b:hashlib.sha256(b).hexdigest()
    assert sha(args.baseline_source.read_bytes())=='df55079f114a6aa9ada970d7d857726e47e3a3dba2a721245ebbacfd4577c13c'
    assert sha(args.baseline_table.read_bytes())=='7e036b1bd05fe8a7e5877a8c5386cae603f4d689adeeb13754ee98dca998bfef'
    assert sha(args.baseline_grammar.read_bytes())=='8b8dd4e165d8a08f7def72eca7f345da231aa3f0c7e318f3e23fddfa8b368f6a'
    parent=s.tree(json.loads(args.baseline_source.read_text()))
    table=tm.read_table(args.baseline_table.read_bytes())
    spec=json.loads(args.baseline_grammar.read_text())
    groups,_=tm.decoder_map(table,parent)
    q=lambda k:tm.sole(groups,k)
    flat=lambda t:tuple((op,arg) for path,op,arg in s.sites(t))
    @cache
    def size(n):return 1 if s.leaf(n) else size(n[0])+size(n[1])

    target='11101001001110'
    oldax=s.subtree(parent,target)
    units={}
    def unravel(pattern,node):
        if type(pattern)is int:units[pattern]=node;return
        unravel(pattern[0],node[0]);unravel(pattern[1],node[1])
    unravel(spec['pattern'],oldax)
    assert set(units)==set(range(164))
    removed=set()
    for i,record in enumerate(spec['units']):
        role=record['role']
        assert size(units[i])==record['leaves']
        assert sha(s.compact(s.sites(units[i])))==record['source_sha256']
        assert s.boundary(units[i])==(0,0,False)
        if isinstance(role,dict) and (9<=role['word_index']<=19 or role['word_index']==74):removed.add(i)
    def rebuild(pattern):
        if type(pattern)is int:return None if pattern in removed else units[pattern]
        x,y=map(rebuild,pattern)
        return y if x is None else x if y is None else (x,y)
    stage1=s.replace(parent,target,rebuild(spec['pattern']))

    # Quantify the equality-row consequent by its canonical relation code.
    pair_inc,rel,eq,all_=q(99),q(155),q(182),q(86)
    assert flat(stage1)[648:732]==flat((pair_inc,eq))
    replacement=((pair_inc,(rel,eq)),all_)
    def splice(n,start):
        end=start+size(n)
        if 732<=start or end<=648:return n
        if 648<=start and end<=732:return replacement if start==648 else None
        assert not s.leaf(n)
        x=splice(n[0],start);y=splice(n[1],start+size(n[0]))
        return y if x is None else x if y is None else (x,y)
    stage2=splice(stage1,0)

    # One closed reassociation restores the inherited six-zero address bound.
    path='1110100100111000'
    oldnode=s.subtree(stage2,path);a,b=oldnode[0];c=oldnode[1]
    assert all(s.boundary(n)==(0,0,False) for n in(a,b,c))
    newnode=a,(b,c)
    def rotate(n):
        if n==oldnode:return newnode
        return n if s.leaf(n) else tuple(map(rotate,n))
    final=rotate(stage2)
    assert flat(final)==flat(stage2)
    graph,count=s.graph_arithmetic(s.sites(final))
    assert graph==s.graph_arithmetic(s.sites(stage2))[0]==s.graph_intervals(s.sites(final))==s.graph_intervals(s.sites(stage2))
    source_bytes=s.compact(s.sites(final))
    assert sha(source_bytes)=='cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e'

    # Exact literal table delta. Hidden helper uses are checked by full runtime.
    delta={(116,1):(1,1,214),(118,1):(1,1,153),(185,0):(0,1,90),
        (207,0):(0,1,300),(207,1):(1,1,301),(210,1):(1,1,159),
        (300,0):(0,1,99),(300,1):(1,1,157),(301,0):(0,1,86),(301,1):(1,1,205)}
    table.update(delta)
    table={row:act for row,act in table.items() if row[0] not in(65,135,212)}
    raw=tm.table_bytes(table)
    assert sha(raw)=='726583d188c22ee0d8572083a22497657c60e33fc80159d317767046dbbda365'
    assert len(table)==444
    canonical,labels=tm.canonical(table)
    assert set(labels.values())==set(range(223))
    actual,paths=tm.decoder_map(table,final)
    assert sum(map(len,actual.values()))==185 and len(actual)==173
    assert s.metrics(final)==dict(dag_nodes=208,leaf_occurrences=4744,maximum_depth=36,maximum_zero_run=6)
    out=args.output_dir;out.mkdir(parents=True,exist_ok=True)
    (out/'candidate.k.tm').write_bytes(raw)
    (out/'candidate222.tm').write_bytes(tm.table_bytes(canonical))
    (out/'sites.json').write_bytes(source_bytes)
    (out/'canonical_map.json').write_text(json.dumps(labels,indent=2)+'\n')
    receipt=dict(status='DETERMINISTIC_SEED_G222_RECONSTRUCTION_PASS',working_states=222,rows=444,
        source_sha256=sha(source_bytes),k_table_sha256=sha(raw),canonical_table_sha256=sha(tm.table_bytes(canonical)),
        source_metrics=s.metrics(final),guarded_cases=count,decoder_roles=185,decoder_states=173,alias_savings=12,
        removed_old_states=[65,135,212],added_states=[300,301],changed_retained_rows=6,
        removed_macro_indices=list(range(9,20))+[74],closed_rotation=path,
        scope='Exact source/table reconstruction and finite source-prefix census. Independent all-natural emitter, logical calibration, blank bootstrap and unbounded binary runtime remain required.')
    (out/'construction.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
