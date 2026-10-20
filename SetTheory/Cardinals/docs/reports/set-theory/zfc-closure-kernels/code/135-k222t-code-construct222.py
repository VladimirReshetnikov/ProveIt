#!/usr/bin/env python3
"""Reconstruct the conditional-K plus merged-equality K222 candidate.

This is a deterministic constructor, with two independent exact transition-fold
proofs. It uses the pinned conditional-K223 source/table, changes only the
specified logical-row and bundle intervals, and performs one closed rotation.
The retained source language and fold checker carry their original attribution.
"""
from pathlib import Path
from functools import cache
from collections import Counter
import sys,json

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'support'))
import source_language as s
import tm_tools as b
import check_folds as f
import argparse,hashlib

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--baseline-source',type=Path,required=True)
ap.add_argument('--baseline-table',type=Path,required=True)
ap.add_argument('--output-dir',type=Path,required=True)
args=ap.parse_args()
assert __debug__ and not sys.flags.optimize
sha=lambda raw:hashlib.sha256(raw).hexdigest()
assert sha(args.baseline_source.read_bytes())=='b4e453a8801597124fd9b3ee1cd2db1cdf80c0bd904c2ffb59b79d95e91a6e96'
assert sha(args.baseline_table.read_bytes())=='614adb7d387a5ccdaebecd37d8896d62bb162a20fb8b93b73ec2bd80bd75d785'
source=s.tree(json.loads(args.baseline_source.read_text()))
table=b.read_table(args.baseline_table.read_bytes())
groups,paths=b.decoder_map(table,source)
node_state={v:k for k,vs in groups.items() for v in vs}
q=lambda k:b.sole(groups,k)

@cache
def size(n):return 1 if s.leaf(n) else size(n[0])+size(n[1])
def flatten(n):return tuple((o,a) for p,o,a in s.sites(n))
pc,rel,eq,all_,imp,neg=(q(i) for i in [166,155,182,86,90,184])
all_imp=q(153);pair_inc=q(99);tail=q(193)
gate_copy=q(116)[1][1][1]
final_and=(neg,(imp,(neg,gate_copy)))
for macro in (pc,rel,eq,all_,imp,neg,all_imp,pair_inc,gate_copy,final_and):
    assert s.boundary(macro)==(0,0,False)
lower_block=((pc,(rel,all_imp)),(final_and,tail))
origins1={}
def lower(n):
    if n==q(224):origins1[lower_block]=n;return lower_block
    if s.leaf(n):return n
    result=tuple(map(lower,n))
    if result!=n:origins1[result]=n
    return result
stage1=lower(source)
assert flatten(source)[648:732]==flatten((pair_inc,eq))
replacement=((pair_inc,(rel,eq)),all_)
origins2={}
def replace_interval(n,pos):
    end=pos+size(n)
    if 732<=pos or end<=648:return n
    if 648<=pos and end<=732:return replacement if pos==648 else None
    a=replace_interval(n[0],pos)
    z=replace_interval(n[1],pos+size(n[0]))
    if a is None:return z
    if z is None:return a
    result=(a,z)
    if result!=n:origins2[result]=n
    return result
stage2=replace_interval(stage1,0)
origins={n:origins1.get(old,old) for n,old in origins2.items()}
origins.update({n:old for n,old in origins1.items() if n not in origins})

def compile_source(final_source,origins):
    live=set()
    def live_visit(n):
        if n in live:return
        live.add(n)
        if not s.leaf(n):live_visit(n[0]);live_visit(n[1])
    live_visit(final_source)
    origins={n:old for n,old in origins.items() if old not in live}
    compiled=table.copy();mapped=node_state.copy();mapped[final_source]=84
    fresh=300;claimed={84:final_source}
    def compile_node(n):
        nonlocal fresh
        if n in mapped:return mapped[n]
        assert not s.leaf(n)
        if n in origins and origins[n] in node_state and len(groups[node_state[origins[n]]])==1 and node_state[origins[n]] not in claimed:
            k=node_state[origins[n]]
        else:k=fresh;fresh+=1
        mapped[n]=k;claimed[k]=n
        for bit,ch in enumerate(n):
            if not s.leaf(ch):compiled[k,bit]=(bit,1,compile_node(ch));continue
            if n in origins and origins[n] in node_state and origins[n][bit]==ch:
                compiled[k,bit]=table[node_state[origins[n]],bit];continue
            choices=Counter(table[v,bit] for n0,v in node_state.items() if n0[bit]==ch)
            direct=[act for act,count in choices.items() if act[:2]==(bit,1)]
            if len(direct)==1:compiled[k,bit]=direct[0]
            elif ch==('CC',1) and bit==1:compiled[k,bit]=(0,-1,1)
            elif ch==('CC',2) and bit==1:compiled[k,bit]=(0,-1,16)
            elif ch==('CB',1) and bit==1:compiled[k,bit]=(0,-1,40)
            else:raise ValueError(('No primitive dispatch',ch,bit,choices))
        return k
    for bit,ch in enumerate(final_source):
        assert not s.leaf(ch)
        compiled[84,bit]=(bit,1,compile_node(ch))
    actual,paths=b.decoder_map(compiled,final_source)
    for state,alts in actual.items():
        assert all(mapped[n]==state for n in alts)
    reachable={0};todo=[0]
    for state in todo:
        for bit in (0,1):
            nxt=compiled[state,bit][2]
            if nxt!=254 and nxt not in reachable:reachable.add(nxt);todo.append(nxt)
    compiled={row:act for row,act in compiled.items() if row[0] in reachable}
    return compiled,mapped,actual

def rotated(source,origins,path='1110100100111000'):
    old_node=s.subtree(source,path)
    assert not s.leaf(old_node[0])
    a,z=old_node[0];d=old_node[1]
    assert all(s.boundary(v)==(0,0,False) for v in (a,z,d))
    new_node=(a,(z,d));nextorigins={}
    def rotate(n):
        if n==old_node:nextorigins[new_node]=origins.get(n,n);return new_node
        if s.leaf(n):return n
        result=tuple(map(rotate,n))
        if result!=n:nextorigins[result]=origins.get(n,n)
        return result
    new_source=rotate(source)
    nextorigins.update({n:old for n,old in origins.items() if n not in nextorigins})
    assert flatten(new_source)==flatten(source)
    assert s.graph_arithmetic(s.sites(new_source))[0]==s.graph_arithmetic(s.sites(source))[0]
    return new_source,nextorigins


# The final source, including the closed zero-run repair, is explicit.
final_source,final_origins=rotated(stage2,origins)
assert s.metrics(final_source)==dict(dag_nodes=209,leaf_occurrences=4581,maximum_depth=38,maximum_zero_run=6)
final_sites=s.sites(final_source)
flat_graph,checks=s.graph_arithmetic(final_sites)
assert flat_graph==s.graph_intervals(final_sites)==s.graph_arithmetic(s.sites(stage2))[0]==s.graph_intervals(s.sites(stage2))
parent,mapped,parent_decoder=compile_source(final_source,final_origins)
assert len(parent)==448
folds=[
    dict(keep=118,delete=303,a0=[0,1,155],a1=[1,1,153],invariant={'118':{'0':0},'159':{'1':0}}),
    dict(keep=159,delete=302,a0=[0,1,166],a1=[1,1,118],invariant={})]
old=parent;proof=[]
for fold in folds:
    facts,invariant=f.check_inductive_invariant(old,fold['invariant'])
    new,phi=f.transformed(old,fold)
    keep,drop=fold['keep'],fold['delete'];blocks=[];skipped=[]
    for q in (keep,drop):
        for bit in (0,1):
            if 0 in facts[q] and facts[q][0]!=bit:skipped.append([q,bit]);continue
            init=dict(facts[q]);init[0]=bit
            w,d,z=old[q,bit];expected=dict(init);expected[0]=w
            block=f.local_block(new,keep,init,(phi(z),d,expected),16)
            blocks.append(dict(old_state=q,read_bit=bit,initial_patch=init,**block))
    for (q,bit),(w,d,z) in old.items():
        if q not in (keep,drop):assert new[phi(q),bit]==(w,d,phi(z))
    proof.append(dict(specification=fold,old_states=len(old)//2,new_states=len(new)//2,
        invariant=invariant,impossible_fold_branches=skipped,positive_blocks=blocks))
    old=new
assert len(old)==444
actual,paths=b.decoder_map(old,final_source)
for q,alternatives in actual.items():
    for node in alternatives:
        expected=mapped[node]
        if expected==303:expected=118
        if expected==302:expected=159
        assert expected==q
canonical,labels=b.canonical(old)
assert labels[254]==222 and labels[0]==0
candidate_raw=b.table_bytes(old);source_raw=s.compact(final_sites)
assert sha(candidate_raw)=='d1ad27580fb8ec41c183760e738a03b1651cc7e2bebc2d48a29a893ca8b34e40'
assert sha(source_raw)=='b8f0b7ef8b9f41329509335f844c5fce94ea9b6cfa8f8a3ca7ebb9fe8c736c13'
output=args.output_dir
assert not output.exists() or (output.is_dir() and not any(output.iterdir()))
output.mkdir(parents=True,exist_ok=True)
artifacts={'parent224.k.tm':b.table_bytes(parent),'candidate222.k.tm':candidate_raw,
    'candidate222.tm':b.table_bytes(canonical),'sites.json':source_raw}
for name,raw in artifacts.items():(output/name).write_bytes(raw)
def dump(name,value):(output/name).write_text(json.dumps(value,indent=2)+'\n')
dump('canonical_map.json',dict(k_to_canonical=labels,start=0,halt=222,dispatcher=labels[84]))
dump('fold_proof.json',dict(status='ALL_TAPE_POSITIVE_BLOCK_FOLD_CHAIN_PASS',folds=proof,
    scope='Same start state and every initial binary tape. Every old step is matched by a positive finite block; all unmentioned tape cells are arbitrary and preserved.'))
receipt=dict(status='DETERMINISTIC_K222_SOURCE_AND_TABLE_CONSTRUCTION_PASS',
    working_states=222,transition_rows=444,source_metrics=s.metrics(final_source),
    source_graph_checks=checks,independent_graph_resolvers_agree=True,
    decoder_subtrees=sum(map(len,actual.values())),decoder_states=len(actual),
    alias_savings=sum(len(v)-1 for v in actual.values()),
    prefix_occurrences=sum(map(len,paths.values())),
    parent_states=len(parent)//2,final_fold_deletions=[303,302],
    start_canonical=0,halt_canonical=222,dispatcher_canonical=labels[84],
    sha256={name:sha(raw) for name,raw in artifacts.items()},
    scope='Exact source construction, source CFG, decoder relation, two all-tape fold simulations and complete canonical row conjugacy. The independent emitter, logic and unbounded runtime certificates are separate required layers.')
dump('construction.json',receipt)
print(json.dumps(receipt,indent=2))
