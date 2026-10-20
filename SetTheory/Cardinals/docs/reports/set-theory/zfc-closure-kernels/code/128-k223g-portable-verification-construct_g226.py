#!/usr/bin/env python3
"""Reproduce the 226-state parent of the merged-equality 223-state candidate.

Inputs are the pinned portable K224 package and its upstream K226 utility tree.
This constructor changes the numerical proof calculus as described in the report;
only the last, closed source-tree rotation is an equivalence to the preceding
source. The calculus equivalence and the three finite transition folds are
separate certificates. Decoder checks below are finite syntactic checks, not a
substitute for the universal binary runtime certificate.
"""
from pathlib import Path
from functools import cache
from collections import Counter
import argparse, hashlib, json, sys


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline224',type=Path,required=True)
    parser.add_argument('--upstream226',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    sys.path.insert(0,str(args.upstream226/'verification'))
    import reconstruct227 as c
    sys.path.insert(0,str(args.baseline224/'portable/verification'))
    import construct_rel225 as cr
    source_path=args.baseline224/'portable/parent225/sites225.json'
    table_path=args.baseline224/'portable/parent225/candidate225.k.tm'
    source=c.tree(json.loads(source_path.read_text()))
    table=cr.read_table(table_path)
    groups,paths=cr.decoder_map(c,table,source)
    node_state={v:k for k,vs in groups.items() for v in vs}
    q=lambda k:cr.sole(groups,k)
    digest=lambda raw:hashlib.sha256(raw).hexdigest()
    assert digest(source_path.read_bytes())=='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878'
    assert digest(table_path.read_bytes())=='4526bd8cf2160ac5dfce039add0550e9788095f60ecc6b4462afd4ebbfd42790'
    @cache
    def size(n):return 1 if c.leaf(n) else size(n[0])+size(n[1])
    def flatten(n):return tuple((o,a) for p,o,a in c.sites(n))
    def source_bytes(n):return c.compact(c.sites(n))

    # Macro names refer to the supplied canonical parent225 decoder, not final
    # compact labels. PushC, Rel(a,b), Eq(a,b), All, Imp, Neg are closed programs.
    pc,rel,eq,all_,imp,neg=(q(i) for i in [166,155,182,86,90,184])
    all_imp=q(153);pair_inc=q(99);tail=q(193)
    gate_copy=q(116)[1][1][1]
    final_and=(neg,(imp,(neg,gate_copy)))
    for macro in (pc,rel,eq,all_,imp,neg,all_imp,pair_inc,gate_copy,final_and):
        assert c.boundary(macro)==(0,0,False)
    lower_block=((pc,(rel,all_imp)),(final_and,tail))
    origins1={}
    def lower(n):
        if n==q(224):origins1[lower_block]=n;return lower_block
        if c.leaf(n):return n
        result=tuple(map(lower,n))
        if result!=n:origins1[result]=n
        return result
    stage1=lower(source)

    # The old interval is the last two increments of Eq(c,b), followed by
    # Eq(a,b). Insert Rel(a,b) before the latter and All after it. Thus the row
    # becomes Eq(c,a) -> (Eq(c,b) -> All_Rel(a,b) Eq(a,b)).
    assert flatten(source)[648:732]==flatten((pair_inc,eq))
    replacement=((pair_inc,(rel,eq)),all_)
    origins2={}
    def replace_interval(n,pos):
        end=pos+size(n)
        if 732<=pos or end<=648:return n
        if 648<=pos and end<=732:return replacement if pos==648 else None
        a=replace_interval(n[0],pos)
        b=replace_interval(n[1],pos+size(n[0]))
        if a is None:return b
        if b is None:return a
        result=(a,b)
        if result!=n:origins2[result]=n
        return result
    stage2=replace_interval(stage1,0)
    origins={n:origins1.get(old,old) for n,old in origins2.items()}
    origins.update({n:old for n,old in origins1.items() if n not in origins})

    # This closed right rotation is indispensable: it reduces the maximum
    # consecutive-zero source address from seven to six without adding a DAG
    # node. The eight-zero reset routine is thereby used within its old bound.
    rotation_path='1110100100111000'
    old_node=c.subtree(stage2,rotation_path)
    assert not c.leaf(old_node[0])
    a,b=old_node[0];d=old_node[1]
    assert all(c.boundary(v)==(0,0,False) for v in (a,b,d))
    new_node=(a,(b,d));origins3={}
    def rotate(n):
        if n==old_node:origins3[new_node]=origins.get(n,n);return new_node
        if c.leaf(n):return n
        result=tuple(map(rotate,n))
        if result!=n:origins3[result]=origins.get(n,n)
        return result
    final_source=rotate(stage2)
    origins3.update({n:old for n,old in origins.items() if n not in origins3})
    final_rows=c.sites(final_source);stage2_rows=c.sites(stage2)
    cfg2,checks2=c.graph_arithmetic(stage2_rows)
    cfg3,checks3=c.graph_arithmetic(final_rows)
    assert cfg2==cfg3==c.graph_intervals(stage2_rows)==c.graph_intervals(final_rows)
    assert flatten(final_source)==flatten(stage2)
    assert c.metrics(final_source)==dict(dag_nodes=209,leaf_occurrences=4581,maximum_depth=38,maximum_zero_run=6)

    # Compile new source nodes while retaining the existing binary instruction
    # engine. A node whose old source meaning remains live may not be overwritten.
    live=set()
    def live_visit(n):
        if n in live:return
        live.add(n)
        if not c.leaf(n):live_visit(n[0]);live_visit(n[1])
    live_visit(final_source)
    origins3={n:old for n,old in origins3.items() if old not in live}
    compiled=table.copy();mapped=node_state.copy();mapped[final_source]=84
    fresh=300;claimed={84:final_source}
    def compile_node(n):
        nonlocal fresh
        if n in mapped:return mapped[n]
        assert not c.leaf(n)
        if n in origins3 and origins3[n] in node_state and len(groups[node_state[origins3[n]]])==1 and node_state[origins3[n]] not in claimed:
            k=node_state[origins3[n]]
        else:k=fresh;fresh+=1
        mapped[n]=k;claimed[k]=n
        for bit,ch in enumerate(n):
            if not c.leaf(ch):compiled[k,bit]=(bit,1,compile_node(ch));continue
            if n in origins3 and origins3[n] in node_state and origins3[n][bit]==ch:
                compiled[k,bit]=table[node_state[origins3[n]],bit];continue
            choices=Counter(table[s,bit] for v,s in node_state.items() if v[bit]==ch)
            direct=[act for act,count in choices.items() if act[:2]==(bit,1)]
            if len(direct)==1:compiled[k,bit]=direct[0]
            elif ch==('CC',1) and bit==1:compiled[k,bit]=(0,-1,1)
            elif ch==('CC',2) and bit==1:compiled[k,bit]=(0,-1,16)
            elif ch==('CB',1) and bit==1:compiled[k,bit]=(0,-1,40)
            else:raise ValueError(('No primitive dispatch',ch,bit,choices))
        return k
    for bit,ch in enumerate(final_source):
        assert not c.leaf(ch)
        compiled[84,bit]=(bit,1,compile_node(ch))

    # Check every compound decoder entry against its source address, including
    # nontrivial shared-state decoders which temporarily move left into prefixes.
    entries=0
    def verify(n,p,k):
        nonlocal entries
        if c.leaf(n):return
        assert mapped[n]==k
        for bit,ch in enumerate(n):
            if c.leaf(ch):continue
            tape={i:int(b) for i,b in enumerate(p+str(bit))};tape[-1]=1
            before=tape.copy();head=len(p);state=k
            for tick in range(100):
                if head==len(p)+1:break
                assert head in tape
                write,direction,state=compiled[state,tape[head]]
                tape[head]=write;head+=direction
            assert tape==before and head==len(p)+1 and state==mapped[ch],(p,k,bit)
            entries+=1;verify(ch,p+str(bit),state)
    verify(final_source,'',84)
    reachable={0};todo=[0]
    for state in todo:
        for bit in (0,1):
            nxt=compiled[state,bit][2]
            if nxt!=254 and nxt not in reachable:reachable.add(nxt);todo.append(nxt)
    compiled={row:act for row,act in compiled.items() if row[0] in reachable}
    cr.decoder_map(c,compiled,final_source)
    assert len(compiled)==452
    encoded=cr.encode_table(compiled)
    assert digest(source_bytes(final_source))=='fe3713adaf008a71ba4fbc6433de760ef124b8638efbc5c75e3afa2c1142c24f'
    assert digest(encoded)=='e7069fe4dc12fe62ba66cd88c27a51bfd83d548daad07591d3e0b0afaf6afe3d'
    receipt=dict(construction='merged equality row G; K and membership-vacuity bundle; one closed rotation',
        source_parent_sha256=digest(source_path.read_bytes()),table_parent_sha256=digest(table_path.read_bytes()),
        source_sha256=digest(source_bytes(final_source)),table_sha256=digest(encoded),
        source_metrics=c.metrics(final_source),parent_states=len(compiled)//2,new_labels_allocated=fresh-300,
        rotation=dict(path=rotation_path,direction='right',closed_factors=True,guarded_cfg_equal=True,
            independent_resolvers_agree=True,checks_before=checks2,checks_after=checks3),
        decoder_compound_entries_checked=entries,
        scope='Finite source and decoder checks. Formal calculus calibration, binary runtime, and three folds are separate artifacts.')
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'sites226.json').write_bytes(source_bytes(final_source))
    (args.output/'parent226.k.tm').write_bytes(encoded)
    (args.output/'construction_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
