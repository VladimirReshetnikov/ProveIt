#!/usr/bin/env python3
"""Independently verify root's source continuation quotient and no-op rank."""
from pathlib import Path
import collections
import json, argparse
from independent_cfg import parse_source,build_cfg,number,refine
ROOT=Path(__file__).resolve().parents[2]
ap=argparse.ArgumentParser()
ap.add_argument("--source",type=Path,default=ROOT/"vendor/context246/sources/Prog254.v")
ap.add_argument("--certificate",type=Path,default=ROOT/"experiments/audit_inputs/quotient.json")
ap.add_argument("--output",type=Path,default=ROOT/"results/audit/quotient_audit.json")
args=ap.parse_args()
rows,leaves=parse_source(args.source)
succ,initial=build_cfg(rows,leaves)
given=json.loads(args.certificate.read_text())
assert all(len(given[k])==len(leaves) for k in
           ("sites","graph","epsilon","rank","classes","labelled","generic_noop"))
ops={"CI":"I","CD":"D","CB":"B","CC":"C","CH":"H"}
for i,(p,op,arg) in enumerate(leaves):
    label=[ops[op]] if arg is None else [ops[op],arg]
    assert given["sites"][i]==[p,label],(i,given["sites"][i],[p,label])
    # Root graph has positive before zero; the independent graph zero before positive.
    edges=list(reversed(succ[i])) if op=="CD" else succ[i]
    assert given["graph"][i]==[label,edges],(i,given["graph"][i],[label,edges])

epsilon=[];rank=[]
for i in range(len(leaves)):
    cursor=i;seen=set();r=0
    while leaves[cursor][1] in ("CB","CC"):
        assert cursor not in seen,("control-only cycle",i)
        seen.add(cursor);r+=1;cursor=succ[cursor][0]
    epsilon.append(cursor);rank.append(r)
assert epsilon==given["epsilon"]
assert rank==given["rank"] and max(rank)==4
for i,(_,op,_) in enumerate(leaves):
    if op in ("CB","CC"):
        assert rank[succ[i][0]]==rank[i]-1
        assert epsilon[succ[i][0]]==epsilon[i]
    else:assert rank[i]==0

labels=[leaves[epsilon[i]][1:] for i in range(len(leaves))]
classes=number(labels);history=[len(set(classes))]
while True:
    updated=number([(labels[i],tuple(classes[epsilon[j]] for j in succ[epsilon[i]]))
                    for i in range(len(leaves))])
    history.append(len(set(updated)))
    if updated==classes:break
    classes=updated

def same_partition(one,two):
    assert len(one)==len(two)
    forward={};reverse={}
    for a,b in zip(one,two):
        assert a not in forward or forward[a]==b
        assert b not in reverse or reverse[b]==a
        forward[a]=b;reverse[b]=a
    return len(forward)
assert same_partition(classes,given["classes"])==given["count"]==4530
strong,sh=refine(leaves,succ,False)
noop,nh=refine(leaves,succ,True)
assert same_partition(strong,given["labelled"])==6217
assert same_partition(noop,given["generic_noop"])==6214

groups=collections.defaultdict(list)
for i,k in enumerate(classes):groups[k].append(i)
counts=collections.Counter(rank)
record={"status":"PASS","source_rows":len(rows),"source_leaves":len(leaves),
        "guarded_edges":sum(map(len,succ)),"weak_classes":len(groups),
        "independent_partition_matches_up_to_renaming":True,
        "control_only_cycles":0,"maximum_control_distance":max(rank),
        "control_distance_histogram":dict(sorted(counts.items())),
        "largest_weak_class":max(map(len,groups.values())),
        "strong_literal_classes":6217,"strong_noop_classes":6214,
        "method":"Independent literal parser and path arithmetic; no root or delivered verifier imports.",
        "scope":"Source graph, all class partitions, epsilon closures and rank only. No TM claim."}
args.output.write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps(record,indent=2))

