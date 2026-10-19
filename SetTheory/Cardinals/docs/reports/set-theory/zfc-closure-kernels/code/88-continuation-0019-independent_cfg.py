#!/usr/bin/env python3
"""Independent finite guarded-CFG partition audit.

Parses the frozen literal Prog254.v source without importing package checkers.
Uses the exact RegisterPath arithmetic; pads absent path bits with zero.
This certifies only source continuation equivalence, not a binary machine.
"""
from pathlib import Path
import argparse
import collections
import json
import re

def parse_source(path):
    text = path.read_text()
    body = text.split("Definition p254_tab : list (cedge * cedge) := [", 1)[1].split("].", 1)[0]
    row_pattern = re.compile(r"\(\s*(CN|CI|CD|CB|CC|CH)(?:\s+([0-9]+))?\s*,\s*(CN|CI|CD|CB|CC|CH)(?:\s+([0-9]+))?\s*\)\s*;?")
    rows=[]
    pos=0
    for m in row_pattern.finditer(body):
        if body[pos:m.start()].strip():
            raise ValueError("unparsed row prefix")
        row=[]
        for op,arg in ((m[1],m[2]),(m[3],m[4])):
            if (op=="CH") != (arg is None):
                raise ValueError("bad operand arity")
            row.append((op,int(arg) if arg is not None else None))
        rows.append(tuple(row));pos=m.end()
    if body[pos:].strip():raise ValueError("unparsed row suffix")
    assert len(rows)==6459
    leaves=[]
    visited=[]
    def descend(node,path,ancestors):
        assert node not in ancestors and 0<=node<len(rows)
        visited.append(node)
        for bit,(op,arg) in enumerate(rows[node]):
            p=path+str(bit)
            if op=="CN":descend(arg,p,ancestors+(node,))
            else:leaves.append((p,op,arg))
    descend(0,"",())
    assert visited==list(range(6459)) and len(leaves)==6460
    return rows,leaves

def increment(path):
    if not path:return ""
    return format((int(path,2)+1)%(1<<len(path)),f"0{len(path)}b")

def strip(path,bit,count):
    if not count:return path
    for i in range(len(path)-1,-1,-1):
        if path[i]==bit:
            count-=1
            if not count:return path[:i]
    return ""

def build_cfg(rows,leaves):
    leaf_index={p:i for i,(p,_,_) in enumerate(leaves)}
    def decode(path):
        node=0;depth=0;seen=""
        while True:
            bit=int(path[depth]) if depth<len(path) else 0
            seen+=str(bit);depth+=1
            op,arg=rows[node][bit]
            if op!="CN":return leaf_index[seen]
            node=arg
    successors=[]
    for path,op,arg in leaves:
        if op=="CH":nxt=[]
        elif op=="CI":nxt=[decode(increment(path))]
        elif op=="CD":
            nxt=[decode(increment(strip(path,"0",1))),decode(increment(path))]
        elif op=="CB":nxt=[decode(increment(strip(path,"0",arg)))]
        elif op=="CC":nxt=[decode(strip(path,"1",arg))]
        else:raise ValueError(op)
        successors.append(nxt)
    assert sum(map(len,successors))==8390
    return successors,decode("")

def number(signatures):
    ids={};out=[]
    for sig in signatures:
        if sig not in ids:ids[sig]=len(ids)
        out.append(ids[sig])
    return out

def refine(leaves,successors,merge_controls):
    labels=[("NOOP",None) if merge_controls and op in ("CB","CC") else (op,arg)
            for _,op,arg in leaves]
    classes=number(labels)
    history=[len(set(classes))]
    while True:
        updated=number([(labels[i],tuple(classes[j] for j in ns))
                        for i,ns in enumerate(successors)])
        history.append(len(set(updated)))
        if updated==classes:break
        classes=updated
    return classes,history

def verify_stability(leaves,successors,classes,merge_controls):
    members=collections.defaultdict(list)
    for i,k in enumerate(classes):members[k].append(i)
    for group in members.values():
        rep=group[0]
        _,op,arg=leaves[rep]
        label=("NOOP",None) if merge_controls and op in ("CB","CC") else (op,arg)
        signature=(label,tuple(classes[j] for j in successors[rep]))
        for i in group:
            _,op,arg=leaves[i]
            label=("NOOP",None) if merge_controls and op in ("CB","CC") else (op,arg)
            assert signature==(label,tuple(classes[j] for j in successors[i]))
    return members

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("source",type=Path,nargs="?",default=Path(__file__).resolve().parents[2]/"vendor/context246/sources/Prog254.v")
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    rows,leaves=parse_source(args.source);successors,initial=build_cfg(rows,leaves)
    result={"source":str(args.source),"leaves":len(leaves),"edges":sum(map(len,successors)),"initial_leaf":initial}
    for merge in (False,True):
        key="semantic_noop_labels" if merge else "literal_control_labels"
        classes,history=refine(leaves,successors,merge)
        groups=verify_stability(leaves,successors,classes,merge)
        result[key]={"classes":classes,"refinement_counts":history,
                     "class_count":len(groups),"largest_class":max(map(len,groups.values())),
                     "nonsingleton_classes":sum(len(g)>1 for g in groups.values())}
    result["sites"]=[{"index":i,"path":p,"operation":op,"argument":arg,"successors_zero_then_positive":successors[i]}
                     for i,(p,op,arg) in enumerate(leaves)]
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:{x:y for x,y in v.items() if x not in ("classes","refinement_counts")} if isinstance(v,dict) else v
                      for k,v in result.items() if k!="sites"},indent=2))

if __name__=="__main__":main()

