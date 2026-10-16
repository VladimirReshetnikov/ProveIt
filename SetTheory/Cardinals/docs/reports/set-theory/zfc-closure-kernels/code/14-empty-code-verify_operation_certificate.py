#!/usr/bin/env python3
"""Verify a finite operation bisimulation of two binary register-program DAGs.

Adapted from the independent checker in the user's incoming
zfc_one_schema_research/machine/verify_rm_certificate.py, generalized to two
explicit JSON input DAGs. This uses string/integer path arithmetic, does not
execute either generator or TM backend, and checks both decrement branches.
The finite verifier itself is not prover-formalized.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import cache
import hashlib
import json
from pathlib import Path
import re


class Machine:
    def __init__(self,path):
        data=json.loads(path.read_text())
        if data["root"]!=0:raise ValueError("expected root zero")
        self.rows={int(n):tuple(es) for n,es in data["nodes"].items()}
        if set(self.rows)!=set(range(len(self.rows))):raise ValueError("invalid node labels")
        for edges in self.rows.values():
            if len(edges)!=2:raise ValueError("nonbinary node")
            for edge in edges:
                if re.fullmatch(r"(ENode|EInc|EDecnz|EBreak|EContinue) (\d+)|EHalt",edge) is None:
                    raise ValueError("invalid edge")
                if edge.startswith("ENode ") and int(edge[6:]) not in self.rows:
                    raise ValueError("missing referenced node")

    @cache
    def lookup(self,pc):
        q,actual=0,""
        for cursor in range(len(self.rows)+1):
            bit=pc[cursor] if cursor<len(pc) else "0"
            if bit not in "01":raise ValueError("nonbinary PC")
            actual+=bit;edge=self.rows[q][int(bit)]
            if not edge.startswith("ENode "):return actual,edge
            q=int(edge[6:])
        raise ValueError("decoder cycle")

    @staticmethod
    def successor(pc):
        return "" if not pc else format((int(pc,2)+1)%(1<<len(pc)),f"0{len(pc)}b")

    @staticmethod
    def strip(pc,bit,count):
        for _ in range(count):
            pos=pc.rfind(bit)
            if pos<0:return ""
            pc=pc[:pos]
        return pc

    @cache
    def contract(self,pc):
        seen=set()
        while True:
            path,edge=self.lookup(pc)
            if edge=="EHalt" or edge.startswith(("EInc ","EDecnz ")):
                return path,edge
            if path in seen:raise ValueError("control-only cycle")
            seen.add(path)
            kind,arg=edge.split()
            if kind=="EBreak":pc=self.successor(self.strip(path,"0",int(arg)))
            elif kind=="EContinue":pc=self.strip(path,"1",int(arg))
            else:raise ValueError("unsupported operation")

    def successors(self,path,edge):
        if edge=="EHalt":return []
        positive=self.contract(self.successor(path))
        if edge.startswith("EInc "):return [positive]
        if not edge.startswith("EDecnz "):raise ValueError("nonoperation certificate entry")
        return [self.contract(self.successor(self.strip(path,"0",1))),positive]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source",type=Path,required=True)
    ap.add_argument("--candidate",type=Path,required=True)
    ap.add_argument("--certificate",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    old,new=Machine(args.source),Machine(args.candidate)
    certificate=json.loads(args.certificate.read_text());records=certificate["pairs"]
    if certificate["initial"]!=0 or certificate["branch_order"]!="EDecnz: zero, positive":
        raise ValueError("wrong certificate convention")
    if old.contract("")!=(records[0]["old"],records[0]["instruction"]):raise ValueError("old entry mismatch")
    if new.contract("")!=(records[0]["new"],records[0]["instruction"]):raise ValueError("new entry mismatch")
    distinct=set();successor_count=0
    for record in records:
        left,right,label=record["old"],record["new"],record["instruction"]
        if (left,right) in distinct:raise ValueError("duplicate related pair")
        distinct.add((left,right))
        if old.lookup(left)!=(left,label) or new.lookup(right)!=(right,label):
            raise ValueError("unequal operation label")
        successors=record["successors"]
        lt,rt=old.successors(left,label),new.successors(right,label)
        if len(successors)!=len(lt) or len(lt)!=len(rt):raise ValueError("branch mismatch")
        for index,a,b in zip(successors,lt,rt,strict=True):
            if type(index) is not int or not 0<=index<len(records):raise ValueError("invalid successor")
            target=records[index]
            if a!=(target["old"],target["instruction"]) or b!=(target["new"],target["instruction"]):
                raise ValueError("unrelated successor")
            successor_count+=1
    seen,pending=set(),[0]
    while pending:
        q=pending.pop()
        if q not in seen:
            seen.add(q);pending.extend(records[q]["successors"])
    if len(seen)!=len(records):raise ValueError("unreachable certificate entries")
    result={"verified":True,"related_operation_pairs":len(records),
            "successor_pairs_verified":successor_count,
            "source_nodes":len(old.rows),"candidate_nodes":len(new.rows),
            "instruction_counts":dict(Counter(r["instruction"].split()[0] for r in records)),
            "all_related_pairs_reachable_from_entry":True,
            "both_decrement_branches_checked":True,
            "source_sha256":hashlib.sha256(args.source.read_bytes()).hexdigest(),
            "candidate_sha256":hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
            "certificate_sha256":hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
            "verifier_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "proof_assistant_verified":False,"binary_TM_compiler_verified":False}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":main()
