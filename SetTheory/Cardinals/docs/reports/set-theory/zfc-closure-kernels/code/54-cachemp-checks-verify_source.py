#!/usr/bin/env python3
"""Exact finite checks of cache-valued MP for the pinned Dag254 program.

This is a standard-library diagnostic, not a formal proof or a binary TM.
The ordinary unbounded proof is in cache_mp_proof.md.  No large integer
fingerprints, floating point, or caught resource failures are used.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from math import isqrt
from pathlib import Path
import random
import re

PIN = "43026ff42f0939f09b9e95495248cfadcad38e38"
DAG_SHA = "538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3"

def pair(a: int, b: int) -> int:
    return (a+b)*(a+b+1)//2+b

def unpair(n: int) -> tuple[int, int]:
    s = (isqrt(8*n+1)-1)//2
    b = n-s*(s+1)//2
    return s-b, b

def imp(a: int, b: int) -> int:
    return 4*pair(a,b)

@dataclass(frozen=True)
class Working:
    top: int
    stack: int
    parameter: int
    cache: int

def step(command: tuple[str,int], w: Working, *, old: bool = False) -> Working | None:
    op,x = command
    t,s,d,h = w.top,w.stack,w.parameter+x,w.cache
    if op == "MP":
        if imp(t,d) == h:
            return Working(d,pair(0,s),d,0) if old else Working(0,s,0,d)
        return Working(0,s,d,0)
    if op == "DROP":
        return Working(h,pair(t,s),d,h)
    if op == "NIP":
        if h == 1:
            return None
        a,b = unpair(s)
        return Working(t,b,d,a)
    raise ValueError(op)

def execute(commands, w, *, old=False):
    for command in commands:
        w = step(command,w,old=old)
        if w is None:
            return None
    return w

def parse_dag(path: Path):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != DAG_SHA:
        raise ValueError("Dag254.v does not match the pinned upstream data")
    nodes={}
    for match in re.finditer(r"\| ([0-9]+) => \((E\w+(?: [0-9]+)?), (E\w+(?: [0-9]+)?)\)",raw.decode()):
        q,left,right=match.groups()
        def edge(s):
            a=s.split()
            return a[0],int(a[1]) if len(a)>1 else None
        nodes[int(q)]=(edge(left),edge(right))
    if set(nodes)!=set(range(219)):
        raise ValueError("unexpected DAG domain")
    if nodes[130] != (("ENode",123),("ENode",166)):
        raise ValueError("unexpected original MP continuation")
    if nodes[197] != (("EDecnz",4),("ENode",191)):
        raise ValueError("unexpected destructive-transfer helper")
    return nodes

class FuelExhausted(RuntimeError): pass

def run_subroutine(nodes,root,registers,fuel=1_000_000):
    """Literal structured RM semantics; every primitive action is counted.

    Break counts zero/left contexts. Continue counts one/right contexts.
    The distinction follows RM.v/Run, rather than treating both uniformly.
    """
    regs=list(registers)
    used=Counter()
    budget=[fuel]
    def call(edge):
        budget[0]-=1
        if budget[0]<0:
            raise FuelExhausted((root,registers))
        kind,r=edge
        used[kind]+=1
        if kind=="EInc":
            regs[r]+=1
            return "normal",0
        if kind=="EDecnz":
            if regs[r]==0:
                return "break",1
            regs[r]-=1
            return "normal",0
        if kind=="EBreak": return "break",r
        if kind=="EContinue": return "continue",r
        if kind=="EHalt": return "halt",0
        if kind!="ENode": raise ValueError(kind)
        left,right=nodes[r]
        while True:
            status,n=call(left)
            if status=="break":
                return ("normal",0) if n==1 else ("break",n-1)
            if status!="normal":
                return status,n
            status,n=call(right)
            if status=="continue":
                if n==1:
                    continue
                return "continue",n-1
            return status,n
    status=call(("ENode",root))
    return status,regs,dict(used),fuel-budget[0]

def verify(dag_path: Path):
    nodes=parse_dag(dag_path)
    changed=dict(nodes)
    changed[130]=(nodes[130][0],("ENode",197))
    result={"status":"PASS","pin":PIN,"Dag254_sha256":DAG_SHA,
            "source_edit":{"node":130,"side":1,"old_target":166,"new_target":197},
            "scope":"Exact finite RM and command checks; no binary or formal theorem"}
    cases=0
    max_actions=0
    # The original and modified actual MP subroutines, including construction
    # and destructive comparison, are checked against distinct exact specs.
    for t in range(5):
      for d in range(5):
       target=imp(t,d)
       for h in sorted({0,target,max(0,target-1),target+1}):
        for s in (0,3,60):
          initial=[7,t,s,11,d,h,0,0,13]
          for source,old in ((nodes,True),(changed,False)):
            status,got,used,actions=run_subroutine(source,150,initial)
            if status != ("normal",0):
                raise AssertionError((status,initial))
            expected_w=step(("MP",0),Working(t,s,d,h),old=old)
            expected=[7,expected_w.top,expected_w.stack,11,expected_w.parameter,expected_w.cache,0,0,13]
            if got!=expected:
                raise AssertionError((old,initial,got,expected))
            max_actions=max(max_actions,actions)
            cases+=1
    result["literal_old_and_changed_MP_cases"]=cases
    result["max_literal_RM_calls"]=max_actions
    transfer_cases=0
    for d in range(16):
      for h in range(8):
        initial=[17,19,23,29,d,h,31,37,41]
        status,got,_,_=run_subroutine(nodes,197,initial)
        expected=initial[:]
        expected[4]=0
        expected[5]=h+d
        assert status==("normal",0) and got==expected
        transfer_cases+=1
    result["literal_transfer197_cases"]=transfer_cases
    # Whole premise arrangement + new inference + cleanup. pa and pab are
    # supplied by the inductive Contract, so this is its exact common tail.
    block_cases=0
    for a in range(12):
      for b in range(12):
       for s in range(25):
        incoming=Working(imp(a,b),pair(a,s),0,0)
        block=[("NIP",0),("DROP",0),("NIP",0),("MP",b),("DROP",0),("NIP",0)]
        got=execute(block,incoming)
        expected=None if a==1 or b==1 else Working(b,s,0,0)
        assert got==expected,(a,b,s,got,expected)
        block_cases+=1
    result["full_MP_contract_tail_cases"]=block_cases
    repair_cases=0
    rng=random.Random(252251)
    for b in [*range(128),1<<63,(1<<127)-1,1<<1024,1<<4096]:
      for s in [0,1,3,60,65535,*[rng.getrandbits(192) for _ in range(3)]]:
        start=Working(0,s,0,b)
        repair=[("DROP",b),("DROP",0),("MP",0),("NIP",0),("DROP",0),("NIP",0)]
        got=execute(repair,start)
        expected=None if b==1 else Working(b,pair(0,s),b,0)
        assert got==expected,(b,s,got,expected)
        repair_cases+=1
    result["six_command_exact_repair_cases"]=repair_cases
    # Both MP branches use the expected arithmetic and leave the source
    # candidate pointer and next-candidate register untouched (covered above).
    result["observed_largest_formula_parameter_bitlength"]=4097
    result["notes"]=[
        "Stack60 and stack1 are deliberately allowed in local algebra tests; no sound-seed assertion is made for them.",
        "Full-calculus soundness and completeness are ordinary proofs in the companion manuscript, not inferred from samples.",
        "The binary 204/read1 edit and affine certificates are supplied separately by the machine-construction lane."
    ]
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dag",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    result=verify(args.dag)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))

if __name__=="__main__": main()
