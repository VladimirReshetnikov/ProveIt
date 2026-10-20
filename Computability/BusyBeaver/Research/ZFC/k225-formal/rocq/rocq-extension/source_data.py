"""Deterministic untrusted serializers; all emitted proof claims are checked in Rocq."""
from pathlib import Path
import hashlib
import json
import re
import shutil

RUNTIME = ["Table230", "TM230", "Zip", "Boot230", "Runtime230Core",
           "Tape230Blocks", "Tape230Carry", "Interpreter230Sites",
           "Interpreter230Check", "Sim230", "Sim230Main"]
DELETED = {79, 140, 175}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def parse(p):
    out = {}
    for line in p.read_text().splitlines():
        if line and not line.startswith("#"):
            q,b,w,d,n = line.split()
            assert (int(q),int(b)) not in out
            out[int(q),int(b)] = int(w),d,int(n)
    return out


def table_text(table, n, name, source):
    rows=[]
    for q in range(n):
        w,d,z=table[q,0];v,e,y=table[q,1]
        rows.append(f"  ({str(bool(w)).lower()}, {d}, {z}, {str(bool(v)).lower()}, {e}, {y})")
    return (f"(** Exact table data from {source.name}; SHA256 {sha(source)}. *)\n"
            "From Coq Require Import List.\nFrom BusyCoq Require Import TM.\n"
            "Import ListNotations.\n"
            f"Definition {name} : list (bool * dir * nat * bool * dir * nat) := [\n"
            + ";\n".join(rows) + "\n].\n")


def program_text(sites):
    leaves={p:(op,arg) for p,op,arg in sites}
    assert len(leaves)==len(sites)
    prefixes={p[:i] for p in leaves for i in range(len(p))}
    assert not(set(leaves)&prefixes)
    memo={};nodes=[];H=[];B=[];C=[]
    def rec(p):
        if p in leaves:
            op,arg=leaves[p]
            if op=='CH':return ('CH',None)
            assert op in ('CI','CD','CB','CC')
            return op,arg
        assert p in prefixes
        a,b=rec(p+'0'),rec(p+'1');key=a,b
        if key not in memo:
            def metrics(e):
                op,x=e
                if op=='CN':return H[x],B[x],C[x]
                return 0,(1 if op=='CD' else x if op=='CB' else 0),(x if op=='CC' else 0)
            ha,ba,ca=metrics(a);hb,bb,cb=metrics(b)
            memo[key]=len(nodes);nodes.append(key)
            H.append(1+max(ha,hb));B.append(max(max(ba-1,0),bb));C.append(max(ca,max(cb-1,0)))
        return 'CN',memo[key]
    root=rec('');assert root[0]=='CN';root=root[1]
    assert B[root]==C[root]==0
    def edge(e):return e[0] if e[1] is None else f'{e[0]} {e[1]}'
    body=("From Coq Require Import Lists.List NArith.\n"
          "From K230 Require Import RM RMEquiv Prog230.\nImport ListNotations.\n\n"
          "Definition p227_tab : list (cedge * cedge) := [\n"
          +';\n'.join(f'  ({edge(a)}, {edge(b)})' for a,b in nodes)+"\n].\n\n"
          "Definition p227 : prog := {|\n"
          "  nodes := fun n => let '(a,b) := nth n p227_tab (CH,CH) in (cv a,cv b);\n"
          f"  root := {root}; nnodes := {len(nodes)}\n|}}.\n")
    for label,values in [('H',H),('B',B),('C',C)]:
        body+=f"Definition p227_{label} : list nat := ["+';'.join(map(str,values))+"].\n"
    body+=("Lemma p227_wf : wf p227.\n"
           "Proof. apply (wf_check_with_sound p227 p227_H p227_B p227_C). vm_compute. reflexivity. Qed.\n")
    return body,{'distinct_nodes':len(nodes),'root':root,'leaf_occurrences':len(sites),'depth':H[root]}

