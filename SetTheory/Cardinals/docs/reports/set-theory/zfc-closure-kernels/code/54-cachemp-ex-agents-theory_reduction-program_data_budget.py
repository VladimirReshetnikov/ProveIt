#!/usr/bin/env python3
"""Lossless program-data measurements; no TM-state estimate is asserted.

The only state bounds below concern a precisely restricted fixed-block
introspective-writer family with b bits in one next-state target per payload
state, and a chain/ring decoding targets by their zero-based position.
No writer or bytecode interpreter has been compiled by this script.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import re

SHA="538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3"
MACROS=[166,121,168,171,177,119,181,182,180,218,178,183,176,158,208,192,131,211,197]

def gamma(n):
    if n<1: raise ValueError(n)
    s=bin(n)[2:]
    return "0"*(len(s)-1)+s

def width(n):
    return max(1,(n-1).bit_length())

def parse(path):
    data=path.read_bytes()
    if hashlib.sha256(data).hexdigest()!=SHA:
        raise ValueError("pinned Dag254.v hash differs")
    nodes={}
    for m in re.finditer(r"\| ([0-9]+) => \((E\w+(?: [0-9]+)?), (E\w+(?: [0-9]+)?)\)",data.decode()):
        q,l,r=m.groups()
        nodes[int(q)]=(l,r)
    assert len(nodes)==219
    return nodes

def full_prefix(nodes):
    alphabet=[f"EInc {i}" for i in range(9)]+[f"EDecnz {i}" for i in range(9)]
    alphabet += [f"EBreak {i}" for i in range(1,4)]+[f"EContinue {i}" for i in range(1,4)]+["EHalt"]
    pool={e:i for i,e in enumerate(alphabet)}
    parts=[]
    originals=[]
    def emit(e):
        if e in pool:
            parts.append("1"+format(pool[e],f"0{width(len(pool))}b"))
            return
        assert e.startswith("ENode ")
        parts.append("0")
        q=int(e.split()[1])
        left,right=nodes[q]
        emit(left);emit(right)
        pool[e]=len(pool)
        originals.append(e)
    emit("ENode 0")
    bits="".join(parts)
    decoded=list(alphabet)
    pos=0
    definitions=[]
    def read():
        nonlocal pos
        bit=bits[pos];pos+=1
        if bit=="1":
            w=width(len(decoded));i=int(bits[pos:pos+w],2);pos+=w
            if i>=len(decoded):raise ValueError("bad reference")
            return i
        a,b=read(),read()
        i=len(decoded)
        decoded.append((a,b));definitions.append((a,b))
        return i
    root=read()
    assert pos==len(bits) and len(definitions)==219
    # Compare every decoded definition with both actual source edges. This
    # establishes exact root-tree reconstruction without numeric fingerprints.
    for j,e in enumerate(originals):
        q=int(e.split()[1]);expected=tuple(pool[z] for z in nodes[q])
        assert decoded[len(alphabet)+j]==expected
    assert root==pool["ENode 0"]
    return bits,{"definitions":219,"terminal_alphabet":len(alphabet),"roundtrip_exact":True}

def ax_word(nodes):
    def expand(q):
        if q in MACROS:return [MACROS.index(q)]
        out=[]
        for e in nodes[q]:
            if not e.startswith("ENode "):raise ValueError((q,e))
            out.extend(expand(int(e.split()[1])))
        return out
    w=expand(1)
    assert len(w)==186
    return w

def disjoint_count(word,pair):
    i=n=0
    while i+1<len(word):
        if (word[i],word[i+1])==pair:n+=1;i+=2
        else:i+=1
    return n

def repair(word,seed):
    rng=random.Random(seed)
    word=list(word);rules=[]
    while True:
        pairs=sorted(set(zip(word,word[1:])))
        scored=[(p,disjoint_count(word,p)) for p in pairs]
        scored=[(p,n) for p,n in scored if n>=2]
        if not scored:break
        p=rng.choices([p for p,n in scored],[n**4 for p,n in scored],k=1)[0]
        new=[];i=0
        while i<len(word):
            if i+1<len(word) and (word[i],word[i+1])==p:
                new.append(len(MACROS)+len(rules));i+=2
            else:new.append(word[i]);i+=1
        rules.append(p);word=new
    return rules,word

def encode_grammar(rules,word):
    parts=[gamma(len(rules)+1)]
    for j,p in enumerate(rules):
        w=width(len(MACROS)+j)
        parts.extend(format(i,f"0{w}b") for i in p)
    parts.append(gamma(len(word)+1))
    w=width(len(MACROS)+len(rules))
    parts.extend(format(i,f"0{w}b") for i in word)
    return "".join(parts)

def decode_grammar(bits):
    pos=0
    def rgamma():
        nonlocal pos
        n=0
        while bits[pos]=="0":n+=1;pos+=1
        r=int(bits[pos:pos+n+1],2);pos+=n+1
        return r
    def rnum(n):
        nonlocal pos
        w=width(n);i=int(bits[pos:pos+w],2);pos+=w
        if i>=n:raise ValueError("bad grammar reference")
        return i
    m=rgamma()-1;rules=[]
    for j in range(m):rules.append((rnum(len(MACROS)+j),rnum(len(MACROS)+j)))
    n=rgamma()-1
    word=[rnum(len(MACROS)+m) for _ in range(n)]
    assert pos==len(bits)
    return rules,word

def expand_grammar(rules,word):
    meanings=[[i] for i in range(len(MACROS))]
    for a,b in rules:meanings.append(meanings[a]+meanings[b])
    return [x for i in word for x in meanings[i]]

def fixed_block_budget(bits):
    rows=[]
    for b in range(1,13):
        digits=[int(bits[i:i+b].ljust(b,"0"),2) for i in range(0,len(bits),b)]
        n=max(len(digits),max(digits)+1)
        rows.append({"bits_per_payload_target":b,"payload_states_needed":len(digits),
                     "largest_literal_target_rank":max(digits),
                     "required_states_at_least":n})
    return min(rows,key=lambda r:r["required_states_at_least"])

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dag",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    ap.add_argument("--seeds",type=int,default=512)
    args=ap.parse_args()
    nodes=parse(args.dag)
    full,metadata=full_prefix(nodes)
    word=ax_word(nodes)
    best=None
    for seed in range(args.seeds):
        rules,residual=repair(word,seed)
        bits=encode_grammar(rules,residual)
        decoded_rules,decoded_word=decode_grammar(bits)
        assert decoded_rules==rules and decoded_word==residual
        assert expand_grammar(decoded_rules,decoded_word)==word
        item=(len(bits),seed,rules,residual,bits)
        if best is None or item[:2]<best[:2]:best=item
    size,seed,rules,residual,axb=best
    args.output.parent.mkdir(parents=True,exist_ok=True)
    (args.output.parent/"dag219-prefix.bits").write_text(full+"\n")
    (args.output.parent/"axioms186-grammar.bits").write_text(axb+"\n")
    record={"status":"PASS","source_sha256":SHA,
      "scope":"Lossless encodings and a restricted-writer necessary state budget; no compiled writer/interpreter/TM",
      "full_DAG":{"bits":len(full),**metadata,"restricted_fixed_block_writer":fixed_block_budget(full)},
      "AX_raw":{"macro_calls":len(word),"alphabet_size":len(MACROS),"bits_including_gamma_length":len(gamma(len(word)+1))+len(word)*width(len(MACROS))},
      "AX_best_sampled_grammar":{"bits":size,"seed":seed,"seeds_tested":args.seeds,"productions":len(rules),"main_tokens":len(residual),"roundtrip_exact":True,"rules":rules,"main":residual,"restricted_fixed_block_writer":fixed_block_budget(axb)},
      "limitations":["No general lower bound for Turing machines or arbitrary introspective encodings.","Both read/write directions and chain transitions are fixed in the restricted writer family; only the other successor target carries payload.","The writer bound is for the actual literal block values (unused top ranks are not charged), fixed bit order and zero padding; other orders, digit recodings, and role sharing are outside this bound.","Interpreter, integer-to-bit decoder, read-only tape access, dispatch, unary register engine, frame/bootstrap and calibration remain unpriced.","AX-only decoding assumes all19macro implementations remain available and does not make their costs disappear."]}
    args.output.write_text(json.dumps(record,indent=2)+"\n")
    print(json.dumps({k:v for k,v in record.items() if k!="AX_best_sampled_grammar"},indent=2))
    print(json.dumps({k:v for k,v in record["AX_best_sampled_grammar"].items() if k not in ("rules","main")},indent=2))

if __name__=="__main__":main()
