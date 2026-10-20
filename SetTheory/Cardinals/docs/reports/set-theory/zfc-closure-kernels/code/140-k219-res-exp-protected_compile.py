#!/usr/bin/env python3
"""Exploratory incremental compiler with protected arithmetic helper states.

The 82 protected states were observed outside complete decoder passes in
all 6167 baseline primitive frames.  Preserving them fixes a known unsafe
optimization in the predecessor exploratory compiler; this is not a new
proof of runtime and every output still needs the full runtime checker.
"""
from pathlib import Path
from collections import Counter
import json
import additive_binder as z

PROTECTED=set(json.loads((Path(__file__).resolve().parent/'receipts/engine_protected.json').read_text())['states'])

def compile_tree(table,old_src,new_src):
    s,b=z.s,z.b
    groups,paths=b.decoder_map(table,old_src)
    node_state={n:q for q,ns in groups.items()for n in ns}
    live=set()
    def visit(n):
        if s.leaf(n)or n in live:return
        live.add(n);visit(n[0]);visit(n[1])
    visit(new_src)
    origins={}
    def walk(n,o):
        if s.leaf(n)or o is None or s.leaf(o):return
        if n!=o:origins.setdefault(n,o)
        walk(n[0],o[0]);walk(n[1],o[1])
    walk(new_src,old_src)
    origins={n:o for n,o in origins.items()if o not in live}
    compiled=dict(table);mapped=dict(node_state);mapped[new_src]=84
    claimed={84:new_src};fresh=max(300,max(q for q,bit in table)+1);startfresh=fresh;reused=0
    leaves={}
    for op in ['CI','CD','CC','CB','CH']:
        for arg in ([None]if op=='CH'else range(10)):
            ch=(op,arg)
            for bit in(0,1):
                choices=Counter(table[q,bit]for n,q in node_state.items()if n[bit]==ch)
                direct=[a for a in choices if a[:2]==(bit,1)]
                if len(direct)==1:leaves[ch,bit]=direct[0]
                elif ch==('CC',1)and bit==1:leaves[ch,bit]=(0,-1,1)
                elif ch==('CC',2)and bit==1:leaves[ch,bit]=(0,-1,16)
                elif ch==('CB',1)and bit==1:leaves[ch,bit]=(0,-1,40)
    def go(n):
        nonlocal fresh,reused
        if n in mapped:return mapped[n]
        oq=node_state.get(origins.get(n))
        if oq is not None and len(groups[oq])==1 and oq not in claimed and oq not in PROTECTED:
            q=oq;reused+=1
        else:q=fresh;fresh+=1
        mapped[n]=q;claimed[q]=n
        for bit,ch in enumerate(n):
            if not s.leaf(ch):compiled[q,bit]=(bit,1,go(ch))
            elif oq is not None and origins[n][bit]==ch:
                compiled[q,bit]=table[oq,bit]
            elif(ch,bit)in leaves:compiled[q,bit]=leaves[ch,bit]
            else:raise ValueError(('no leaf action',ch,bit,q))
        return q
    for bit,ch in enumerate(new_src):compiled[84,bit]=(bit,1,go(ch))if not s.leaf(ch)else leaves[ch,bit]
    assert all(compiled[q,bit]==table[q,bit]for q in PROTECTED for bit in(0,1))
    todo=[0];reach={0}
    for q in todo:
        for bit in(0,1):
            dest=compiled[q,bit][2]
            if dest!=254 and dest not in reach:reach.add(dest);todo.append(dest)
    compiled={k:v for k,v in compiled.items()if k[0]in reach}
    gg,pp=b.decoder_map(compiled,new_src)
    for q,ns in gg.items():
        for n in ns:
            if mapped.get(n)!=q:raise ValueError(('node binding mismatch',q,mapped.get(n)))
    return compiled,dict(working_states=len(compiled)//2,fresh=fresh-startfresh,reused=reused,
                        protected_states=len(PROTECTED),aliases=sum(len(ns)-1 for ns in gg.values()),
                        decoder_states=len(gg),interior_nodes=sum(len(ns)for ns in gg.values()))

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('sites',type=Path);p.add_argument('out',type=Path);a=p.parse_args()
    tree=z.s.tree(json.loads(a.sites.read_text()));table,receipt=compile_tree(z.T,z.TREE,tree)
    a.out.mkdir(parents=True,exist_ok=True)
    (a.out/'candidate.tm').write_bytes(z.b.table_bytes(table));(a.out/'sites.json').write_bytes(z.s.compact(z.s.sites(tree)))
    (a.out/'compile.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
