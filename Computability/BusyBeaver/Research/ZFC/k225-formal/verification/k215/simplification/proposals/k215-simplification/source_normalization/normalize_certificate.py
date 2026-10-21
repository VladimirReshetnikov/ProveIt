#!/usr/bin/env python3
"""Generate/recheck a consumed-leaf-normalized K215 source certificate.

Data has ordinary all-register mathematical meaning. This script is not a
proof-assistant kernel check. It deliberately does not replace upstream files.
"""
from __future__ import annotations
import collections, hashlib, json
from pathlib import Path
from graph_compress import BASE, dag_leaves, effects, mod

if not __debug__:
    raise SystemExit('Run this generator without Python -O; its validation uses assertions.')

def trim(p):
    while p and not p[-1]: p=p[:-1]
    return p

def nseg(tree,p):
    s=mod.seg(tree,p)
    if s is None: raise ValueError('failed segment')
    increments,end=s
    (op,r),leaf=tree.tsite(end)
    assert op in ('EDecnz','EHalt')
    assert tree.tsite(leaf)==tree.tsite(end)
    assert trim(end)==trim(leaf), 'a segment endpoint has live bits after its consumed leaf'
    return increments,trim(end)

def generate(t1,t2):
    index={}; entries=[]; queue=collections.deque()
    def target(a,b):
        xs,p=nseg(t1,a); ys,q=nseg(t2,b)
        if effects(xs)!=effects(ys): raise ValueError('effects differ')
        key=p,q
        if key not in index:
            index[key]=len(entries); entries.append([p,q,None,None]);queue.append(key)
        return index[key]
    root=target((),()); assert root==0
    while queue:
        p,q=queue.popleft(); i=index[p,q]
        (op,r),p1=t1.tsite(p);(oq,s),q1=t2.tsite(q)
        assert trim(p1)==p and trim(q1)==q
        if op==oq=='EHalt':entries[i][2:]=[0,0]
        else:
            assert op==oq=='EDecnz' and r==s
            entries[i][2]=target(mod.inc_path(p1),mod.inc_path(q1))
            entries[i][3]=target(mod.brk(1,p1),mod.brk(1,q1))
    return entries

def validate(t1,t2,entries):
    """Check serialized certificate by local obligations, without discovering pairs."""
    def branch(a,b,j):
        assert 0<=j<len(entries)
        xs,p=nseg(t1,a);ys,q=nseg(t2,b)
        assert effects(xs)==effects(ys)
        assert (p,q)==tuple(entries[j][:2])
    branch((),(),0)
    dec=halt=0
    for p,q,j,k in entries:
        (op,r),pp=t1.tsite(p);(oq,s),qq=t2.tsite(q)
        assert trim(pp)==p and trim(qq)==q
        if op==oq=='EHalt':halt+=1
        else:
            assert op==oq=='EDecnz' and r==s
            branch(mod.inc_path(pp),mod.inc_path(qq),j)
            branch(mod.brk(1,pp),mod.brk(1,qq),k)
            dec+=1
    return {'decrement_entries':dec,'halt_entries':halt,'entry_obligations':len(entries),'branch_obligations':1+2*dec}

def code(p):
    n=1
    for b in p:n=2*n+int(b)
    return n

def main():
    source=BASE/'upstream/sites215.json';dag=BASE/'upstream/dagperm_nodes.json'
    t1=mod.Tree(mod.load(source));t2=mod.Tree(dag_leaves(json.loads(dag.read_text())))
    old=mod.generate(t1,t2); cert=generate(t1,t2)
    newidx={(p,q):i for i,(p,q,*_) in enumerate(cert)}
    oldmap=[newidx[trim(p),trim(q)] for p,q,*_ in old]
    for i,(p,q,z,j,k) in enumerate(old):
        assert z==0
        assert cert[oldmap[i]][2:]==[oldmap[j],oldmap[k]]
    assert set(oldmap)==set(range(len(cert)))
    wire={'schema':'K215-normalized-source-bisim-v1','source_commit':'b6c7087477e51c017003bd729e712c8969733223','inputs':{source.name:hashlib.sha256(source.read_bytes()).hexdigest(),dag.name:hashlib.sha256(dag.read_bytes()).hexdigest()},'entries':[[str(code(p)),str(code(q)),j,k] for p,q,j,k in cert]}
    out=BASE/'normalized_certificate.json';out.write_text(json.dumps(wire,separators=(',',':'))+'\n')
    # Round-trip from decimal integers; leading 1 is the sentinel, not a path bit.
    d=json.loads(out.read_text())
    dec=lambda s:tuple(x=='1' for x in bin(int(s))[3:])
    decoded=[(dec(p),dec(q),j,k) for p,q,j,k in d['entries']]
    stats=validate(t1,t2,decoded)
    (BASE/'old_to_normalized.json').write_text(json.dumps(oldmap,separators=(',',':'))+'\n')
    stats.update(original_entries=len(old),normalized_entries=len(cert),removed_entries=len(old)-len(cert),percentage_removed=100*(len(old)-len(cert))/len(old),certificate_bytes=out.stat().st_size,original_max_path_bits=max(max(len(p),len(q)) for p,q,*_ in old),normalized_max_path_bits=max(max(len(p),len(q)) for p,q,*_ in cert),offsets='all zero',surjective_map_preserves_both_successors=True,kernel_checked=False,kernel_status_scope="This Python producer performs no kernel checking. Consult kernel_receipt.json for the separately executed Lean result.")
    (BASE/'normalized_summary.json').write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))

if __name__=='__main__':main()
