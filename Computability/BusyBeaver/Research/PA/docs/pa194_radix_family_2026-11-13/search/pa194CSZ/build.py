#!/usr/bin/env python3
"""Compose the symmetric cached guard with the invariant-backed zero-register jump.
PA194CSZ: 194 working states, two symbols, blank two-way tape.
This is an ordinary proof certificate, not a new proof-assistant endpoint.
"""
from pathlib import Path
import hashlib,json,time
from collections import deque
import compiler as c
import baseline_tools as b
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'machine'
def sha(data):return hashlib.sha256(data).hexdigest()
def js(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')
def successors(code,pc,mask):
    z=code[pc]
    if z[0]=='jump':return [(z[1],mask)]
    if z[0]=='inc':return [(z[2],mask|(1<<z[1]))]
    if z[0]=='dec':
        bit=1<<z[1]
        return [(z[3],mask&~bit),(z[3],mask)] if mask&bit else [(z[2],mask)]
    assert z[0]=='halt'
    return []
def closure(code):
    seen=bytearray(len(code)*512);seen[25*512+1]=1
    todo=deque([25*512+1])
    while todo:
        pc,m=divmod(todo.popleft(),512)
        for p,n in successors(code,pc,m):
            assert 0<=p<len(code) and 0<=n<512
            ix=p*512+n
            if not seen[ix]:seen[ix]=1;todo.append(ix)
    return seen

def main():
    assert __debug__
    started=time.monotonic();OUT.mkdir(exist_ok=True)
    original=c.raw_nodes
    def nodes():
        ns=original();ns['node163']=('node6','node147')
        ns['node170']=(('node36',('node167','node145')),'node56')
        ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
        assert ns['node22']==(('leaf','dec',8),('leaf','breakTo',1))
        ns['node22']=(('leaf','dec',8),('leaf','dec',6))
        return ns
    c.raw_nodes=nodes
    inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    assert sha((ROOT/'inputs/pa194CS.native.tm').read_bytes())=='00446d08d3c35909a11460a9e19507d53e8526ad822b94ce9a04c73951eb447b'
    parent=b.read_table(ROOT/'inputs/pa194CS.native.tm')
    assert parent[27,1]==(0,False,40)
    child=dict(parent);child[27,1]=(1,True,21)
    t=c.read_grammar(ROOT/'inputs/pa194.grammar.json');sites,ins,cs=c.source(t)
    assert len(sites)==3646 and len(cs)==4746
    old=json.loads((ROOT/'inputs/pa194CS.instructions.json').read_text())
    new=json.loads(json.dumps(ins))
    assert [i for i,(a,z) in enumerate(zip(old,new)) if a!=z]==[26]
    assert old[26]==['jump',34] and new[26]==['dec',6,34,27]
    old_sites=json.loads((ROOT/'inputs/pa194CS.sites.json').read_text())
    new_sites=[[''.join(map(str,p)),op,a]for p,op,a in sites]
    assert [i for i,(a,z) in enumerate(zip(old_sites,new_sites)) if a!=z]==[26]
    assert new_sites[26]==[old_sites[26][0],'dec',6]
    r0,r1=closure(old),closure(new)
    assert r0==r1
    count=sum(r0);masks=[]
    for ix,yes in enumerate(r0):
        if not yes:continue
        pc,m=divmod(ix,512)
        assert successors(old,pc,m)==successors(new,pc,m)
        assert all(r0[p*512+n] for p,n in successors(new,pc,m))
        if pc==26:masks.append(m)
    assert r0[25*512+1] and masks and all(m&64==0 for m in masks)
    invariant={'pairs':count,'contains_seed':True,'closed':True,'old_new_successors_equal_on_invariant':True,
      'site26_masks':masks,'register6_zero_at26':True,'encoding':'bytearray of length3646*512, index512*pc+mask',
      'storage':'positivity_invariant.hex','storage_encoding':'Text lines: source-site decimal, then 128 hex digits; bit m records (site,m). Hash below binds the decoded 3646*512 bytes with index 512*site+mask.',
      'sha256':sha(r0),'source_seed':[25,[2,0,0,0,0,0,0,0,0]]}
    print('positivity PASS',invariant,flush=True)
    runtime=c.validate(child,cs);assert runtime['ok'],runtime
    seed=b.startup(child,sites[25][0])
    dense,labels=b.dense_table(child,194)
    native=b.table_text(child).encode();dense_bytes=b.table_text(dense).encode()
    (OUT/'pa194CSZ.native.tm').write_bytes(native)
    (OUT/'pa194CSZ.tm').write_bytes(dense_bytes)
    js(OUT/'pa194CSZ.labels.json',labels);js(OUT/'pa194CSZ.sites.json',new_sites)
    js(OUT/'pa194CSZ.instructions.json',ins)
    encoded = ''.join(f'{pc} {sum(r0[512*pc+m] << m for m in range(512)):0128x}\n' for pc in range(len(ins)))
    (OUT/'positivity_invariant.hex').write_text(encoded)
    js(OUT/'positivity_invariant.json',invariant)
    receipt={'family':'PA194CSZ','working_states':194,'transition_rows':388,'source_sites':3646,
      'source_contracts':4746,'source_edit':[26,old[26],new[26]],
      'native_edit':[[27,1],parent[27,1],child[27,1]],'positivity_invariant':invariant,
      'symbolic_validation':runtime,'startup':seed,'native_sha256':sha(native),'dense_sha256':sha(dense_bytes),
      'seconds':time.monotonic()-started,'kernel_checked':False}
    js(OUT/'construction_receipt_csz.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
