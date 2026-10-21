#!/usr/bin/env python3
"""Reconstruct the counter-salt source using only the bundled K219 source.

The generated source is mathematically calibrated in the report.  Source
DAG counts are not literal Turing-machine state counts.  The uncorrected
all-asymmetric source is constructed only to reproduce the negative result.
"""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PINNED_INPUT_SHA256 = '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
PINNED_OUTPUT_SHA256 = 'dc32510df9ffb07c2e106d835f735baff4a19989198a7f5bfec3f34e0046559d'
D = lambda i: ('CD', i)
I = lambda i: ('CI', i)
C = lambda i: ('CC', i)
B = lambda i: ('CB', i)
F = lambda a,b: (D(a),(I(b),C(2)))
P = (D(6),C(2))
U = (P,B(1))
Z = (D(5),C(1))
K219_EQ = (((D(5),U),D(6)),(Z,U))
ASYMMETRIC = ((D(5),(P,(I(6),Z))),(D(6),B(1)))
CLEAR6 = (D(6),C(1))
LOCAL_REPAIR_PATH = '11101001001110111101'

def leaf(n): return isinstance(n[0],str)

def tree(rows):
    leaves = {p:(op,k) for p,op,k in rows}
    assert len(leaves)==len(rows)
    prefixes = {p[:i] for p in leaves for i in range(len(p)+1)}
    def go(p):
        if p in leaves:
            assert p+'0' not in prefixes and p+'1' not in prefixes
            return leaves[p]
        assert p+'0' in prefixes and p+'1' in prefixes, p
        return go(p+'0'),go(p+'1')
    return go('')

def sites(t):
    rows=[]
    def go(n,p):
        if leaf(n):rows.append([p,n[0],n[1]])
        else:go(n[0],p+'0');go(n[1],p+'1')
    go(t,'')
    return rows

def subtree(t,p):
    for c in p:t=t[int(c)]
    return t

def replace(t,p,n):
    if not p:return n
    k=int(p[0]);children=list(t);children[k]=replace(children[k],p[1:],n)
    return tuple(children)

def metrics(t):
    nodes=set()
    def go(n):
        if n in nodes:return
        nodes.add(n)
        if not leaf(n):go(n[0]);go(n[1])
    go(t);rows=sites(t)
    return {'dag_nodes':len(nodes),'internal_dag_nodes':sum(not leaf(n)for n in nodes),
            'primitive_kinds':sum(leaf(n)for n in nodes),'leaf_occurrences':len(rows),
            'maximum_depth':max(len(p)for p,_,_ in rows),
            'maximum_zero_run':max(len(z)for p,_,_ in rows for z in p.split('1'))}

def source_bytes(t):return (json.dumps(sites(t),separators=(',',':'))+'\n').encode()

def reconstruct(output_dir):
    output_dir=Path(output_dir);output_dir.mkdir(parents=True,exist_ok=True)
    raw=(ROOT/'inputs/k219.sites.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==PINNED_INPUT_SHA256
    old=tree(json.loads(raw));matches=[]
    def rewrite(n,p=''):
        if n==K219_EQ:matches.append(p);return ASYMMETRIC
        if leaf(n):return n
        return rewrite(n[0],p+'0'),rewrite(n[1],p+'1')
    weak=rewrite(old)
    assert matches==['111010010011101111000','11101001001110111110',
                     '1110100101100','111110'],matches
    node=subtree(weak,LOCAL_REPAIR_PATH)
    assert node==(F(7,6),F(4,5))
    variants=[];selected=None
    for local_association in range(2):
        local=(CLEAR6,node) if local_association==0 else ((CLEAR6,node[0]),node[1])
        t=replace(weak,LOCAL_REPAIR_PATH,local)
        for root_association in range(2):
            variant=(F(6,4),t) if root_association==0 else ((F(6,4),t[0]),t[1])
            measured=metrics(variant)
            assert measured['dag_nodes']==208 and measured['leaf_occurrences']==4741
            assert measured['maximum_zero_run']==6
            encoded=source_bytes(variant)
            variants.append({'local_association':local_association,'root_association':root_association,
                             **measured,'sha256':hashlib.sha256(encoded).hexdigest()})
            if (local_association,root_association)==(0,1):selected=encoded
    assert hashlib.sha256(selected).hexdigest()==PINNED_OUTPUT_SHA256
    assert selected==(ROOT/'sources/counter_salt_208.sites.json').read_bytes()
    (output_dir/'counter_salt_208.sites.json').write_bytes(selected)
    receipt={'status':'PASS_SOURCE_RECONSTRUCTION','input_sha256':PINNED_INPUT_SHA256,
             'output_sha256':PINNED_OUTPUT_SHA256,'equality_replacement_paths':matches,
             'local_repair_path':LOCAL_REPAIR_PATH,'baseline':metrics(old),
             'unsafe_all_asymmetric':metrics(weak),'repaired_associations':variants,
             'selected_association':[0,1],
             'scope':'Exact AST reconstruction and source metrics, not a binary TM runtime proof. The 205-node uncorrected variant fails the freshness gate.'}
    (output_dir/'source_reconstruction.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,required=True)
    print(json.dumps(reconstruct(parser.parse_args().output_dir),indent=2))
