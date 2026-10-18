#!/usr/bin/env python3
"""Auditable FC13B membership elimination and Boolean truth/constant fusion.

This is a finite equational payload, not a compiled binary Turing machine.
The logical model/proof transformations are documented in NOTES.md.
"""
from __future__ import annotations
import argparse
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import sys

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'reference'))
from equational_search import Kernel, freeze, nodes, variables
from build_equations import encode_packet, decode_packet, pretty, canonical_equation

D=('d',)
TOP=('top',)
ONE=('I',D,D)

def inc_definition(x,y):
    return ('p_Inc',('C',('C',D,D,x),ONE,y),('A',D,ONE))

def map_term(t,eliminate=False,fuse=False):
    if isinstance(t,str):
        return t
    args=tuple(map_term(c,eliminate,fuse) for c in t[1:])
    if eliminate and t[0]=='p_E':
        return inc_definition(*args)
    if fuse and t[0]=='top':
        return D
    return (t[0],)+args


def compile_variant(source,eliminate=False,fuse=False):
    eqs=[]
    for i,eq in enumerate(source['equations']):
        # Original equation 19 is the explicit congruence for p_E.  The
        # replacement is a term over symbols whose congruence is retained.
        if eliminate and i==19:
            continue
        eqs.append(tuple(map_term(t,eliminate,fuse) for t in eq))
    sig={s:a for s,a in source['signature'].items()
         if not(eliminate and s=='p_E') and not(fuse and s=='top')}
    start=map_term(freeze(source['start']),eliminate,fuse)
    target=map_term(freeze(source['target']),eliminate,fuse)
    Kernel(sig,eqs,start,target)
    bits,stats=encode_packet(eqs,sig,start,target)
    expected=(sig,[canonical_equation(e) for e in eqs],start,target)
    assert decode_packet(bits,list(sig))==expected
    stats['input_equations']=len(source['equations'])
    stats['eliminated_membership_predicate']=eliminate
    stats['fused_truth_constant']=fuse
    stats['packet_sha256']=sha256((bits+'\n').encode()).hexdigest()
    stats['term_opcodes']=dict(sorted(Counter(symbol(t) for e in eqs for root in e for t in walk(root)).items()))
    data={'name':f'FC13B_Efree{int(eliminate)}_truth_fused{int(fuse)}',
          'signature':sig,'equations':eqs,'start':start,'target':target,
          'status':'complete equational packet; ordinary equiconsistency proof; no binary TM state count'}
    return data,bits,stats


def walk(t):
    yield t
    if not isinstance(t,str):
        for c in t[1:]:
            yield from walk(c)

def symbol(t):
    return '$var' if isinstance(t,str) else t[0]


def build(out=ROOT/'output'):
    out.mkdir(parents=True,exist_ok=True)
    src=freeze(json.loads((ROOT/'reference/grouped.json').read_text()))
    all_stats={}
    for name,eliminate,fuse in [('baseline',False,False),('membership_eliminated',True,False),('truth_fused',False,True),('combined',True,True)]:
        data,bits,stats=compile_variant(src,eliminate,fuse)
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
        (out/(name+'.bits')).write_text(bits+'\n')
        (out/(name+'.equations')).write_text('\n'.join(f'{i}: {pretty(a)} = {pretty(b)}' for i,(a,b) in enumerate(data['equations']))+'\n')
        all_stats[name]=stats
    assert all_stats['baseline']['complete_packet_bits']==2324
    assert all_stats['combined']['opcode_width']==4
    (out/'metrics.json').write_text(json.dumps(all_stats,indent=2)+'\n')
    return all_stats

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=ROOT/'output')
    args=p.parse_args()
    print(json.dumps(build(args.output),indent=2))
