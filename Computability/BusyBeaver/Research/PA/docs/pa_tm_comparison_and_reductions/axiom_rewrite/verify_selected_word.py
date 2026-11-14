#!/usr/bin/env python3
"""Independently check the selected 199-token AX word against its formulas.

Requires only the standard library and distributed_gate.py in this directory.
This verifies mathematical emission and exact token counts, not physical routing.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json
import re
import distributed_gate as d

NAMES = {'node49':'P','node55':'D','node58':'H','node65':'C','node70':'A',
         'node72':'rH','node75':'rDC','node142':'gc','node150':'gt'}

def short(token):
    if isinstance(token,str):
        d.require(token in NAMES,'Unexpected named macro: '+token)
        return NAMES[token]
    d.require(token in [['leaf','inc',1],['leaf','breakTo',1]],
              'Unexpected primitive macro')
    return 'i' if token[1]=='inc' else 'J'

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).resolve().parent
    ap.add_argument('--source',type=Path,default=here/'inputs/BusyBeaver')
    ap.add_argument('--word',type=Path,default=here/'selected_word.json')
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    program=(args.source/'PA196/Program.lean').read_bytes()
    blocks_file=(args.source/'PA196/Source/AXProgram.lean').read_bytes()
    d.require(hashlib.sha256(program).hexdigest()==d.PROGRAM_HASH,'Program pin mismatch')
    d.require(hashlib.sha256(blocks_file).hexdigest()==d.AX_HASH,'AX source pin mismatch')
    sizes=d.expanded_counts(program.decode())
    block_text=blocks_file.decode().split('def blocks :',1)[1].split('def program :',1)[0]
    blocks=[(d.TOKEN[n],int(a),int(b)) for n,a,b in
            re.findall(r'\(\.(\w+), (\d+), (\d+)\)',block_text)]
    baseline=[x[0] for x in blocks]
    d.require(len(baseline)==201,'Baseline token count')
    prefix,suffix=baseline[:18],baseline[-3:]
    hh=d.heads()
    d.require(prefix+sum(map(d.emit,hh),[])+d.emit(d.old_gate())+suffix==baseline,
              'Independent formulas do not reconstruct literal baseline')
    _,x,(_,y,z)=hh[5]
    hh[5]=d.I(y,d.I(x,z))
    order=[0,5,1,2,3,4]
    expected=prefix+sum((d.emit(hh[j]) for j in order),[])+d.emit(d.new_gate('LRP',False))+suffix
    word_bytes=args.word.read_bytes()
    actual=[short(token) for token in json.loads(word_bytes)]
    d.require(actual==expected,'Selected word differs from claimed formula/permutation')
    delta=Counter(actual);delta.subtract(baseline)
    delta={k:v for k,v in sorted(delta.items()) if v}
    d.require(delta=={'C':-1,'D':1,'P':-2},'Unexpected macro multiset difference')
    weights={token:end-start for token,start,end in blocks}
    difference=sum(weights[k]*v for k,v in delta.items())
    d.require(len(actual)==199 and difference==-39,'Unexpected candidate counts')
    receipt={
        'result':'exact match',
        'upstream_commit':d.PIN,
        'selected_word_sha256':hashlib.sha256(word_bytes).hexdigest(),
        'head_emission_order_one_based':[j+1 for j in order],
        'exchanged_heads_one_based':[6],
        'gate_antecedent_order':'LRP',
        'gate_inner_exchange':False,
        'old_top_to_bottom':['h6','h5','h4','h3','h2','h1','rho8','generalization','saved'],
        'new_top_to_bottom':['h5','h4','h3','h2','h6_exchanged','h1','rho8','generalization','saved'],
        'guard':'A != H and A != D, unchanged',
        'gate_parameter_binding':{'a':'H','b':'D','c':'A'},
        'macro_tokens':len(actual),
        'macro_multiset_delta':delta,
        'source_sites':sizes['trie']+difference,
        'verification_scope':'formula emission, permutation, pinned source and exact counts; no physical TM claim'
    }
    out=json.dumps(receipt,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(out)
    print(out,end='')

if __name__=='__main__':main()
