#!/usr/bin/env python3
"""Reconstruct PA196's AX word and emit the equivalent distributed gate.

This script counts macros/source primitives. It does not construct a binary TM.
Usage: python3 distributed_gate.py /path/to/BusyBeaver --output result_directory
Only the Python standard library is required.
"""
from pathlib import Path
from collections import Counter
from itertools import permutations
import argparse
import hashlib
import json
import re

PIN = '407cdc356f6b586635e71ac92be394255f4bfea4'
PROGRAM_HASH = '8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872'
AX_HASH = '8eda8dc0ed0b445c05726990c5a07634464c10ba547fff6bbdba516578ad572c'
TOKEN = {'push':'P','copyD':'D','copyH':'H','copyA':'A','cons':'C','incT':'i',
         'readH':'rH','readDCons':'rDC','copyGuard':'gc','compareGuard':'gt','close':'J'}

def require(b, why):
    if not b:
        raise ValueError(why)

def I(a,b): return (0,a,b)
def M(a,b): return (1,a,b)
def U(a,b): return (2,b,a)
def E(a,b): return (3,a,b)
def N(a): return I(a,'1')
def conj(a,b): return N(I(a,N(b)))
def ex(x,a): return N(U(x,N(a)))

def emit(x):
    if isinstance(x,str):
        return ['P','i'] if x=='1' else [x]
    tag,a,b=x
    return emit(a)+emit(b)+['C']+['i']*tag

def expanded_counts(program_text):
    """Count primitive leaves from the pinned, acyclic literal Tree definitions."""
    sizes={}
    for name,expr in re.findall(r'^def (\w+) : Tree := (.+)$',program_text,re.M):
        refs=re.findall(r'\b(?:node\d+|x\d+)\b',expr)
        require(all(ref in sizes for ref in refs),'Non-topological Tree definitions')
        sizes[name]=expr.count('.leaf')+sum(sizes[ref] for ref in refs)
    require(sizes.get('trie')==3812,'Unexpected literal source expansion')
    return sizes

def heads():
    d,h,a='DHA'
    return [I(ex(d,U(d,h)),h), I(U(d,U(a,h)),U(a,U(d,h))),
            I(M(h,d),I(E(h,a),M(a,d))), I(E(h,d),I(M(a,h),M(a,d))),
            ex(d,E(h,d)), I(U(d,a),I(U(d,I(a,h)),U(d,h)))]

def parts(inner_swap=False):
    a,b,c='HDA'
    delta=I(E(a,b),U(c,E(a,b)))
    vac=I(M(a,b),U(c,M(a,b)))
    point=I(c,M(c,b))
    left=I(c,I(M(a,b),M(c,b))) if inner_swap else I(M(a,b),point)
    right=I(M(c,b),c)
    return delta,vac,point,left,right

def old_gate():
    delta,vac,point,left,right=parts()
    return N(I(delta,I(vac,U('A',I(U('D',conj(left,right)),N(point))))))

def new_gate(order,inner_swap):
    delta,vac,point,left,right=parts(inner_swap)
    terms={'L':U('D',left),'R':U('D',right),'P':point}
    tail='1'
    for key in reversed(order):
        tail=I(terms[key],tail)
    return N(I(delta,I(vac,U('A',tail))))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    raw=(args.source/'PA196/Program.lean').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==PROGRAM_HASH,'Unexpected PA196 Program.lean')
    sizes=expanded_counts(raw.decode())
    axraw=(args.source/'PA196/Source/AXProgram.lean').read_bytes()
    require(hashlib.sha256(axraw).hexdigest()==AX_HASH,'Unexpected PA196 AXProgram.lean')
    block_text=axraw.decode().split('def blocks :',1)[1].split('def program :',1)[0]
    blocks=[(TOKEN[n],int(a),int(b)) for n,a,b in re.findall(r'\(\.(\w+), (\d+), (\d+)\)',block_text)]
    require(len(blocks)==201,'Unexpected AX macro count')
    require(blocks[0][1]==50 and blocks[-1][2]==3693,'Unexpected AX source boundaries')
    require(all(x[2]==y[1] for x,y in zip(blocks,blocks[1:])),'Discontinuous macro blocks')
    weights={}
    for token,start,end in blocks:
        require(token not in weights or weights[token]==end-start,'Nonuniform macro length')
        weights[token]=end-start
    require(weights['D']==sizes['node55']==26,'copyD size mismatch')
    require(weights['C']==sizes['node65']==27,'cons size mismatch')
    require(weights['P']==sizes['node49']==19,'push size mismatch')
    word=[x[0] for x in blocks]
    prefix,suffix=word[:18],word[-3:]
    common=prefix+sum((emit(h) for h in heads()),[])
    require(common+emit(old_gate())+suffix==word,'Mathematical formula does not reconstruct AX word')
    args.output.mkdir(parents=True,exist_ok=True)
    cases=[]
    for order in permutations('LRP'):
        for swap in (False,True):
            fresh=common+emit(new_gate(order,swap))+suffix
            delta=Counter(fresh);delta.subtract(word)
            delta={k:v for k,v in sorted(delta.items()) if v}
            require(delta=={'C':-1,'D':1,'P':-2},'Unexpected token multiset change')
            source_delta=sum(weights[k]*v for k,v in delta.items())
            require(len(fresh)==199 and source_delta==-39,'Unexpected expansion counts')
            name='distributed_'+''.join(order)+('_swap' if swap else '')
            (args.output/(name+'.word.json')).write_text(json.dumps(fresh,indent=2)+'\n')
            cases.append({'name':name,'antecedent_order':order,'inner_swap':swap,
                          'macro_tokens':len(fresh),'source_sites':sizes['trie']+source_delta})
    receipt={'upstream_commit':PIN,'program_sha256':PROGRAM_HASH,
             'ax_program_sha256':hashlib.sha256(axraw).hexdigest(),
             'baseline_gate_tokens':len(emit(old_gate())),
             'revised_gate_tokens':len(emit(new_gate('LRP',False))),
             'baseline_macro_tokens':201,'revised_macro_tokens':199,
             'token_multiset_delta':{'C':-1,'D':1,'P':-2},
             'macro_source_lengths':weights,'baseline_source_sites':3812,
             'revised_source_sites':3773,'variants':cases,
             'state_count':'not established; requires a separately verified physical compilation'}
    (args.output/'distributed_gate_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='variants'},indent=2))

if __name__=='__main__': main()
