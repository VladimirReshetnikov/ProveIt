#!/usr/bin/env python3
"""Extend the PA196 AX word search to membership-argument transposition.

Mode bit 0 transposes equality arguments; mode bit 1 transposes membership
arguments. Implication and the transposed quantifier remain unchanged.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
import sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(HERE))
import gate_variants as g
WORDFILE=HERE/'formula_words.py'
import formula_words as w

def transpose_membership(f):
    if isinstance(f,str):return f
    tag,a,b=f
    a,b=transpose_membership(a),transpose_membership(b)
    return (tag,b,a) if tag==1 else (tag,a,b)

def orient(f,mode):
    return transpose_membership(f) if mode&2 else f

def cpp(x):
    return '{'+','.join(cpp(a) if isinstance(a,list) else str(a) for a in x)+'}'

def numeric(f,env):
    if isinstance(f,str):return 1 if f=='1' else env[f]
    tag,a,b=f;a=numeric(a,env);b=numeric(b,env)
    return 4*((a+b)*(a+b+1)//2+b)+tag

def run_word(word,env):
    stack=[];t=17
    inverse={v:k for k,v in g.TOK.items()}
    for op in word:
        if op in inverse:
            stack.insert(0,t);t=env[inverse[op]]
        elif op=='node49':stack.insert(0,t);t=0
        elif op=='node65':
            a=stack.pop(0);b=t;t=4*((a+b)*(a+b+1)//2+b)
        elif op==g.INC:t+=1
        else:raise ValueError(op)
    assert stack==[17]
    return t

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path,default=HERE/'membership_config.json')
    p.add_argument('--header',type=Path,default=HERE/'membership_config.hpp')
    args=p.parse_args()
    symbols=list(dict.fromkeys(w.w));ids={s:i for i,s in enumerate(symbols)}
    perms=list(itertools.permutations('DHA'))
    mids=[ids[g.TOK[c]] for c in 'DHA']
    heads=[];gate=[];metadata=[];tests=0
    for mode in range(4):
        hs=[]
        for j in range(6):
            variants=[]
            for flags in range(8):
                f=orient(w.heads(flags,bool(mode&1))[j],mode)
                h=g.emit(f)
                for params in itertools.product(range(2),repeat=3):
                    env=dict(zip('DHA',params));assert run_word(h,env)==numeric(f,env);tests+=1
                for perm in perms:
                    remap=dict(zip(mids,[ids[g.TOK[c]] for c in perm]))
                    seq=[remap.get(ids[t],ids[t]) for t in h]
                    if seq not in variants:variants.append(seq)
            hs.append(variants)
        heads.append(hs)
        gs=[]
        for flags in itertools.product((False,True),repeat=3):
            f=orient(g.gate(*flags,equality_flip=bool(mode&1)),mode)
            seq=g.emit(f);assert len(seq)==77
            gs.append([ids[t]for t in seq])
            for params in itertools.product(range(2),repeat=3):
                env=dict(zip('DHA',params));assert run_word(seq,env)==numeric(f,env);tests+=1
        gate.append(gs)
        metadata.append({'mode':mode,'equality_transposed':bool(mode&1),'membership_transposed':bool(mode&2)})
    original=json.loads((HERE/'inputs/base_config.json').read_text())
    assert heads[:2]==original['heads']
    assert [gate[m][:2] for m in range(2)]==original['gate']
    obj={'symbols':symbols,'prefix':[ids[t]for t in w.prefix],
         'suffix':[ids[t]for t in w.suffix], 'heads':heads,'gate':gate,
         'modes':metadata,
         'gate_flags':[list(x)for x in itertools.product((False,True),repeat=3)],
         'numeric_emission_checks':tests,
         'scope':'Emitter spelling and encoding candidates; no physical machine, internal consistency theorem, or identity proof transport asserted.',
         'source_words_sha256':hashlib.sha256(WORDFILE.read_bytes()).hexdigest()}
    assert obj['prefix']==original['prefix'] and obj['suffix']==original['suffix']
    assert json.loads(json.dumps(obj['symbols']))==original['symbols']
    assert len(obj['prefix'])+sum(len(x[0])for x in heads[0])+77+len(obj['suffix'])==201
    args.output.write_text(json.dumps(obj,indent=2)+'\n')
    args.header.write_text('\n'.join([
        '#pragma once','const int NT='+str(len(symbols))+';','const int NM=4;','const int NG=8;',
        'vector<int> prefix='+cpp(obj['prefix'])+';',
        'vector<int> suffix='+cpp(obj['suffix'])+';',
        'vector<vector<vector<vector<int>>>> heads='+cpp(heads)+';',
        'vector<vector<vector<int>>> gate='+cpp(gate)+';'])+'\n')
    print(json.dumps({'modes':4,'head_options':[[len(v)for v in hs]for hs in heads],
                      'gate_options':[len(x)for x in gate],'numeric_checks':tests,
                      'inherited_modes_match':True,'symbols':symbols}))

if __name__=='__main__':main()
