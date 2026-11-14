#!/usr/bin/env python3
"""Finite local optimization scope; these checks imply no global lower bound."""
from pathlib import Path
import argparse, collections, hashlib, json
from certify_u221 import read, encode, known_symbol_analysis

def bisimulation(T):
    Q={q for q,b in T};classes={q:0 for q in Q};classes[254]=-1;rounds=0
    def partition(c):
        G=collections.defaultdict(set)
        for q,g in c.items():G[g].add(q)
        return frozenset(frozenset(v)for v in G.values())
    while True:
        signatures={q:tuple((w,d,classes[z])for b in(0,1)for w,d,z in[T[q,b]])for q in Q}
        ids={v:i for i,v in enumerate(sorted(set(signatures.values())))}
        new={q:ids[s]for q,s in signatures.items()};new[254]=-1;rounds+=1
        if partition(new)==partition(classes):classes=new;break
        classes=new
    groups=sorted([sorted(g)for g in partition(classes)])
    return {'working_states':len(Q),'state_classes_including_halt':len(groups),
            'refinement_rounds':rounds,'nontrivial_classes':[g for g in groups if len(g)>1]}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('old',type=Path);ap.add_argument('chosen',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args()
    old=read(a.old);chosen=read(a.chosen)
    alt={(q,b):(w,d,112 if z==200 else z)for(q,b),(w,d,z)in old.items()if q!=200}
    facts={}
    for name,T in [('U222',old),('U221_representative_209',chosen),('U221_representative_112',alt)]:
        facts[name]={'canonical_sha256':hashlib.sha256(encode(T)).hexdigest(),
                     'bisimulation':bisimulation(T),
                     'known_symbol_radius':3,
                     'excluded_rows':known_symbol_analysis(T)['excluded_rows']}
    result={'status':'FINITE_LOCAL_ANALYSIS_COMPLETE','machines':facts,
            'scope':'Strong deterministic transition-preserving bisimulation and radius-3 Cartesian known-symbol invariants from state 0 on arbitrary tapes. The two 221-state variants have singleton bisimulation classes and no excluded state/read pairs under this abstraction. This is not a lower bound and does not exclude other semantic, source, or encoding optimizations.'}
    s=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(s)
    print(s,end='')
if __name__=='__main__':main()
