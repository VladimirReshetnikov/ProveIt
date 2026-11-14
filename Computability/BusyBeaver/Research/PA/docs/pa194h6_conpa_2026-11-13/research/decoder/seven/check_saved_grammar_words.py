#!/usr/bin/env python3
"""Validate every saved grammar's exact seven-head source word.

This verifies the mutation domain, not any consistency theorem or physical
implementation.  A head's three parameters may be bijectively renamed.
"""
from pathlib import Path
from functools import lru_cache
from itertools import permutations
import argparse,json

LEAF={'node65':90,'node55':98,'node58':12,'node70':166,
      'node49':19,'node72':69,'node75':213,'node142':194,'node150':221}
VARIABLES=(98,12,166)
LENGTHS=(17,19,16,16,16,19,7)

def word(path):
    obj=json.loads(path.read_text()); rules=obj['rules']
    def rec(t):
        if isinstance(t,str):
            if t in LEAF:return [LEAF[t]]
            if t=='node60':return [61,61]
            if t=='node61':return [61]*4
            return rec(rules[t])
        if t==['leaf','inc',1]:return [61]
        if t==['leaf','breakTo',1]:return [-1]
        return rec(t[0])+rec(t[1])
    return rec(obj['root'])

def original_word(seedpath):
    lines=seedpath.read_text().splitlines();p=int(lines[0])+2
    tid,n,root=map(int,lines[p].split());p+=1;nodes=[]
    for _ in range(n):
        op,a,b,c=map(int,lines[p].split());p+=1
        nodes.append([a] if op==0 else nodes[a]+nodes[b])
    return nodes[root]

def check(candidate,original):
    if len(candidate)!=190 or candidate[:18]!=original[:18] or candidate[128:]!=original[128:]:
        raise ValueError('source word prefix, suffix, or length changed')
    heads=[];start=18
    for length in LENGTHS:
        head=original[start:start+length];variants=set()
        for perm in permutations(VARIABLES):
            rename=dict(zip(VARIABLES,perm))
            variants.add(tuple(rename.get(x,x)for x in head))
        heads.append(variants);start+=length
    @lru_cache(None)
    def match(pos,remaining):
        if not remaining:return () if pos==128 else None
        for j in range(7):
            if remaining>>j&1 and tuple(candidate[pos:pos+LENGTHS[j]])in heads[j]:
                tail=match(pos+LENGTHS[j],remaining^(1<<j))
                if tail is not None:return (j,)+tail
        return None
    order=match(18,127)
    if order is None:raise ValueError('not a permutation of seven independently renamed heads')
    return list(order)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent);a=ap.parse_args()
    original=original_word(a.directory/'seeds.txt')
    result=[]
    for p in sorted(a.directory.glob('*.seed*.grammar.json')):
        result.append({'file':p.name,'macro_tokens':190,'head_order':check(word(p),original)})
    for p in sorted(a.directory.glob('*.best.grammar.json')):
        result.append({'file':p.name,'macro_tokens':190,'head_order':check(word(p),original)})
    print(json.dumps({'checked_saved_grammars':len(result),'all_words_valid':True,'scope':'Exact mutation-domain check only. Not a physical or PA proof.','grammars':result},indent=2))
if __name__=='__main__':main()
