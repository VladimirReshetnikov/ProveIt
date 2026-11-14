#!/usr/bin/env python3
"""Convert a saved .shape/.word witness into an explicit AX grammar.

This is only a witness decoder, not a correctness checker for a new TM.
"""
from pathlib import Path
import argparse,json
p=argparse.ArgumentParser(description=__doc__)
p.add_argument("witness",type=Path,help="metadata JSON; .shape and .word are appended")
p.add_argument("output",type=Path)
a=p.parse_args()
terms=["node58","node55","node65",("leaf","inc",1),"node72","node75","node70","node49","node142","node150",("leaf","breakTo",1)]
w=list(map(int,Path(str(a.witness)+".word").read_text().split()))
values=[terms[t] for t in w]
for line in Path(str(a.witness)+".shape").read_text().splitlines():
    i,j=map(int,line.split())
    assert 0<=i<len(values) and 0<=j<len(values)
    values.append((values[i],values[j]))
rules={};names={}
def enc(t):
    if not (isinstance(t,tuple) and len(t)==2):return t
    if t in names:return names[t]
    pair=[enc(x) for x in t]
    k="g"+str(len(rules));names[t]=k;rules[k]=pair
    return k
root=enc(values[-1])
a.output.write_text(json.dumps({"root":root,"rules":rules},indent=2,sort_keys=True)+"\n")
print(json.dumps({"macro_tokens":len(w),"grammar_nodes":len(rules)},sort_keys=True))
