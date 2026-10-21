#!/usr/bin/env python3
"""Structural lookup census, separate from kernel correctness and wall-clock timing."""
from pathlib import Path
import json, re
ROOT=Path(__file__).resolve().parent
rows=[tuple(map(int,m)) for m in re.findall(
    r'\((\d+)%positive,(\d+)%positive,(\d+)%N,(\d+)%N\)',
    (ROOT/'Cert215Compact.v').read_text())]
assert len(rows)==2240
# Independently read the exact compact program table, using its zero-padded
# Boolean path semantics. This census is not a premise of the formal theorem.
program=(ROOT/'deps/K215F/Prog215.v').read_text()
block=program.split('Definition p215_tab',1)[1].split(':= [',1)[1].split('].',1)[0]
program_rows=re.findall(r'\((C[NIDBC] \d+|CH), (C[NIDBC] \d+|CH)\)',block)
assert len(program_rows)==179
start=int(re.search(r'root := (\d+)',program).group(1));assert start==178
def decode(n):
    out=[]
    while n>1:out.append(bool(n&1));n//=2
    return out
def leaf(a):
    bits=decode(a); n=start
    for d in range(180):
        tag=program_rows[n][int(bits[d]) if d<len(bits) else 0].split()
        if tag[0]!='CN':return tag[0]
        n=int(tag[1])
    raise AssertionError('decoder fuel exhausted')
refs=[0]
types={}
for i,(_,_,j,k) in enumerate(rows):
    kind=leaf(rows[i][0]);types[kind]=types.get(kind,0)+1
    if kind=='CD':refs.extend([j,k])
    else:assert kind=='CH'
assert types=={'CD':2239,'CH':1}
assert len(refs)==4479 and all(0<=j<len(rows) for j in refs)
def depth(n,j):
    if n==0:return 0
    if n==1:return 1
    k=n//2
    return 1+(depth(k,j) if j<k else depth(n-k,j-k))
a=sum(j+1 for j in refs); b=sum(depth(len(rows),j) for j in refs)
result={'entries':len(rows),'types':{'EDecnz':2239,'EHalt':1},'lookups':len(refs),
        'list_constructors_visited':a,'tree_nodes_visited':b,
        'max_tree_nodes_visited':max(depth(len(rows),j) for j in refs),
        'mean_list_visits':a/len(refs),'mean_tree_visits':b/len(refs)}
expected=json.loads((ROOT/'evidence/lookup_metrics.json').read_text())
assert result==expected, (result,expected)
print(json.dumps(result,indent=2))
