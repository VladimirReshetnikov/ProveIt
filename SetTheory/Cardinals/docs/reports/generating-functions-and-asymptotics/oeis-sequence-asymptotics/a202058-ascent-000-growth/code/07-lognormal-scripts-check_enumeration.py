#!/usr/bin/env python3
"""Independent finite word enumeration versus compacted transfer. No asymptotic inference."""
from collections import defaultdict
from pathlib import Path
import json

def children(x):
    s,u,k=x
    for i in range(s+u):
        if i<s:
            yield s-1,u+int(i>=k),i
        else:
            yield s+1,u-int(i<k),i+1

def transfer_counts(nmax):
    counts=[1,1]; states={(1,1,1):1}
    for n in range(2,nmax+1):
        nxt=defaultdict(int)
        for x,mult in states.items():
            for child in children(x):
                nxt[child]+=mult
        states=nxt;counts.append(sum(states.values()))
    return counts

def literal_counts(nmax):
    counts=[1]+[0]*nmax
    def visit(word, asc, used):
        n=len(word); counts[n]+=1
        if n==nmax:return
        for value in range(asc+2):
            if used.get(value,0)==2:continue
            used[value]=used.get(value,0)+1
            visit(word+(value,),asc+int(word[-1]<value),used)
            used[value]-=1
    visit((0,),0,{0:1})
    return counts

nmax=10
literal=literal_counts(nmax); transfer=transfer_counts(nmax)
reference=[1,1,2,4,10,27,83,277,1015,4007,17047]
assert literal==transfer==reference
out={'passed':True,'nmax':nmax,'literal_word_counts':literal,
     'compacted_transfer_counts':transfer,
     'scope':'Independent finite enumeration only; no asymptotic inference'}
Path(__file__).with_name('enumeration-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
