"""Finite independent diagnostics for the exact two-coordinate B6 replacement."""
from itertools import product
import json
from pathlib import Path

def relations(n):
    edges=[(i,j) for i in range(n) for j in range(i,n)]
    for mask in range(1<<len(edges)):
        rows=[0]*n
        for k,(i,j) in enumerate(edges):
            if mask>>k&1:
                rows[i]|=1<<j;rows[j]|=1<<i
        yield tuple(rows)

def box(r,p,n):
    return sum((1<<i) for i,row in enumerate(r) if row&p==row)
def dia(r,p,n):
    return sum((1<<i) for i,row in enumerate(r) if row&p)
def implies(p,q,n):return ((~p)|q)&((1<<n)-1)
def run():
    counts={'relation_pairs':0,'payload_valuations':0,'B6_checks':0,'schema_equivalence_checks':0}
    for n in (1,2,3):
        allbits=(1<<n)-1
        for a,b in product(relations(n),repeat=2):
            old=True;new=True
            for p in range(1<<n):
                assert implies(dia(a,box(a,p,n),n),p,n)==allbits
                assert implies(dia(b,box(b,p,n),n),p,n)==allbits
                counts['B6_checks']+=2
                old &= implies(box(a,box(b,p,n),n),box(b,box(a,p,n),n),n)==allbits
                new &= implies(dia(a,dia(b,box(a,box(b,p,n),n),n),n),p,n)==allbits
                counts['payload_valuations']+=1
            assert old==new
            counts['schema_equivalence_checks']+=1;counts['relation_pairs']+=1
    return dict(counts,all_passed=True,proof_status='Finite tests; unrestricted proof in double_b6_route.md.')
if __name__=='__main__':
    if not __debug__: raise RuntimeError('Run without -O: assertions are part of these diagnostics.')
    result=run();Path(__file__).with_name('double_b6_modal_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
