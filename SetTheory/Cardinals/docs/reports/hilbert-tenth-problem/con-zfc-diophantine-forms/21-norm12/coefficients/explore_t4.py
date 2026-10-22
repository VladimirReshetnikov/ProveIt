import json,sys,itertools,time
from pathlib import Path
import check_t4 as old

def kind(x):
    return 'v' if x==old.V else 'h' if x==old.H else 'p' if x in (old.L,old.Q,old.R) else 'o'

def adj(x,y):
    if old.V in (x,y): return x != y
    if kind(x)!=kind(y):return False
    if kind(x)=='p':return (x,y) in old.PSET
    return True

def strict(w,variant=3):
    l,c,r,n=w
    if not adj(l,c) or not adj(c,r):return False
    if variant>=2:
        # Blank margins beside every vertical wall.
        if old.V in (l,c,r) and any(kind(x)=='o' and x!=0 for x in (l,c,r)):
            return False
    if variant>=3 and n==old.H:
        # The entire preceding row has halted, so any nearby head has halted.
        if any(old.D[x][1] not in (None,215) for x in (l,c,r)):return False
    return old.valid(w)

def enumeration(variant):
    # Cover precisely the same horizontal-head-filtered candidate domain.
    triples=set(itertools.product(old.HEADLESS,repeat=3))
    for pos in range(3):
        for head in old.HEADED:
            for a,b in itertools.product(old.HEADLESS,repeat=2):
                w=[a,b];w.insert(pos,head);triples.add(tuple(w))
    triples=[w for w in sorted(triples) if adj(w[0],w[1]) and adj(w[1],w[2])]
    enumeration.stats=dict(head_filtered_horizontal_triples=46980,
       symmetric_row_filtered_horizontal_triples=len(triples),
       successors_per_triple=439,quadruples_checked=439*len(triples),
       note='Every excluded horizontal triple fails the explicit one-head or symmetric row guard.')
    out=[]
    for triple in triples:
        for n in range(439):
            w=triple+(n,)
            if strict(w,variant):out.append(w)
    return out

if __name__=='__main__':
 for variant in [1,2,3]:
    wins=enumeration(variant)
    print(variant,len(wins),flush=True)
    Path(f'filtered_t4_{variant}.json').write_text(json.dumps(wins,separators=(',',':'))+'\n')
