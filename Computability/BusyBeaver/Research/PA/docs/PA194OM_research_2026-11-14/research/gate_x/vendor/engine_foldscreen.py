"""Small reproducible raw-action fold screen, adapted from the retained compiler.
Every proposed simultaneous fold must subsequently pass build.check_folds.
This is a finite search family, not a global minimization algorithm.
"""
from collections import defaultdict

def opportunities(rows):
    incoming=defaultdict(set)
    for (q,b),(w,d,n) in rows.items():
        if d and w==b:incoming[n].add(b)
    providers=[defaultdict(list),defaultdict(list)]
    for h in {q for q,b in rows}:
        w0,d0,u0=rows[h,0];w1,d1,u1=rows[h,1]
        if w0 or w1!=1 or not d0 or not d1:continue
        for bit in (0,1):
            if (u0,bit) in rows and (u1,bit) in rows:
                providers[bit][(rows[u0,bit],rows[u1,bit])].append((h,u0,u1))
    states={q for q,b in rows}
    left=sorted(q for q in states if incoming[q]=={0})
    right=sorted(q for q in states if incoming[q]=={1})
    result=[]
    for a in left:
        for b in right:
            opts=[]
            for bit in (0,1):
                if rows[a,bit]==rows[b,bit]:opts.append([rows[a,bit]])
                else:opts.append([(bit,False,h) for h,u0,u1 in providers[bit].get((rows[a,bit],rows[b,bit]),[]) if not {a,b}&{h,u0,u1}])
            if all(opts):result.append((a,b,opts))
    return result

def matching(ops):
    edges=defaultdict(list)
    for a,b,_ in ops:edges[a].append(b)
    matches={}
    def augment(a,seen):
        for b in edges[a]:
            if b in seen:continue
            seen.add(b)
            if b not in matches or augment(matches[b],seen):
                matches[b]=a
                return True
        return False
    for a in edges:augment(a,set())
    return [(a,b) for b,a in matches.items()]

def proposed_folds(rows):
    ops=opportunities(rows);choices={(a,b):o for a,b,o in ops}
    return [[a,b,[o[0] for o in choices[a,b]]] for a,b in matching(ops)]
