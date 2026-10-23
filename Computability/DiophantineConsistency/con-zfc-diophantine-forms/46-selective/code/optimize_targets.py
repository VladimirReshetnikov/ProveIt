#!/usr/bin/env python3
"""Choose certified target shifts; the search is not a correctness premise."""
import argparse,json,random,math,time
from pathlib import Path

def prepare(weights,rows):
    t=max(weights); n=len(rows)
    pair_sums={weights[i]+weights[j] for i in range(len(weights)) for j in range(i,len(weights))}
    supports=[{sum(a*w for a,w in zip(term['alpha'],weights[1:])) for term in row} for row in rows]
    forbidden=[{s-e for s in pair_sums for e in support} for support in supports]
    costs=[[next(d for d in range(t+1,2*t+2) if d not in forbidden[i] and -d not in forbidden[j]) for j in range(n)] for i in range(n)]
    return t,supports,forbidden,costs

def optimize(weights,rows,seconds=20,seed=23023):
    t,supp,forbidden,cost=prepare(weights,rows);n=len(rows);rng=random.Random(seed)
    # Fix last row: its constant coefficient is +2 and dominates D.
    def total(p):return 2*t+sum(cost[a][b] for a,b in zip(p,p[1:]))
    p=list(range(n));best=p[:];score=total(p);bs=score;steps=0;until=time.monotonic()+seconds
    while time.monotonic()<until:
        if steps%100000==0:
            p=list(range(n-1));rng.shuffle(p);p+=[n-1];score=total(p)
        i,j=rng.sample(range(n-1),2);p[i],p[j]=p[j],p[i]
        ns=total(p);temperature=0.6+20*(1-(steps%100000)/100000)**3
        if ns<=score or rng.random()<math.exp((score-ns)/temperature):score=ns
        else:p[i],p[j]=p[j],p[i]
        if score<bs:bs=score;best=p[:]
        steps+=1
    targets=[2*t]
    for a,b in zip(best,best[1:]):targets.append(targets[-1]+cost[a][b])
    # Independently check all pairs, including nonadjacent rows.
    for i,a in enumerate(best):
        if targets[i]<max(supp[a]):raise ValueError('negative exponent')
        for j,b in enumerate(best):
            if i!=j and targets[j]-targets[i] in forbidden[a]:raise ValueError('cross-target collision')
    return {'weights':weights,'t':t,'row_permutation':best,'targets':targets,'span':targets[-1]+2*t,
            'gaps':[b-a for a,b in zip(targets,targets[1:])],'seed':seed,'search_steps':steps,
            'certificate':'All active monomials isolated; all cross-target convolution contributions excluded.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('weights');ap.add_argument('rows');ap.add_argument('output');ap.add_argument('--seconds',type=float,default=20)
    a=ap.parse_args();w=json.loads(Path(a.weights).read_text())['weights'];r=json.loads(Path(a.rows).read_text())['rows']
    result=optimize(w,r,a.seconds);Path(a.output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
