#!/usr/bin/env python3
"""Decoder reassociations with the literal permutation252 runtime retained.

Reuses the closed-region rotation criterion and contextual-subtree emitter
from the attributed source09/source27 experiments at the pinned ProveIt
commit. New experiment: simultaneous rotations scored by actual graph-reachable
table size after removal of old bootstrap state5 and register permutation.
Passing structural tests is NOT a consistency proof or runtime certificate.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter,deque
import hashlib,json,random,math,time,argparse,sys,importlib.util

HERE=Path(__file__).resolve().parent
OLD=json.loads((HERE/'decoder_entries.json').read_text())
NODES={int(k):tuple(map(tuple,v)) for k,v in OLD['nodes'].items()}
ROOT=OLD['root']
NEWPHYS=(6,2,0,4,3,7,8,5,1)
BASE={}
for line in (HERE/'candidate-permutation252/zfc_permutation252_old.tm').read_text().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,t=line.split();BASE[q,int(b)]=int(w),d,t
OLD_FP={v:int(n) for n,v in OLD['fingerprints'].items()}
CONTROL_OPTIONS={}
for n,pair in NODES.items():
    for bit,e in enumerate(pair):
        if e[0] not in 'BC':continue
        key=e,bit;counts=CONTROL_OPTIONS.setdefault(key,Counter())
        for state,weight in OLD['state_entries'][str(n)].items():counts[BASE[state,bit]]+=weight

def emit(nodes,root):
    @lru_cache(None)
    def fingerprint(e):
        text='N('+','.join(fingerprint(x) for x in nodes[e[1]])+')' if e[0]=='N' else ':'.join(map(str,e))
        return hashlib.sha256(text.encode()).hexdigest()
    table=BASE.copy();entries={};allocate=255
    def modal(counts):return max(counts,key=counts.get)
    for n in nodes:
        f=fingerprint(('N',n))
        if n==root:entries[n]='96'
        elif f in OLD_FP:entries[n]=modal(OLD['state_entries'][str(OLD_FP[f])])
        else:entries[n]=str(allocate);allocate+=1
    def action(e,b):
        if e[0]=='N':return b,'R',entries[e[1]]
        if e[0]=='B' and e[1]==1:return 0,'L','7' if b==0 else '33'
        if e[0] in 'BC':return CONTROL_OPTIONS[e,b].most_common(1)[0][0]
        return b,'R',modal(OLD['leaf_entries'][':'.join(map(str,e))])
    for n in nodes:
        if entries[n]=='96' or fingerprint(('N',n)) not in OLD_FP:
            for b,e in enumerate(nodes[n]):table[entries[n],b]=action(e,b)
    return table

def gc(table):
    seen=set();todo=['64']
    while todo:
        q=todo.pop()
        if q in seen or q=='254':continue
        seen.add(q);todo.extend(table[q,b][2] for b in (0,1))
    return {k:v for k,v in table.items() if k[0] in seen}

def bounds(nodes):
    @lru_cache(None)
    def f(e):
        if e[0]!='N':return (0,e[1] if e[0]=='B' else 1 if e[0]=='D' else 0,e[1] if e[0]=='C' else 0)
        a,b=map(f,nodes[e[1]])
        return 1+max(a[0],b[0]),max(a[1]-1,b[1]),max(a[2],b[2]-1)
    return f

def options(nodes):
    f=bounds(nodes);closed=lambda e:f(e)[1:]==(0,0);out=[]
    for n,(x,y) in nodes.items():
        if x[0]=='N':
            a,c=nodes[x[1]]
            if all(map(closed,(a,c,y))):out.append((n,('T',a,('T',c,y)),'right'))
        if y[0]=='N':
            a,c=nodes[y[1]]
            if all(map(closed,(x,a,c))):out.append((n,('T',('T',x,a),c),'left'))
        if x[0]==y[0]=='I' and x!=y:out.append((n,('T',y,x),'commute'))
    return out

def mutate(nodes,root,n,exp):
    new={};seen={}
    def intern(a,b):
        p=a,b
        if p not in seen:i=len(new);seen[p]=i;new[i]=p
        return ('N',seen[p])
    @lru_cache(None)
    def edge(e):
        if e[0]=='N':
            if e[1]==n:return edge(exp)
            return intern(*map(edge,nodes[e[1]]))
        if e[0]=='T':return intern(edge(e[1]),edge(e[2]))
        return e
    r=edge(('N',root))[1]
    return new,r

def metrics(nodes,root):
    @lru_cache(None)
    def f(e):
        if e[0]!='N':return (0,0,0)
        a,b=map(f,nodes[e[1]]);p=1+a[0]
        return p,max(p,a[1],b[1]),1+max(a[2],b[2])
    return f(('N',root))

def save(path,table):
    path.write_text('#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t)in sorted(table.items(),key=lambda a:(int(a[0][0]),a[0][1]))))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--iterations',type=int,default=10000);ap.add_argument('--seed',type=int,default=252);ap.add_argument('--restarts',type=int,default=10)
    ap.add_argument('--output',type=Path,default=HERE/'rotation-results.json');args=ap.parse_args()
    assert emit(NODES,ROOT)==BASE
    candidates=[];seen_dags=set();outdir=HERE/'rotation-candidates';outdir.mkdir(exist_ok=True)
    def score(ns,r):
        m=metrics(ns,r)
        if m[1]>7 or m[2]>39:return 10000,None
        try:t=gc(emit(ns,r))
        except KeyError:return 10000,None
        return len(t)//2,t
    singles=[]
    for i,(n,e,k) in enumerate(options(NODES)):
        ns,r=mutate(NODES,ROOT,n,e);v,t=score(ns,r);singles.append((v,i,n,k,len(ns)))
        if v<252:
            stem=f'single-{i}-{v}';save(outdir/(stem+'.tm'),t);(outdir/(stem+'.json')).write_text(json.dumps({'nodes':ns,'root':r}));candidates.append(stem)
    print('Singles',dict(Counter(x[0] for x in singles)),flush=True)
    minima=sorted(singles)[:10];print('Minima',minima,flush=True)
    rng=random.Random(args.seed);best=(252,NODES,ROOT,[]);improvements=[];steps=0;start=time.monotonic()
    # Maintain short paths away from the retained optimum; permit temporary growth.
    for restart in range(args.restarts):
        cur,r=NODES,ROOT;cost=252;history=[]
        for i in range(args.iterations):
            opts=options(cur)
            if not opts:break
            j=rng.randrange(len(opts));n,e,k=opts[j];ns,nr=mutate(cur,r,n,e);nc,table=score(ns,nr);steps+=1
            temperature=.15+1.2*(1-i/args.iterations)
            if nc<=cost or rng.random()<math.exp((cost-nc)/temperature):
                cur,r,cost=ns,nr,nc;history=history+[(n,k,j)]
            if nc<best[0]:
                best=(nc,ns,nr,history+[(n,k,j)]);improvements.append([restart,i,nc,len(ns),len(history)+1]);print('Best',improvements[-1],flush=True)
            if nc<=251:
                digest=hashlib.sha256(json.dumps(ns,sort_keys=True).encode()).hexdigest()
                if digest not in seen_dags:
                    seen_dags.add(digest);stem=f'r{restart}-i{i}-{nc}';save(outdir/(stem+'.tm'),table);(outdir/(stem+'.json')).write_text(json.dumps({'nodes':ns,'root':nr,'history':history+[(n,k,j)]}));candidates.append(stem)
            if i%500==0:print('Progress',restart,i,cost,best[0],len(candidates),round(time.monotonic()-start,2),flush=True)
    result={'baseline_states':252,'single_options':singles,'seed':args.seed,'restarts':args.restarts,'iterations_per_restart':args.iterations,'tested_steps':steps,'best_graph_states':best[0],'candidates':candidates,'improvements':improvements,'elapsed_seconds':time.monotonic()-start,'scope':'Actual transition graph counts only; runtime and startup unverified for candidates.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
