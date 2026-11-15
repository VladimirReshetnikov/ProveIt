#!/usr/bin/env python3
"""Exact transition-graph isomorphism screen, including four global symmetries.

Roots may move arbitrarily. Incoming terminal actions are ignored. The
bit-exchange option is a structural test, not fixed-zero-blank equivalence.
Partition refinement only prunes: final matching explicitly maps every state
and checks every labeled edge. Failed backtracking exhausts the finite map
search, rather than relying on unequal cryptographic hashes.
"""
import argparse,collections,json,pathlib

def parse(path,mirror=False,swap=False,loose=True):
    rows={}
    for line in pathlib.Path(path).read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        if mirror:d='L' if d=='R' else 'R'
        if swap:b,w=1-b,1-w
        assert (q,b) not in rows
        rows[q,b]=(w,d,n)
    states=sorted({q for q,b in rows});ids={q:i for i,q in enumerate(states)}
    assert all((q,b) in rows for q in states for b in (0,1))
    out=[]
    for q in states:
        rr=[]
        for b in (0,1):
            w,d,n=rows[q,b]
            rr.append((w,d,ids[n]) if n in ids else ((0,'R',-1) if loose else (w,d,-1)))
        out.append(tuple(rr))
    return tuple(out),states

def colors_pair(a,b):
    if len(a)!=len(b):return None
    n=len(a)
    graphs=(a,b);colors=[[0]*n,[0]*n]
    incoming=[]
    for g in graphs:
        inc=[[] for _ in range(n)]
        for q,rr in enumerate(g):
            for sym,(w,d,t) in enumerate(rr):
                if t!=-1:inc[t].append((q,sym,w,d))
        incoming.append(inc)
    for _ in range(2*n+1):
        sig=[]
        for gi,g in enumerate(graphs):
            c=colors[gi]
            sig.append([(c[q],tuple((w,d,c[t] if t!=-1 else -1) for w,d,t in rr),
                         tuple(sorted((c[p],sym,w,d) for p,sym,w,d in incoming[gi][q])))
                        for q,rr in enumerate(g)])
        if collections.Counter(sig[0])!=collections.Counter(sig[1]):return None
        labels={v:i for i,v in enumerate(sorted(set(sig[0]+sig[1])))}
        new=[[labels[v] for v in s] for s in sig]
        if new==colors:return tuple(tuple(c) for c in colors)
        # Refinement may renumber stable partitions; equal number of classes suffices.
        if len(set(new[0]))==len(set(colors[0])):return tuple(tuple(c) for c in new)
        colors=new
    raise AssertionError('partition refinement did not stabilize')

def isomorphic(a,b):
    colors=colors_pair(a,b)
    if colors is None:return None
    ca,cb=colors;n=len(a)
    targets=collections.defaultdict(list)
    for r,col in enumerate(cb):targets[col].append(r)
    def propagate(mapping,inverse,q,r):
        mapping=mapping.copy();inverse=inverse.copy();todo=[(q,r)]
        while todo:
            q,r=todo.pop()
            if q in mapping:
                if mapping[q]!=r:return None
                continue
            if r in inverse or ca[q]!=cb[r]:return None
            mapping[q]=r;inverse[r]=q
            for x,y in zip(a[q],b[r]):
                if x[:2]!=y[:2] or (x[2]==-1)!=(y[2]==-1):return None
                if x[2]!=-1:todo.append((x[2],y[2]))
        return mapping,inverse
    def go(mapping,inverse):
        if len(mapping)==n:return mapping
        q=min((q for q in range(n) if q not in mapping),
              key=lambda q:sum(r not in inverse for r in targets[ca[q]]))
        for r in targets[ca[q]]:
            if r in inverse:continue
            pair=propagate(mapping,inverse,q,r)
            if pair is not None:
                found=go(*pair)
                if found is not None:return found
        return None
    result=go({},{})
    if result is not None:
        assert len(result)==n and len(set(result.values()))==n
        for q,r in result.items():
            for x,y in zip(a[q],b[r]):
                assert x[:2]==y[:2]
                assert (-1 if x[2]==-1 else result[x[2]])==y[2]
    return result

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('machines',nargs='+',type=pathlib.Path)
    ap.add_argument('--corpus',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent/'current_194_representatives')
    ap.add_argument('--out',type=pathlib.Path)
    args=ap.parse_args()
    index=json.loads((args.corpus/'index.json').read_text())
    corpus=[(i,parse(args.corpus/i['representative'])[0]) for i in index]
    results=[]
    for p in args.machines:
        matches=[];checks=0
        for mirror in (False,True):
            for swap in (False,True):
                a,labels=parse(p,mirror=mirror,swap=swap)
                for item,b in corpus:
                    checks+=1;found=isomorphic(a,b)
                    if found is not None:
                        matches.append({'table_class':item['table_class'],'source':item['source'],
                                        'mirror':mirror,'swap_bits':swap,
                                        'mapping_to_representative_index':{str(labels[q]):r for q,r in found.items()}})
        r={'machine':str(p),'checked_corpus_tables':len(corpus),'exact_isomorphism_attempts':checks,
           'novel_under_enlarged_structural_equivalence':not matches,'matches':matches}
        results.append(r);print(p,'NOVEL' if not matches else 'MATCH',len(matches),flush=True)
    if args.out:args.out.write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':main()
