#!/usr/bin/env python3
"""Regenerate the exact guarded continuation partition, without bounded runs.
The shipped verifier uses its own parser, graph arithmetic and refinement.
"""
from pathlib import Path
import argparse,collections,json
from source_decoder import Decoder,read_literal,LITERAL

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();nodes,root=read_literal(LITERAL);dec=Decoder(nodes,root);G=dec.graph()
    epsilon=[None]*len(G);rank=[None]*len(G);pending=set()
    def norm(i):
        if epsilon[i] is not None:return epsilon[i],rank[i]
        assert i not in pending,'silent control cycle'
        if G[i][0][0] not in ('B','C'):epsilon[i]=i;rank[i]=0;return i,0
        pending.add(i);j,r=norm(G[i][1][0]);pending.remove(i)
        epsilon[i]=j;rank[i]=r+1;return j,r+1
    for i in range(len(G)):norm(i)
    active=[i for i in range(len(G)) if epsilon[i]==i]
    def partition(indices,label,succ):
        ids={};C={i:ids.setdefault(label(i),len(ids)) for i in indices}
        while True:
            ids={};D={i:ids.setdefault((label(i),tuple(C[j] for j in succ(i))),len(ids)) for i in indices}
            if D==C:return C
            C=D
    weak=partition(active,lambda i:G[i][0],lambda i:[epsilon[j] for j in G[i][1]])
    strong=partition(range(len(G)),lambda i:G[i][0],lambda i:G[i][1])
    generic=partition(range(len(G)),lambda i:('noop',) if G[i][0][0] in ('B','C') else G[i][0],lambda i:G[i][1])
    classes=[weak[epsilon[i]] for i in range(len(G))]
    result=dict(count=len(set(classes)),graph=G,sites=dec.sites,classes=classes,epsilon=epsilon,rank=rank,
        labelled=[strong[i] for i in range(len(G))],generic_noop=[generic[i] for i in range(len(G))],
        counts=dict(leaves=len(G),guarded_edges=sum(len(s) for _,s in G),active=len(active),
                    weak_classes=len(set(classes)),labelled_classes=len(set(strong.values())),
                    generic_noop_classes=len(set(generic.values())),max_rank=max(rank),rank_histogram=dict(collections.Counter(rank))))
    assert result['counts']['weak_classes']==4530 and max(rank)==4
    a.output.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps(result['counts']))

if __name__=='__main__':main()
