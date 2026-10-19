#!/usr/bin/env python3
"""Exact hash-consed DAG search over two independently certified dead regions.

No binary-machine state count is inferred from the source node count.
The search changes only two forced-zero tests and their dead positive arms.
"""
from pathlib import Path
from functools import cache
import argparse, json, time

HERE = Path(__file__).resolve().parent

def run():
    ap = argparse.ArgumentParser()
    ap.add_argument('--input', type=Path, default=HERE/'boundary_source_input.json')
    ap.add_argument('--output', type=Path, default=HERE/'dontcare_best.json')
    args=ap.parse_args()
    j=json.loads(args.input.read_text()); S=[tuple(x) for x in j['structures']]
    I={x:i for i,x in enumerate(S)}; root=j['root']
    def cons(a,b):
        p=(a,b)
        if p not in I: I[p]=len(S); S.append(p)
        return I[p]
    @cache
    def live(n):
        x=S[n]
        return 1<<n if isinstance(x[0],str) else (1<<n)|live(x[0])|live(x[1])
    @cache
    def lead(n):
        return 0 if isinstance(S[n][0],str) else 1+lead(S[n][0])
    @cache
    def zr(n):
        return 0 if isinstance(S[n][0],str) else max(1+lead(S[n][0]),zr(S[n][0]),zr(S[n][1]))
    @cache
    def depth(n):
        return 0 if isinstance(S[n][0],str) else 1+max(depth(S[n][0]),depth(S[n][1]))
    @cache
    def paths(n):
        x=S[n]
        if isinstance(x[0],str):return (('',*x),)
        return tuple((str(b)+p,o,r) for b in (0,1) for p,o,r in paths(x[b]))
    def get(path):
        n=root
        for b in path:n=S[n][int(b)]
        return n
    def put(n,path,v):
        if not path:return v
        a,b=S[n]
        return cons(put(a,path[1:],v),b) if path[0]=='0' else cons(a,put(b,path[1:],v))
    original=[i for i in range(len(S)) if (live(root)>>i)&1]
    choices1=[I[('CD',r)] for r in (3,6,7)]+[I[('CB',1)]]
    choices2=[I[('CD',r)] for r in (1,3,5,6,7)]+[I[('CB',1)]]
    left=get('1110'); right=get('1111')
    variants=[]
    for side,sub,path,choices in [(0,left,'1001011000111',choices1),(1,right,'1100',choices2)]:
        out=[];seen=set()
        for test in choices:
            for dead in original:
                n=put(sub,path,cons(test,dead))
                if n in seen:continue
                seen.add(n)
                out.append((n,live(n),zr(n),depth(n),test,dead))
        variants.append(out)
    # Parts to the left of prefix 111 never change.
    outer=[get('0'),get('10'),get('110')]
    base=live(outer[0])|live(outer[1])|live(outer[2])
    best=(live(root).bit_count(),zr(root),depth(root))
    base_score=best; best_data=None;began=time.monotonic();tested=0;eligible=0
    def output(l,r,score):
        n=cons(l[0],r[0])
        for a in reversed(outer):n=cons(a,n)
        assert (live(n).bit_count(),zr(n),depth(n))==score
        pp=paths(n)
        args.output.write_text(json.dumps(dict(status='SOURCE_ONLY',original_root=root,root=n,
          structures=S,score=score,sites=pp,replacements=[dict(path='111010010110001110',value=S[l[4]]),
          dict(path='111010010110001111',subtree=l[5]),dict(path='111111000',value=S[r[4]]),
          dict(path='111111001',subtree=r[5])]),indent=2)+'\n')
    for l in variants[0]:
        for r in variants[1]:
            tested+=1
            run=max(1+lead(l[0]),l[2],r[2],*(1+lead(a) for a in outer),*(zr(a) for a in outer))
            if run>6:continue
            eligible+=1
            mask=base|l[1]|r[1]; missing=0
            pair=(l[0],r[0]); n=I.get(pair)
            if n is None:missing+=1;n=-missing
            else:mask|=1<<n
            d=1+max(l[3],r[3])
            for a in reversed(outer):
                pair=(a,n);n=I.get(pair)
                if n is None:missing+=1;n=-missing
                else:mask|=1<<n
                d=1+max(depth(a),d)
            score=(mask.bit_count()+missing,run,d)
            if score<best:
                best=score;best_data=(l,r)
                print('BEST',score,'tests',tested,'choices',S[l[4]],l[5],S[r[4]],r[5],flush=True)
                output(l,r,score)
    receipt=dict(status='EXHAUSTIVE_WITHIN_LISTED_SUBSTITUTION_FAMILY',base=base_score,best=best,
      original_subtrees=len(original),left_variants=len(variants[0]),right_variants=len(variants[1]),
      tested_pairs=tested,zero_run_eligible_pairs=eligible,seconds=round(time.monotonic()-began,3),
      scope='Two forced-zero instructions; two unreachable subtrees replaced by any original live subtree; no reassociation.')
    args.output.with_name(args.output.stem+'_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)

if __name__=='__main__':run()
