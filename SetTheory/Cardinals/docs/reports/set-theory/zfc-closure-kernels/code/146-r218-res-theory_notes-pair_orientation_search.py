#!/usr/bin/env python3
"""Formula-constructor Cantor orientations without a stack-swap operation."""
from pathlib import Path
import argparse
import itertools
import json
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
import tag_permutation_search as t


def run(tree,reg,budget):
    budget[0]-=1
    if budget[0]<0:raise ValueError('finite test budget')
    if t.s.leaf(tree):
        op,r=tree
        if op=='CI':reg[r]+=1;return'N',0
        if op=='CD':
            if reg[r]==0:return'B',1
            reg[r]-=1;return'N',0
        return {'CB':'B','CC':'C','CH':'H'}[op],r or 0
    while True:
        k,v=run(tree[0],reg,budget)
        if k=='B':return('N',0)if v==1 else('B',v-1)
        if k!='N':return k,v
        k,v=run(tree[1],reg,budget)
        if k=='C':
            if v==1:continue
            return'C',v-1
        return k,v


def finite_check():
    P=lambda x,y:(x+y)*(x+y+1)//2+y
    count=0
    for x,y,tail in itertools.product(range(7),range(7),range(7)):
        for reversed in (False,True):
            r=[17,y,P(x,tail),19,23,29,0,0,31]
            out=r.copy();out[1]=4*(P(y,x)if reversed else P(x,y));out[2]=tail
            exit=run(t.REVERSED_CORE if reversed else t.CORE,r,[10000000])
            assert exit==('N',0)and r==out,(x,y,tail,reversed,exit,r,out)
            count+=1
    return dict(status='PAIR_ORIENTATION_LOCAL_FINITE_AUDIT_PASS',tests=count,
                core_leaf_count=27,pair_offset=[11,21],
                proof='The 10-leaf pair block is the literal register1/register6 conjugate of the inherited arbitrary-register pair162 contract. Pop and multiply-by4 blocks are unchanged. The finite tests only check the implementation.')


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--tags',action='store_true');args=ap.parse_args()
    out=t.ROOT/'theory_notes/orientation_variants';out.mkdir(exist_ok=True)
    (out/'local_audit.json').write_text(json.dumps(finite_check(),indent=2)+'\n')
    objective=t.a.hw.make(t.a.table,t.a.old)[0]
    results=[];best=999;start=time.monotonic();seen=set()
    tagslist=list(itertools.permutations((0,2,3)))if args.tags else [(0,2,3)]
    policies=list(itertools.product(range(3),range(3),range(2)))if args.tags else [(0,0,0)]
    for bits in itertools.product((0,1),repeat=4):
        reverse={m for m,b in zip((119,180,181,182),bits)if b}
        local=[]
        for values in tagslist:
            tags=dict(zip((119,180,182),values));tags[181]=1
            for add,delete,shape in policies:
                tree,binding=t.edit(tags,add,delete,shape,reverse)
                if tree in seen:continue
                seen.add(tree)
                score=objective(tree)
                row=dict(orientations=dict(zip(('I','Q','R','E'),bits)),tags=dict(zip(('I','Q','E'),values)),addition_policy=add,deletion_policy=delete,increment_shape=shape,hardware_lower_bound=score,metrics=t.s.metrics(tree))
                results.append(row);local.append(row)
                if score['cost_lower_bound']<best:
                    best=score['cost_lower_bound'];print('BEST',json.dumps(row),flush=True)
                if score['cost_lower_bound']<=221:
                    d=out/('r'+''.join(map(str,bits))+'_t'+''.join(map(str,values))+f'_a{add}_d{delete}_s{shape}');d.mkdir(exist_ok=True)
                    (d/'sites.json').write_bytes(t.s.compact(t.s.sites(tree)))
                    (d/'receipt.json').write_text(json.dumps(dict(**row,constructor_bindings=binding),indent=2)+'\n')
        if local:print('ORIENTATION',bits,'distinct',len(local),'best',min(r['hardware_lower_bound']['cost_lower_bound']for r in local),'seconds',time.monotonic()-start,flush=True)
    (out/('joint_results.json'if args.tags else 'results.json')).write_text(json.dumps(results,indent=2)+'\n')
    print('DONE',len(results),'best',best,'seconds',time.monotonic()-start,flush=True)


if __name__=='__main__':main()
