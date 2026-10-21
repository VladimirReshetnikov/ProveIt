#!/usr/bin/env python3
import argparse,json,subprocess
from functools import cache
from pathlib import Path
import encoding_support as x
from semantic_grammar import atoms,dag
s,b,z,W=x.s,x.b,x.z,x.W

@cache
def shape(n):
    if s.leaf(n):return 0,0
    a,bb=shape(n[0]),shape(n[1]);lead=1+a[0]
    return lead,max(lead,a[1],bb[1])


def parse_one(tree,reference,path,K,seed,reference_only=False):
    region=s.subtree(tree,path);aa=atoms(region)
    nodes=[];nid={}
    def index(n):
        if n not in nid:
            if not s.leaf(n):index(n[0]);index(n[1])
            nid[n]=len(nodes);nodes.append(n)
    index(reference);reference_nodes=set(nid);index(tree)
    seq=tuple(aa);matches=[]
    limit=K-(len(path)-len(path.rstrip('0')))
    assert limit>=0,(path,limit)
    for n in nodes:
        if reference_only and n not in reference_nodes:continue
        if n==region or s.boundary(n)!=(0,0,False)or shape(n)[1]>K:continue
        word=atoms(n);lead=shape(n)[0]
        for i in range(len(seq)-len(word)+1):
            if seq[i:i+len(word)]==word:matches.append((i,i+len(word),lead,nid[n]))
    inp=f'{len(seq)} {limit} {K} {len(matches)} {seed}\n'+''.join(' '.join(map(str,m))+'\n'for m in matches)
    r=subprocess.run([str(W/'closed_parse')],input=inp,text=True,capture_output=True,check=True)
    data=json.loads(r.stdout)
    if 'error'in data:raise ValueError(data)
    def decode(n):return nodes[n]if isinstance(n,int)else(decode(n[0]),decode(n[1]))
    new=decode(data['tree']);assert atoms(new)==aa
    assert shape(new)[1]<=K and shape(new)[0]<=limit
    return s.replace(tree,path,new),{'path':path,'atoms':len(aa),'new_join_cost':data['cost']}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--sites',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True);ap.add_argument('--path')
    ap.add_argument('--maxzero',type=int,default=6);ap.add_argument('--seed',type=int,default=0)
    args=ap.parse_args()
    base=W/'K220_Construction_2026-10-20/machine'
    reference=s.tree(json.loads((base/'sites220.json').read_text()))
    T=b.read_table((base/'k220.native.tm').read_bytes())
    initial=s.tree(json.loads(args.sites.read_text()));tree=initial
    paths=[]
    def walk(n,p=''):
        if s.leaf(n):return
        if s.boundary(n)==(0,0,False)and len(atoms(n))>1:paths.append(p);return
        walk(n[0],p+'0');walk(n[1],p+'1')
    if args.path is None:walk(tree)
    else:paths=[args.path]
    receipts=[]
    for path in paths:
        tree,r=parse_one(tree,reference,path,args.maxzero,args.seed);receipts.append(r)
        print(r,flush=True)
    rr=s.sites(tree);oldrows=s.sites(initial)
    assert [r[1:]for r in rr]==[r[1:]for r in oldrows]
    assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)==s.graph_arithmetic(oldrows)[0]
    rec={'metrics':s.metrics(tree),'closed_reparses':receipts,'primitive_word_and_CFG_unchanged':True}
    args.out.mkdir(parents=True,exist_ok=True);(args.out/'sites.json').write_bytes(s.compact(rr))
    try:
        U,c=z.compile_tree(T,reference,tree);rec['compiler']=c
        (args.out/'candidate.tm').write_bytes(b.table_bytes(U))
    except Exception as exc:rec['error']=repr(exc)
    (args.out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)


if __name__=='__main__':main()
