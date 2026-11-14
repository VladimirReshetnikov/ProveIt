#!/usr/bin/env python3
"""Long-sequence, seeded source-DAG reassociation experiment.

The acceptance objective is a source grammar size, never a TM state count.
Every reported improving tree is checked against the complete original CFG.
"""
import argparse, importlib.util, json, math, random, time, sys
from collections import Counter
from functools import lru_cache
from pathlib import Path

BASE=Path(__file__).resolve().parents[2]
SRC=Path(__file__).with_name('rotation_core.py')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--steps',type=int,default=100000)
    ap.add_argument('--seed',type=int,default=1)
    ap.add_argument('--temp',type=float,default=.16)
    ap.add_argument('--restart',type=int,default=5000)
    ap.add_argument('--output',type=Path,default=BASE/'research/anneal')
    ap.add_argument('--zero-weight',type=float,default=0.0)
    ap.add_argument('--max-zero',type=int,default=10000)
    ap.add_argument('--max-depth',type=int,default=45)
    ap.add_argument('--input',type=Path)
    ap.add_argument('--physical-estimate',action='store_true')
    ap.add_argument('--ax-only',action='store_true')
    ap.add_argument('--helper-pattern',action='store_true')
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    spec=importlib.util.spec_from_file_location('rot',SRC)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    baseline=m.root; baseline_graph=m.graph(baseline)
    baseline_ids=set(m.unique(baseline))
    pattern_left,pattern_right=m.env['node32'],m.env['node17']
    aliases=[]
    outside=set()
    if args.physical_estimate:
        alloc=SRC.parent/'allocator-screen';sys.path.insert(0,str(alloc))
        import source_language as sl, build221 as bl
        old=sl.tree(json.loads((alloc/'original.json').read_text()))
        groups,_=bl.decoder_map(bl.read_table((alloc/'pa196.native.tm').read_bytes()),old)
        opmap={'CI':'inc','CD':'dec','CB':'breakTo','CC':'continueTo','CH':'halt'}
        def convert(t):
            if sl.leaf(t):return m.interned((opmap[t[0]],0 if t[1] is None else t[1]))
            return m.node(convert(t[0]),convert(t[1]))
        aliases=[{convert(n) for n in ns} for ns in groups.values()]
    if args.ax_only:
        allowed=set(m.unique(m.env['x67']))
        frozen=set()
        for name in ['node49','node55','node58','node70','node65','node72','node75','node150']:
            frozen.update(m.unique(m.env[name]))
        outside=baseline_ids-allowed | frozen
    rng=random.Random(args.seed); start=time.monotonic()
    @lru_cache(None)
    def shape(t):
        if not m.isnode(t):return 0,0,0
        _,a,b=m.store[t]; da,pa,za=shape(a);db,pb,zb=shape(b)
        return max(da,db)+1,pa+1,max(pa+1,za,zb)
    def cost(t):
        d,p,z=shape(t)
        seen=m.unique(t)
        if args.physical_estimate:
            represented=set().union(*(a&seen for a in aliases))
            used=sum(bool(a&seen) for a in aliases)
            score=49+used+sum(m.isnode(n) for n in seen-represented)
        else:score=m.metric(t)
        if args.helper_pattern:
            found=False
            for n in seen:
                if not m.isnode(n):continue
                _,a,b=m.store[n]
                if m.isnode(a) and m.isnode(b) and m.store[a][1]==pattern_left and m.store[b][1]==pattern_right:
                    found=True;break
            if not found:score+=1
        return score+args.zero_weight*max(0,z-5)+.001*max(0,d-38)
    def dump_tree(t,path):
        opmap={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
        rows=[]
        for p,x in m.leaf_occurrences(t):
            op,arg=m.store[x];rows.append([''.join(map(str,p)),opmap[op],None if op=='halt' else arg])
        path.write_text(json.dumps(rows,separators=(',',':'))+'\n')
        return rows
    def parse(rows):
        opmap={'CI':'inc','CD':'dec','CB':'breakTo','CC':'continueTo','CH':'halt'}
        paths={p:(o,a) for p,o,a in rows}
        def rec(p):
            if p in paths:
                o,a=paths[p];return m.interned((opmap[o],0 if a is None else a))
            return m.node(rec(p+'0'),rec(p+'1'))
        return rec('')
    if args.input: baseline=parse(json.loads(args.input.read_text()));baseline_graph=m.graph(baseline)
    best=cur=baseline;bestcost=curcost=cost(cur)
    accepted=0; found=[]; counts=Counter();savecount=0
    variants={}
    for i in range(args.steps):
        if i and i%args.restart==0:
            cur=baseline if rng.random()<.5 else best;curcost=cost(cur)
        allowed_root=cur
        if args.ax_only:
            for bit in (1,0,1,0,1,0,0,1):allowed_root=m.store[allowed_root][1+bit]
        nodes=[x for x in m.unique(allowed_root) if m.isnode(x) and x not in outside]
        possibilities=[]
        # Sample an eligible node without constructing whole-tree neighbours.
        for k in range(20):
            old=rng.choice(nodes); possibilities=list(m.transforms(old))
            if possibilities:break
        if not possibilities:continue
        direction,new=rng.choice(possibilities)
        changed=m.rewrite(cur,old,new)
        sh=shape(changed)
        if sh[0]>args.max_depth or sh[2]>args.max_zero:continue
        cc=cost(changed); delta=cc-curcost
        if delta<=0 or rng.random()<math.exp(-delta/args.temp):
            cur=changed;curcost=cc;accepted+=1
            if cc<bestcost-1e-9:
                best=cur;bestcost=cc
                if m.graph(best)!=baseline_graph:raise ValueError('Full source CFG changed')
                savecount+=1;filename=f'best_{args.seed}_{savecount}.json'
                dump_tree(best,args.output/filename)
                item={'step':i+1,'nodes':m.metric(best),'shape':shape(best),'cost':cc,'source':filename}
                found.append(item);print(json.dumps(item),flush=True)
            if m.metric(cur)<=159 or (args.physical_estimate and cc<197):
                variants.setdefault(cur,(m.metric(cur),shape(cur)))
        counts[m.metric(cur)]+=1
        if (i+1)%10000==0:
            print(json.dumps({'step':i+1,'accepted':accepted,'best':bestcost,'current':curcost,'arena':len(m.store),'seconds':round(time.monotonic()-start,2)}),flush=True)
        # Compact hash-consing arena to keep memory bounded, preserving saved trees.
        if len(m.store)>350000:
            keep=[baseline,best,cur]
            if len(variants)>1500:variants=dict(list(variants.items())[-1500:])
            keep+=list(variants)+list(outside)+[t for a in aliases for t in a]+[pattern_left,pattern_right]
            oldstore=m.store; mapping={}
            m.store=[];m.intern={};m.bound.cache_clear();shape.cache_clear()
            def copy(t):
                if t in mapping:return mapping[t]
                row=oldstore[t]
                v=m.node(copy(row[1]),copy(row[2])) if row[0]=='node' else m.interned(row)
                mapping[t]=v;return v
            allnew=[copy(t) for t in keep]
            baseline,best,cur=allnew[:3]
            variants={mapping[t]:v for t,v in variants.items()}
            outside={mapping[t] for t in outside}
            aliases=[{mapping[t] for t in a} for a in aliases]
            pattern_left,pattern_right=mapping[pattern_left],mapping[pattern_right]
    dump_tree(best,args.output/f'best_{args.seed}.json')
    # Record distinct low-cost witnesses for downstream physical allocation.
    vdir=args.output/f'variants_{args.seed}';vdir.mkdir(exist_ok=True)
    for j,(t,(n,sh)) in enumerate(sorted(variants.items(),key=lambda kv:(kv[1][0],kv[1][1][2],kv[1][1][0]))[:200]):
        dump_tree(t,vdir/f'{j:03d}.json')
    receipt={'seed':args.seed,'steps':args.steps,'temperature':args.temp,'restart':args.restart,'zero_weight':args.zero_weight,
             'accepted':accepted,'best_internal_nodes':m.metric(best),'best_shape':shape(best),'found':found,
             'current_size_histogram':dict(counts),'seconds':round(time.monotonic()-start,3),
             'scope':'Seeded finite source-grammar search; no physical state reduction or PA proof follows.'}
    (args.output/f'receipt_{args.seed}.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)

if __name__=='__main__':main()
