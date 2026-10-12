"""Reproducible, finite independent comparisons. Each family writes its own evidence."""
import argparse,random,time,json,platform,collections
from pathlib import Path
from cycle_kernel import Graph,close,power_explicit,kernel_power,normal_form
from cycle_kernel.partitions import boundary_partition,stabilize,verify_stabilization,product as part_product,rank
from cycle_kernel.oracle import graph_signature,signature_power,enumerate_signature
from cycle_kernel.validation import source_cell_cover
from cycle_kernel.query import solve_graph,closed_source_is_cubic
from cycle_kernel.replay import verify_graph
from cycle_kernel.grammar import evaluate

ROOT=Path(__file__).resolve().parent

def partitions(n):
    a=[0]*n
    def visit(i,m):
        if i==n:yield tuple(a);return
        for x in range(m+2):a[i]=x;yield from visit(i+1,max(m,x))
    yield from visit(1,0)

def reference_product(a,b):
    # Independent connected-set closure; no call to the production DSU.
    w=len(a)//2;blocks=[]
    for off,p in ((0,a),(w,b)):
        for c in set(p):blocks.append({off+i for i,x in enumerate(p) if x==c})
    merged=[]
    while blocks:
        s=blocks.pop();changed=True
        while changed:
            changed=False;keep=[]
            for t in blocks:
                if s&t:s|=t;changed=True
                else:keep.append(t)
            blocks=keep
        merged.append(s)
    vertices=list(range(w))+list(range(2*w,3*w));labels=[];seen={}
    for v in vertices:
        c=next(i for i,s in enumerate(merged) if v in s)
        labels.append(seen.setdefault(c,len(seen)))
    return tuple(labels)

def partition_audit():
    count=0;max_s={}
    for w in range(1,5):
        ms=0
        for p in partitions(2*w):
            cert=stabilize(p);assert verify_stabilization(p,cert)
            a=p
            for _ in range(cert['s']-1):a=reference_product(a,p)
            b=reference_product(a,p)
            assert reference_product(b,tuple(cert['divisor']))==a
            rr=rank(a)
            for _ in range(w+3):a=reference_product(a,p);assert rank(a)==rr
            count+=1;ms=max(ms,cert['s'])
        max_s[w]=ms
    return dict(partitions=count,max_stabilization=max_s,reference='connected-set closure, independent of production DSU')

def signature_audit():
    rng=random.Random(2026101217);hist=collections.Counter();kinds=collections.Counter();entries=0;reductions=0
    for trial in range(6000):
        w=1+trial%3;nv=2*w+rng.randrange(4)
        edges=tuple((rng.randrange(nv),rng.randrange(nv)) for _ in range(rng.randrange(2*nv+1)))
        tile=Graph(nv,edges,tuple(range(w)),tuple(range(w,2*w)))
        n=rng.choice([3,4,7,13,21,42,101,2**32+13]);k=trial%5
        g,meta=kernel_power(tile,n,k,connected_fastpath=False)
        assert graph_signature(g,k)==signature_power(tile,n,k), (trial,tile,n,k)
        entries+=4*(1<<(2*w));hist[meta['stabilization']['s']]+=1
        kinds.update(meta.get('normalization',{}).get('seam_kinds',{}))
        reductions+=len(g.edges)<n*len(tile.edges)
    return dict(models=6000,signature_entries=entries,seed=2026101217,thresholds=[0,1,2,3,4],
                stabilization_histogram=dict(hist),seam_component_totals=dict(kinds),strict_edge_reductions=reductions,
                reference='local coloring enumeration and exact transfer power versus graph variable elimination')

def geometry_audit():
    rng=random.Random(2026101229);covers=0;edgecells=0;equalities=0;cubic=0;full_queries=0
    for trial in range(1800):
        w=1+trial%5;nv=2*w+rng.randrange(4)
        t=Graph(nv,tuple((rng.randrange(nv),rng.randrange(nv)) for _ in range(rng.randrange(2*nv+1))),
                tuple(range(w)),tuple(range(w,2*w)))
        s=stabilize(boundary_partition(t))['s'];nf=normal_form(power_explicit(t,s))
        info=source_cell_cover(nf,3+trial%6);assert info['valid'];covers+=1
        edgecells+=info['edges'];equalities+=info['equalities']
    for trial in range(700):
        w=1+trial%5;private=rng.randrange(4)
        if (w+private)%2:private+=1
        nv=2*w+private;stubs=[]
        for i in range(w):
            d=rng.randrange(4);stubs.extend([i]*d);stubs.extend([w+i]*(3-d))
        for i in range(2*w,nv):stubs.extend([i]*3)
        rng.shuffle(stubs);edges=tuple(zip(stubs[::2],stubs[1::2]))
        t=Graph(nv,edges,tuple(range(w)),tuple(range(w,2*w)))
        assert closed_source_is_cubic(t)
        n=rng.choice([3,7,19,101,2**128+1]);g,_=kernel_power(t,n);cg=close(g)
        degrees=[0]*cg.n
        for a,b in cg.edges:degrees[a]+=1;degrees[b]+=1
        assert all(d==3 for d in degrees);cubic+=1
        if trial<150:
            p=solve_graph(cg);assert verify_graph(cg,p);full_queries+=1
    return dict(source_covers=covers,covered_edge_occurrences=edgecells,covered_seam_equalities=equalities,
                cubic_source_powers=cubic,independently_replayed_graph_queries=full_queries,seed=2026101229)

def nested_audit():
    rng=random.Random(2026101231);count=0;entries=0
    for trial in range(250):
        w=1+trial%2;nv=2*w+rng.randrange(2)
        def randleaf():
            e=tuple((rng.randrange(nv),rng.randrange(nv)) for _ in range(rng.randrange(nv+2)))
            return {'op':'leaf','tile':Graph(nv,e,tuple(range(w)),tuple(range(w,2*w))).to_dict()}
        tree={'op':'power','exponent_hex':hex(rng.randrange(2,8)),
              'child':{'op':'serial','children':[{'op':'power','exponent_hex':hex(rng.randrange(2,8)),'child':randleaf()},randleaf()]}}
        a,stats=evaluate(tree);b,_=evaluate(tree,compress=False)
        assert graph_signature(a)==graph_signature(b);count+=1;entries+=4*(1<<(2*w))
    return dict(expression_trees=count,signature_entries=entries,seed=2026101231,
                reference='literal expanded expression versus recursively reduced expression, exact graph elimination')

def main():
    p=argparse.ArgumentParser();p.add_argument('family',choices=['partitions','signatures','geometry','nested']);args=p.parse_args()
    fun={'partitions':partition_audit,'signatures':signature_audit,'geometry':geometry_audit,'nested':nested_audit}[args.family]
    start=time.perf_counter();result=fun();result.update(family=args.family,seconds=time.perf_counter()-start,
                python=platform.python_version(),platform=platform.platform(),status='PASS')
    (ROOT/('audit-'+args.family+'.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
