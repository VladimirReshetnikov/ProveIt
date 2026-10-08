#!/usr/bin/env python3
"""Paired observer timings, fresh setup included; NOT knot-recognition timings."""
from pathlib import Path
import sys,json,random,platform,time,statistics,csv,hashlib,argparse
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from terminal_updates.terminal import TerminalKernel,ExactObserver,quotient_cofactor
from terminal_updates.linear import bareiss
from workloads import wheel,triangular_grid,shallow_tree,chain,partition_labels,dynamic_queries,static_queries,children

def exact_dynamic(observer,events):
    tree=children(events);ans=[0]*(len(events)+1)
    def visit(i,state):
        ans[i]=state.value
        for j,a,z in tree[i]:visit(j,state.merged(a,z))
    visit(0,observer.cursor());return ans

def main():
    rng=random.Random(731004);rounds=7;cases=[]
    for b in (8,16,32,64,96):
        g,t=wheel(b);cases.append((f'wheel-{b}-shallow',g,t,shallow_tree(b,8),'field'))
    for w in (6,10):
        g,t=triangular_grid(w);cases.append((f'grid-{w}-shallow',g,t,shallow_tree(len(t),8),'field'))
    g,t=wheel(64,True);cases.append(('signed-wheel-64-chain',g,t,chain(len(t)),'field'))
    for b in (6,10):
        g,t=wheel(b,True);cases.append((f'signed-wheel-{b}-exact',g,t,shallow_tree(b),'exact'))
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only',nargs='*',help='run named cases; persist each case separately')
    parser.add_argument('--resume',action='store_true',help='reuse completed case files')
    args=parser.parse_args()
    parts=ROOT/'results/benchmark_parts';parts.mkdir(exist_ok=True)
    if args.only and any(name not in [c[0] for c in cases] for name in args.only):parser.error('unknown case')
    rows=[]
    for case_index,(name,g,t,ev,mode) in enumerate(cases):
        target=parts/(name+'.json')
        if (args.only and name not in args.only) or (args.resume and target.exists()):
            if target.exists():rows.append(json.loads(target.read_text()))
            continue
        rng=random.Random(731004+case_index)
        labels=partition_labels(len(t),ev)
        reference=[bareiss(quotient_cofactor(g,t,z)) for z in labels]
        expected=[x%1009 for x in reference] if mode=='field' else reference;samples=[]
        def run(arm):
            start=time.perf_counter()
            if mode=='field':
                k=TerminalKernel(g,t,1009);prepared=time.perf_counter()
                result=dynamic_queries(k,ev) if arm=='dynamic' else static_queries(k,labels)
            elif arm=='integer':
                prepared=start;result=[bareiss(quotient_cofactor(g,t,z)) for z in labels]
            else:
                k=ExactObserver(g,t);prepared=time.perf_counter()
                result=exact_dynamic(k,ev) if arm=='dynamic' else [k.query(z) for z in labels]
            end=time.perf_counter()
            if result!=expected:raise AssertionError((name,arm,'incorrect result'))
            return dict(arm=arm,setup=prepared-start,query=end-prepared,total=end-start)
        arms=['static','control','dynamic']+(['integer'] if mode=='exact' else [])
        for arm in arms:run(arm)
        for ri in range(rounds):
            order=arms[:];rng.shuffle(order)
            for arm in order:
                sample=run(arm);sample['round']=ri;samples.append(sample)
        med={a:{metric:statistics.median(x[metric] for x in samples if x['arm']==a)
                for metric in ('setup','query','total')} for a in arms}
        row=dict(name=name,mode=mode,vertices=g.vertices,edges=len(g.edges),terminals=len(t),merge_edges=len(ev),queries=len(labels),
                 graph=dict(vertices=g.vertices,edges=g.edges),terminal_vertices=t,events=ev,medians=med,samples=samples,
                 static_over_dynamic=med['static']['total']/med['dynamic']['total'],static_over_control=med['static']['total']/med['control']['total'],
                 answer_sha256=hashlib.sha256(json.dumps(reference).encode()).hexdigest())
        if mode=='field':
            k=TerminalKernel(g,t,1009);row.update(prime=1009,interior_nullity=k.nullity,dimension=k.dimension)
        else:
            k=ExactObserver(g,t);row.update(primes=k.primes,bound=k.bound,integer_over_dynamic=med['integer']['total']/med['dynamic']['total'])
        row['case_seed']=731004+case_index
        row['source_sha256']={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(list((ROOT/'terminal_updates').glob('*.py'))+[Path(__file__).resolve(),ROOT/'scripts/workloads.py'])}
        target.write_text(json.dumps(row,indent=2)+'\n')
        rows.append(row);print(name,'v',g.vertices,'b',len(t),'Q',len(labels),'static/dynamic',round(row['static_over_dynamic'],3),'control',round(row['static_over_control'],3),flush=True)
    if len(rows)!=len(cases):
        print(f'Persisted {len(rows)} of {len(cases)} cases; run --resume to complete the report.');return
    report=dict(schema='terminal-observer-benchmark-v1',seed=731004,rounds=rounds,
                environment=dict(python=sys.version,platform=platform.platform(),processor=platform.processor()),
                source_sha256={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(list((ROOT/'terminal_updates').glob('*.py'))+[Path(__file__).resolve(), ROOT/'scripts/workloads.py'])},
                scope='Observer microbenchmarks on explicit planar graphs. No upstream recognizer run.',
                timing='Case-specific deterministic shuffle seeds; fresh setup in each arm; one excluded warmup; seven shuffled paired rounds; medians; correctness checked outside recorded intervals.',rows=rows)
    (ROOT/'results/benchmark.json').write_text(json.dumps(report,indent=2)+'\n')
    with (ROOT/'results/benchmark.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['name','v','b','Q','mode','static_ms','control_ms','dynamic_ms','static/dynamic','static/control'])
        for x in rows:w.writerow([x['name'],x['vertices'],x['terminals'],x['queries'],x['mode'],*[1000*x['medians'][a]['total'] for a in ('static','control','dynamic')],x['static_over_dynamic'],x['static_over_control']])
    lines=[r'\begin{tabular}{lrrrrrr}',r'\toprule',r'Workload & $b$ & $Q$ & Static (ms) & Dynamic (ms) & Ratio & Control\\',r'\midrule']
    for x in rows:
        if x['mode']!='field':continue
        lines.append(f"{x['name'].replace('-',' ')} & {x['terminals']} & {x['queries']} & {1000*x['medians']['static']['total']:.2f} & {1000*x['medians']['dynamic']['total']:.2f} & {x['static_over_dynamic']:.2f} & {x['static_over_control']:.2f}\\\\")
    lines += [r'\bottomrule',r'\end{tabular}'];(ROOT/'article/benchmark_table.tex').write_text('\n'.join(lines)+'\n')
if __name__=='__main__':main()
