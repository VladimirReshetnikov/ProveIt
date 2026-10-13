"""Paired completed-query timings; all samples retained, no knot claims."""
import csv,json,platform,statistics,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from ordered_kernel import *
from scripts.fixtures import complete_blocks,ball_blocks,triangular,random_local,complete_chain_decomposition,source_scc_fan
from reference.positive_predecessor.cancellation.deferred import deferred_plan


def encode(obj):
    return json.dumps(obj,sort_keys=True,separators=(',',':'))


def old_query(a):
    old=deferred_plan(a,len(a))
    p={'schema':'ordered-deferral-v1','deferred_rows':old['deferred_rows'],
       'cancellations':old['cancellations'],'cost':old['minimum_deferrals']}
    assert verify_plan(a,p)
    encode({'plan':p,'residual':old['residual']})
    return p,{'subsets':old['subsets_checked']}


def factored_query(a):
    matrix=Matrix.parse(a);labels,adj,_=matrix.graph()
    seen=set();groups=[]
    for v in range(len(labels)):
        if v in seen:continue
        seen.add(v);stack=[v];rows=[]
        while stack:
            x=stack.pop()
            if labels[x][0]=='r':rows.append(labels[x][1])
            for y in adj[x]:
                if y not in seen:seen.add(y);stack.append(y)
        if rows:groups.append(rows)
    deferred=[];moves=[];subsets=0
    for rows in groups:
        rowset=set(rows)
        old=deferred_plan({r:row for r,row in a.items() if r in rowset},len(rows))
        deferred+=old['deferred_rows'];moves+=old['cancellations'];subsets+=old['subsets_checked']
    p={'schema':'ordered-deferral-v1','deferred_rows':sorted(deferred),
       'cancellations':moves,'cost':len(deferred)}
    assert verify_plan(a,p)
    residual=transport_counts(a,p,saturated=True)
    encode({'plan':p,'residual':residual})
    return p,{'subsets':subsets}


def new_query(a,method='ordered'):
    p=optimize_counts(a,method=method)
    assert p['status']=='OPTIMAL_MATRIX_PLAN'
    assert verify_plan(a,p)
    if p['method']=='two-incidence-scc':
        assert verify_two_incidence_optimality(a,p)
    residual=transport_counts(a,p,saturated=True)
    # Serialize the same decision/cancellation/count payload as the baseline;
    # internal DP table statistics and source-SCC proof are retained separately.
    compact={k:p[k] for k in ('schema','deferred_rows','cancellations','cost')}
    encode({'plan':compact,'residual':residual})
    return p,p['stats']


def main(repeats=5):
    cases=[]
    for q in range(1,7): cases.append((f'K33-chain-{q}',complete_blocks(q),'ordered'))
    for q in (1,6): cases.append((f'ball-matrix-blocks-{q}',ball_blocks(q),'two-incidence'))
    for q in (1,3,6): cases.append((f'source-SCC-fan-{q}',source_scc_fan(q),'two-incidence'))
    for n in (4,12): cases.append((f'triangular-{n}',triangular(n),'auto'))
    for seed in (12,77,121): cases.append((f'local-8-seed-{seed}',random_local(8,seed),'ordered'))
    rows=[];raw=[]
    for name,a,method in cases:
        po,so=old_query(a);pf,sf=factored_query(a);pn,sn=new_query(a,method)
        assert po['cost']==pf['cost']==pn['cost']
        old=[];factored=[];new=[]
        for rep in range(repeats):
            # Alternate ordering to reduce one-sided warm-cache bias.
            for kind in (('old','factored','new') if rep%2==0 else ('new','factored','old')):
                begin=time.perf_counter_ns()
                p,s=(old_query(a) if kind=='old' else factored_query(a) if kind=='factored' else new_query(a,method))
                elapsed=(time.perf_counter_ns()-begin)/1e6
                (old if kind=='old' else factored if kind=='factored' else new).append(elapsed)
                raw.append(dict(case=name,replicate=rep,method=kind,milliseconds=elapsed))
        om,fm,nm=statistics.median(old),statistics.median(factored),statistics.median(new)
        row=dict(case=name,rows=len(a),columns=len({c for row in a.values() for c in row}),
                 incidences=sum(map(len,a.values())),cost=pn['cost'],width=sn.get('width','-'),
                 peak_states=sn.get('peak_states',0),subsets=so['subsets'],old_ms=om,factored_ms=fm,new_ms=nm,
                 speedup=om/nm,factored_speedup=fm/nm,factored_subsets=sf['subsets'],method=method)
        rows.append(row); print(row,flush=True)
    (ROOT/'results'/'benchmark_raw.json').write_text(json.dumps(dict(
        python=sys.version,platform=platform.platform(),repeats=repeats,
        scope='matrix parse/optimization/independent replay/passive counts/compact serialization',
        samples=raw),indent=2)+'\n')
    with (ROOT/'results'/'benchmark_summary.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    text='\\begin{tabular}{lrrrrrrr}\n\\toprule\nCase & Rows & Opt. & Width & Old ms & Fact. ms & New ms & Ratio\\\\\n\\midrule\n'
    for x in rows:
        text+=f"{x['case']} & {x['rows']} & {x['cost']} & {x['width']} & {x['old_ms']:.3f} & {x['factored_ms']:.3f} & {x['new_ms']:.3f} & {x['factored_speedup']:.2f}\\\\\n"
    text+='\\bottomrule\n\\end{tabular}\n'
    (ROOT/'results'/'benchmark_table.tex').write_text(text)
    # Scale the width-three query without invoking the exponential baseline.
    stress=[]
    for q in (16,64,256):
        a=complete_blocks(q)
        begin=time.perf_counter_ns()
        td=complete_chain_decomposition(q)
        p=ordered_plan(a,decomposition=td)
        assert p['cost']==q+1 and verify_plan(a,p)
        encoded=len(encode({k:p[k] for k in ('schema','deferred_rows','cancellations','cost')}))
        stress.append(dict(blocks=q,rows=len(a),optimum=p['cost'],width=p['stats']['width'],
                           peak_states=p['stats']['peak_states'],work=p['stats']['work'],
                           plan_bytes=encoded,milliseconds=(time.perf_counter_ns()-begin)/1e6,
                           baseline='not run',scope='supplied-decomposition construction, exact plan, replay, serialization; no passive transport'))
    (ROOT/'results'/'stress.json').write_text(json.dumps(stress,indent=2)+'\n')

if __name__=='__main__':main()
