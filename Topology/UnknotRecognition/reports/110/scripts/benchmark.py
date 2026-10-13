#!/usr/bin/env python3
"""Paired component measurements, not whole-knot performance claims."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
import json,time,statistics,random,platform,gc
from itertools import combinations
from pivotwidth import Instance,optimize,replay
from pivotwidth.transfer import power_certificate
from pivotwidth.transfer_verify import verify_power
from examples.templates import chain_matrix,chain_decomposition,defect_tile


def enumerate_deferrals(a):
    m,n=len(a),len(a[0]) if a else 0;trials=0
    for d in range(m+1):
        for deferred in combinations(range(m),d):
            trials+=1;active=set(range(m))-set(deferred)
            while active:
                hit=next((i for j in range(n) for i in active
                          if a[i][j]==1 and sum(a[k][j] for k in active)==1),None)
                if hit is None:break
                active.remove(hit)
            if not active:return d,trials
    raise AssertionError('the all-deferred set is always feasible')


def run():
    rng=random.Random(91681);records=[]
    for q in range(1,8):
        a,w=chain_matrix(q);dec=chain_decomposition(q)
        def dp():
            x=optimize(Instance.from_dense(a,w),dec);replay(a,w,x)
            assert x['deferred_weight']==q
            return x
        def old():
            d,trials=enumerate_deferrals(a);assert d==q
            return trials
        dp();old();samples={'ordered_dp_and_replay':[],'deferred_set_enumeration':[]}
        last=None;trials=None
        for rep in range(5):
            order=list(samples);rng.shuffle(order)
            for arm in order:
                start=time.perf_counter_ns()
                if arm=='ordered_dp_and_replay':last=dp()
                else:trials=old()
                elapsed=(time.perf_counter_ns()-start)/1e6;samples[arm].append(elapsed)
        med={k:statistics.median(v) for k,v in samples.items()}
        records.append({'q':q,'rows':2*q,'columns':2*q+1,'width':2,
                        'deferred_weight':q,'enumerated_subsets':trials,'samples_ms':samples,
                        'medians_ms':med,'ratio_enumeration_over_dp':med['deferred_set_enumeration']/med['ordered_dp_and_replay'],
                        'dp_stats':last['stats']})
        print('chain',q,med,flush=True)
    powers=[]
    for bits in [16,64,256,1024]:
        samples=[];size=0;cert=None
        for rep in range(5):
            start=time.perf_counter_ns()
            cert=power_certificate(defect_tile(3,7),1<<bits);verify_power(cert)
            text=json.dumps(cert,separators=(',',':'));size=len(text.encode())
            samples.append((time.perf_counter_ns()-start)/1e6)
        powers.append({'exponent':f'2^{bits}','exponent_bits':bits+1,'samples_ms':samples,
                       'median_ms':statistics.median(samples),'serialized_bytes':size,
                       'stats':cert['stats']})
    data={'python':sys.version,'platform':platform.platform(),'seed':91681,'repetitions':5,
          'matrix_benchmarks':records,'power_benchmarks':powers,
          'measurement_scope':{'ordered_dp_and_replay':'Given dense matrix and supplied path decomposition: parse matrix, validate decomposition, optimize, independent feasible-plan replay.',
                               'deferred_set_enumeration':'Same dense matrix: increasing-size deferred-set enumeration with complete private-peeling feasibility checks; returns optimal unit-weight value. Independent reference baseline, not copied native code.',
                               'power':'Compile template, construct power/table certificate, independently replay, serialize to JSON; no explicit graph expansion.'}}
    (ROOT/'results'/'benchmarks.json').write_text(json.dumps(data,indent=2)+'\n')
    lines=['\\begin{tabular}{rrrrrr}', '\\toprule',
           '$q$ & Rows & Tested sets & Enumeration (ms) & Ordered DP (ms) & Ratio \\\\', '\\midrule']
    for r in records:
        md=r['medians_ms']
        lines.append(f"{r['q']} & {r['rows']} & {r['enumerated_subsets']:,} & {md['deferred_set_enumeration']:.3f} & {md['ordered_dp_and_replay']:.3f} & {r['ratio_enumeration_over_dp']:.2f} \\\\")
    lines+=['\\bottomrule','\\end{tabular}']
    (ROOT/'article'/'benchmark_table.tex').write_text('\n'.join(lines)+'\n')
    lines=['\\begin{tabular}{rrrrr}', '\\toprule',
           'Copies & Proof nodes & Max bag & JSON bytes & Total (ms) \\\\', '\\midrule']
    for r in powers:
        bits=r['exponent_bits']-1
        lines.append(f"$2^{{{bits}}}$ & {r['stats']['proof_nodes']} & {r['stats']['max_bag']} & {r['serialized_bytes']:,} & {r['median_ms']:.3f} \\\\")
    lines+=['\\bottomrule','\\end{tabular}']
    (ROOT/'article'/'power_table.tex').write_text('\n'.join(lines)+'\n')
    last=records[-1];first=records[0];power=powers[-1]
    values={'EnumSeven':f"{last['medians_ms']['deferred_set_enumeration']:.1f}",
            'DPSeven':f"{last['medians_ms']['ordered_dp_and_replay']:.3f}",
            'RatioSeven':f"{last['ratio_enumeration_over_dp']:.0f}",
            'EnumOne':f"{first['medians_ms']['deferred_set_enumeration']:.3f}",
            'DPOne':f"{first['medians_ms']['ordered_dp_and_replay']:.3f}",
            'HugeMillis':f"{power['median_ms']:.1f}",
            'HugeBytes':f"{power['serialized_bytes']:,}"}
    (ROOT/'article'/'metrics.tex').write_text(''.join(
        '\\newcommand{\\'+k+'}{'+v+'}\n' for k,v in values.items()))


if __name__=='__main__':run()
