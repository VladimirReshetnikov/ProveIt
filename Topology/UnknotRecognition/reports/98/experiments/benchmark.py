"""Paired complete graph queries: gauge atlas vs explicit-root response baseline.

Same supplied grammar and identical serialized closed-root exact response.
The gauge path additionally constructs origins for its complete certificate.
No native knot or source-geometric timings are claimed.
"""
import csv,gc,json,platform,statistics,sys,time
from pathlib import Path
from gauge_cuts import compile_grammar
from checker import verify_packet,validate_source
from fixtures import component_fan,permutation_power
from reference import dense_compile

OUT=Path('data')
def gauge(g):
    p=compile_grammar(g)
    payload=json.dumps(sorted((r[0],r[1],r[3]) for r in p['atlases'][-1]['rows']),separators=(',',':'))
    return payload,{'peak_states':max(s['states'] for s in p['statistics']),
                    'total_states':sum(s['states'] for s in p['statistics']),'candidate_work':p['candidate_work']}
def dense(g):
    validate_source(g);p=dense_compile(g)
    payload=json.dumps(sorted(p['tables'][-1]),separators=(',',':'))
    return payload,{k:p[k] for k in ('peak_states','total_states','candidate_work')}
def measured(f,g):
    gc.collect();t=time.perf_counter_ns();value=f(g);return (time.perf_counter_ns()-t)/1e6,value

def main():
    raw=[];summary=[]
    cases=[('component_fan',c,component_fan(c)) for c in [1,2,4,8,12,16,18]]
    cases += [('permuted_unit_channels',d,permutation_power(2,d)) for d in [1,4,16,64]]
    for family,param,g in cases:
        first,a=gauge(g);second,b=dense(g);assert first==second
        ga=[];de=[]
        for repeat in range(5):
            order=[('gauge',gauge),('explicit',dense)] if repeat%2==0 else [('explicit',dense),('gauge',gauge)]
            values={}
            for label,f in order:
                ms,result=measured(f,g);values[label]=result[0]
                (ga if label=='gauge' else de).append(ms)
                raw.append({'family':family,'parameter':param,'repeat':repeat,'method':label,'milliseconds':ms})
            assert values['gauge']==values['explicit']
        t=time.perf_counter();replay=verify_packet(compile_grammar(g),g);rp=(time.perf_counter()-t)*1e3
        row={'family':family,'parameter':param,'gauge_ms':statistics.median(ga),'explicit_ms':statistics.median(de),
             'ratio_explicit_over_gauge':statistics.median(de)/statistics.median(ga),
             'gauge_peak_rows':a['peak_states'],'explicit_peak_rows':b['peak_states'],
             'gauge_candidate_work':a['candidate_work'],'explicit_candidate_work':b['candidate_work'],
             'compile_plus_replay_ms_single':rp}
        summary.append(row);print(row,flush=True)
    # Same-operation controls: variability is not a claimed algorithmic gain.
    controls=[];g=component_fan(12)
    for trial in range(5):
        a,ra=measured(gauge,g);b,rb=measured(gauge,g);assert ra[0]==rb[0]
        controls.append({'trial':trial,'first_ms':a,'second_ms':b,'ratio':b/a})
    with (OUT/'benchmark_raw.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(raw[0]));w.writeheader();w.writerows(raw)
    result={'python':sys.version,'platform':platform.platform(),'repeats':5,'summary':summary,'AA_controls':controls,
            'scope':'same supplied abstract graph grammar, complete exact root response; no native geometry or knot recognition'}
    (OUT/'benchmark.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
