#!/usr/bin/env python3
"""Independent inventory of exact-source guarded cases, positive clocks and rows.

This audits the outputs of a fresh universal replay; it does not replace that
replay or independently rederive its symbolic transitions.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,sys
from collections import Counter


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in('table','source','runtime','cases','mapping','output'):ap.add_argument('--'+n,type=Path,required=True)
    args=ap.parse_args()
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
    table={}
    for line in args.table.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in table
        table[q,b]=(w,1 if d=='R'else-1,z)
    source=json.loads(args.source.read_bytes());run=json.loads(args.runtime.read_bytes())
    case_raw=args.cases.read_bytes()
    if args.cases.suffix=='.gz':case_raw=gzip.decompress(case_raw)
    cases=json.loads(case_raw)
    assert sha(args.table)==run['table_sha256']=='04b4dbb537306f40f8965ad6a0ee6034e9953f079c233153e9696acdf06c2712'
    assert sha(args.source)==run['sites_sha256']=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
    assert run['status']=='UNIVERSAL_MATHEMATICAL_PASS' and not run['failures']
    expected=[(i,b)for i,(_,op,_)in enumerate(source)for b in((False,True)if op=='CD'else(False,))]
    actual=[(x['site_index'],x['positive'])for x in cases]
    assert actual==expected and len(expected)==6176 and len(source)==4751
    assert run['expected_cases']==run['proved_cases']==len(cases)
    assert len(set(actual))==len(actual)
    states={q for q,b in table};assert len(states)==215 and len(table)==430
    m={int(k):int(v)for k,v in json.loads(args.mapping.read_bytes()).items()}
    for q in states|{254}:
        if q not in m:m[q]=q+1000
    inverse={m[q]:q for q in states|{254}};assert len(inverse)==len(states)+1
    used=set();kinds=Counter();durations=[];motion_constants=set()
    for case in cases:
        d=case['duration'];assert len(d)==13 and all(type(x)is int and x>=0 for x in d)and d[0]>0
        assert len(case['motion'])==13 and all(x==0 for x in case['motion'][1:]);motion_constants.add(case['motion'][0])
        assert sum(case['kinds'].values())==case['symbolic_steps']>0
        assert len(case['rows'])==len(set(tuple(x)for x in case['rows']))
        for q,b in case['rows']:
            assert q in inverse and (inverse[q],b)in table;used.add((inverse[q],b))
        kinds.update(case['kinds']);durations.append(d)
    assert used==set(table)
    out={'status':'INDEPENDENT_FRESH_RUNTIME_RECEIPT_INVENTORY_PASS','table_sha256':sha(args.table),'source_sha256':sha(args.source),
         'runtime_receipt_sha256':sha(args.runtime),'cases_sha256':sha(args.cases),'mapping_sha256':sha(args.mapping),
         'source_leaves':len(source),'decrement_leaves':sum(op=='CD'for _,op,_ in source),'guarded_cases':len(cases),'exact_order_and_unique_coverage':True,
         'working_states':len(states),'transition_rows':len(table),'directly_used_native_rows':len(used),'all_rows_covered':True,
         'symbolic_steps':sum(c['symbolic_steps']for c in cases),'symbolic_rule_kinds':dict(kinds),
         'affine_clock_variables':12,'minimum_positive_constant':min(d[0]for d in durations),'all_clock_coefficients_nonnegative':True,
         'motion_constants':sorted(motion_constants),'native_rows':sorted(used),
         'scope':'Independent audit of all fresh runtime records, table/source identity, every guarded case, all 430 native rows, and affine positive durations. Mathematical universal replay was executed separately with the inherited induction checker; no proof-assistant endpoint claimed.'}
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='native_rows'},indent=2))

if __name__=='__main__':main()
