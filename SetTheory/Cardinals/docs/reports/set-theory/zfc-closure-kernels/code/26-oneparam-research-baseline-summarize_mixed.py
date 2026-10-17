#!/usr/bin/env python3
"""Independently summarize the completed mixed-state construction evidence."""
from pathlib import Path
import collections
import hashlib
import importlib.util
import json

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('mix',ROOT/'mixed_merge_search.py')
mix=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mix)
report=json.loads((ROOT/'mixed_merge_results.json').read_text())
assert report['status']=='completed'
assert report['driver_sha256']==hashlib.sha256((ROOT/'mixed_merge_search.py').read_bytes()).hexdigest()
raw=mix.gc.patched_rows(ROOT/'busy-beaver/ZF/m254/machine/zfc_254.tm')
table={(str(q),b):(w,d,str(n))for(q,b),(w,d,n)in raw.items()}
counts=collections.Counter()
reasons=collections.Counter()
seen=set()
for record in report['candidates']:
    p,q,b=str(record['deleted_old']),str(record['retained_old']),record['read_from_deleted']
    assert (p,q,b)not in seen
    seen.add((p,q,b))
    def mapped(row):
        w,d,n=row
        return w,d,q if n==p else n
    genuine=all(mapped(table[p,c])!=mapped(table[q,c])for c in(0,1))
    counts['constructions']+=1
    counts['genuinely_mixed_constructions']+=int(genuine)
    counts[record['outcome']]+=1
    if record['outcome']!='protected_row_changed':
        counts['protected_admissible_constructions']+=1
        counts['protected_admissible_genuinely_mixed']+=int(genuine)
    failure=record.get('first_failure',{})
    if failure:
        if failure.get('detail')=='fuel':reason='fuel_exhaustion'
        elif failure.get('reason')=='unexpected_status':reason='unexpected_terminal_status'
        else:reason='symbolic_geometry_failure'
        reasons[reason]+=1
summary={
    'public_table_sha256':report['public_table_sha256'],
    'public_pin':report['public_pin'],
    'driver_sha256_checked':True,
    'summary_driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'counts':dict(counts),'failure_categories':dict(reasons),
    'eligible_states':len(report['eligible_old_labels']),
    'affine_case_fuel':report['fuel_per_case'],'baseline_cases':report['baseline_cases'],
    'survivors':report['survivors'],
    'warning':'Bounded failure to certify the fixed runtime interface, not impossibility or a state lower bound.',
    'excludes':'Both the dispatcher96 and all28 box states as members of the amalgamated pair.',
    'no_new_kernel_verified_machine':True,
    'raw_results_sha256':hashlib.sha256((ROOT/'mixed_merge_results.json').read_bytes()).hexdigest()
}
(ROOT/'mixed_merge_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
