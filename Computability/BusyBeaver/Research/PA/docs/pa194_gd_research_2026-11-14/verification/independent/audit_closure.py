#!/usr/bin/env python3
"""Audit branch coverage, affine clocks, literal-row use and frozen identities."""
from pathlib import Path
import collections,hashlib,json
HERE=Path(__file__).resolve().parent

def audit(path):
    sites=json.loads((path/'sites.json').read_text())
    raw=(path/'independent/contracts.json').read_bytes();cases=json.loads(raw)
    expected={(i,p)for i,(_,op,_)in enumerate(sites)for p in([False,True]if op=='dec'else[False])}
    observed=[(c['site'],c['positive'])for c in cases]
    assert len(observed)==len(set(observed)) and set(observed)==expected
    assert all(len(c['duration'])==13 and all(isinstance(n,int)and n>=0 for n in c['duration'])and c['duration'][0]>0 for c in cases)
    halt=[c for c in cases if sites[c['site']][1]=='halt']
    live=[c for c in cases if sites[c['site']][1]!='halt']
    assert len(halt)==1 and halt[0]['duration']==[3]+[0]*12
    assert all(c['motion']==[0]*13 for c in live)
    counts=collections.Counter(tuple(r)for c in cases for r in c['rows'])
    mapping={int(k):v for k,v in json.loads((HERE/'literal/vendor/legacy_mapping.json').read_text()).items()}
    native_rows=[]
    for line in(path/'machine.native.tm').read_text().splitlines():
        q,b,*_=line.split();q,b=int(q),int(b);mapping.setdefault(q,q+10000);native_rows.append((q,b))
    unused=[r for r in native_rows if(mapping[r[0]],r[1])not in counts]
    return {'family':path.name,'status':'PASS','all_source_branch_cases_present_once':True,'source_sites':len(sites),'source_outcomes':len(cases),'nonhalting_outcomes':len(live),'halting_outcomes':len(halt),'all_affine_duration_coefficients_nonnegative':True,'minimum_positive_duration_constant':min(c['duration'][0]for c in cases),'nonhalting_affine_head_motion_zero':True,'halting_duration':3,'literal_rows_used_in_symbolic_cases':len(native_rows)-len(unused),'unused_literal_rows':unused,'minimum_case_count_per_used_row':min(counts.values()),'contracts_sha256':hashlib.sha256(raw).hexdigest()}

if __name__=='__main__':
    names=('GD194sum','GD194H','GD194HS')
    manifest=json.loads((HERE/'input_sha256.json').read_text())
    for n in names:
        for f,h in manifest[n].items():assert hashlib.sha256((HERE/'inputs'/n/f).read_bytes()).hexdigest()==h,(n,f)
    receipts=[audit(HERE/'inputs'/n)for n in names]
    result={'frozen_input_payloads_unchanged':True,'machines':receipts}
    (HERE/'closure_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
