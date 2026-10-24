#!/usr/bin/env python3
"""Check exact full-row identities and sequential sign hypotheses, no producer."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'candidates/projected-radius-mixed-bounds'


def need(ok,text):
    if not ok:raise ValueError(text)


def load(path):return json.loads(path.read_text())
def digest(data):return sha256(data).hexdigest()


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj


def lower_bound(raw,step,known,b):
    v,L=step['variable'],step['lower'];F,G=b.poly(step['factor']),b.poly(step['rhs'])
    need(type(v)is int and 0<=v<1259 and v not in known and type(L)is int and L>=0,
         'fresh integer lower-bound target')
    need(all(0<=i<1259 and i!=v for p in [F,G]for m in p for i in m),'no target or out-of-range factor/RHS variable')
    actual={}
    for item in step['row_combination']:
        i=item['row'];need(type(i)is int and 0<=i<1177,'literal original raw row')
        multiplier=b.poly(item['multiplier'])
        need(all(0<=v<1259 for m in multiplier for v in m),'literal integer ideal multiplier')
        actual=b.add(actual,b.mul(multiplier,b.poly(raw['rows'][i]['terms'])))
    need(actual==b.add(b.mul({(v,):1},F),G,-1),'entire original-row ideal identity')
    shifted_factor=b.nonnegative(F,known,True)
    shifted_gap=b.nonnegative(b.add(G,F,-(L-1)),known,True)
    known[v]=L
    return dict(raw_variable=v,lower=L,original_row_count=len(step['row_combination']),
        shifted_factor=[[c,list(m)]for m,c in sorted(shifted_factor.items())],
        shifted_gap=[[c,list(m)]for m,c in sorted(shifted_gap.items())])


def verify(raw,body,parent,cert,b,mixed):
    ids={json.dumps(v,sort_keys=True,separators=(',',':')):i for i,v in enumerate(raw['variables'])}
    retained=[ids[json.dumps(v,sort_keys=True,separators=(',',':'))]for v in body['variables']]
    need(retained==parent['retained_raw_indices']and len(retained)==667,'all actual raw-to667 identities')
    old=[g['raw_variable']for g in parent['guards']]
    need(cert['all_original_guard_indices']==old and len(old)==107,'complete frozen107 guard boundary')
    removed=cert['removed_guard_identities']
    exact=[(32,29),(87,66),(107,77),(130,91),(517,218)]
    need(removed==[dict(raw_variable=r,contracted_variable=c,metadata=raw['variables'][r])for r,c in exact]
         and all(retained[c]==r for r,c in exact),'five full-metadata sign identities')
    seeds=cert['remaining_raw_guard_indices']
    need(seeds==sorted(set(old)-{r for r,c in exact})and len(seeds)==102,
         'exact102 retained seeds, with no formerly signed coordinate assumed natural')
    need({0,694}<=set(seeds),'actual t0/T guards retained')
    known={i:0 for i in seeds}
    need(cert['initial_bound_steps']==parent['bound_steps'],'unchanged four preliminary certificates')
    bounds=[lower_bound(raw,s,known,b)for s in cert['initial_bound_steps']]
    need([(x['raw_variable'],x['lower'])for x in bounds]==[(4,1),(5,2),(644,2),(917,2)],
         'four sequential t,n,A,D bounds')
    rows=dict(variables=raw['variables'],residuals=[dict(label=r['label'],terms=r['terms'])for r in raw['rows']])
    need([(s['variable'],s['lower'])for s in cert['stages']]==[(87,0),(107,0),(130,0),(517,0),(32,1)],
         'fixed five-stage order')
    results=[];total_steps=0
    for stage in cert['stages']:
        preceding=set(known)
        for step in stage['preceding_sign_steps']:mixed.inferred_step(rows,step,preceding)
        for v in preceding:known.setdefault(v,0)
        if stage['variable']==517:
            need(516 in known,'CRT evaluation numerator sign proved before division')
        result=lower_bound(raw,stage,known,b)
        need(stage['known_after']==sorted(known),'complete sequential known-sign ledger')
        result['preceding_original_sign_rows']=len(stage['preceding_sign_steps'])
        result['nonnegative_after']=len(known);results.append(result)
        total_steps+=len(stage['preceding_sign_steps'])
    need(set(old)<=set(known)and cert['known_after']==sorted(known),
         'all107 original guard values proved nonnegative without a cycle')
    return dict(initial_guard_count=102,recovered_original_guard_count=107,
        preliminary_bounds=bounds,stages=results,ordinary_source_sign_rows=total_steps,
        nonnegative_raw_coordinates=len(known),
        arithmetic_semantic_calls=0,
        conclusion='Supply15 fresh integer Legendre witnesses to reach the literal988 equation. Pure original-row inequalities precede every power/Pell interpretation.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'entire frozen input '+n)
    manifest=load(BASE/'MANIFEST.json')['files']
    need({str(p.relative_to(BASE))for p in BASE.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}==set(manifest),
         'whole closed frozen988 file set')
    for n,h in manifest.items():need(digest((BASE/n).read_bytes())==h,'complete frozen988 member '+n)
    raw=load(BASE/'source/raw_builder.json');body=load(BASE/'source/natural667.json')
    parent=load(BASE/'domain_certificate.json');cert=load(HERE/'CERTIFICATE.json')
    b=module('frozen_nonnegative_shift_checker',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed=module('frozen_exact_sign_row_checker',ROOT/'candidates/projected-radius-mixed/check.py')
    result=verify(raw,body,parent,cert,b,mixed);mutations=[]
    def reject(label,thunk):
        try:thunk()
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError):mutations.append(label)
        else:raise ValueError('bad certificate accepted '+label)
    bad=deepcopy(cert);bad['remaining_raw_guard_indices'].append(87)
    reject('assumed removed factorial sign',lambda:verify(raw,body,parent,bad,b,mixed))
    bad=deepcopy(cert);bad['stages'][0],bad['stages'][2]=bad['stages'][2],bad['stages'][0]
    reject('cyclic or reordered stage boundary',lambda:verify(raw,body,parent,bad,b,mixed))
    for j in range(5):
        bad=deepcopy(cert);bad['stages'][j]['row_combination'][0]['multiplier'][0][0]+=1
        reject('changed full row identity '+str(j),lambda:verify(raw,body,parent,bad,b,mixed))
    bad=deepcopy(cert);bad['stages'][0]['preceding_sign_steps'][0]['rhs'][0][0]+=1
    reject('changed preceding sign-row coefficient',lambda:verify(raw,body,parent,bad,b,mixed))
    bad=deepcopy(cert);bad['removed_guard_identities'][0]['contracted_variable']+=1
    reject('wrong retained-coordinate identity',lambda:verify(raw,body,parent,bad,b,mixed))
    bad=deepcopy(cert);bad['remaining_raw_guard_indices'].remove(694)
    reject('missing preliminary T guard',lambda:verify(raw,body,parent,bad,b,mixed))
    result.update(status='PASS',optimized_python=bool(sys.flags.optimize),rejected_corruptions=mutations,
        certificate_sha256=digest((HERE/'CERTIFICATE.json').read_bytes()),
        scope='Five universal pre-semantic sign consequences, fully specified original-row ideals and sequential dependency checks. No new complete quartic/count frontier is claimed by this research receipt.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
