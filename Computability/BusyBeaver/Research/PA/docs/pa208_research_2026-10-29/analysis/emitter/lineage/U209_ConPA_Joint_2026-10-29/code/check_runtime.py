#!/usr/bin/env python3
"""Fresh unary/list-inductive derivation for every final literal primitive.
The two inference modules are vendored byte-identically from Contextual U211.
Legacy names are conjugated bijectively; saved per-case rows use native names.
"""
import argparse,gzip,json,sys,time
from pathlib import Path
from common import ROOT,need,read,census,sha,write_json
PINS={'symbolic_runtime.py':'61b9c66272e8fd149829177cc384013814aea3c6b3b6b6f48e462d3913ea2022',
      'independent_runtime.py':'d490397a2b31be4f7f62461a3d9bcd88faf9093de904e43eea1b865561e7b7ee'}

def check(machine,output,compare=True):
    need(__debug__ and not sys.flags.optimize,'Run full symbolic verification without -O')
    for name,digest in PINS.items():need(sha((ROOT/'code'/name).read_bytes())==digest,'Induction engine identity')
    import symbolic_runtime as s
    machine=Path(machine);output=Path(output);output.mkdir(parents=True,exist_ok=True)
    table=read(machine/'u209.native.tm');states=census(table,209);sites=json.loads((machine/'sites.json').read_text())
    mapping={int(k):int(v)for k,v in json.loads((ROOT/'baseline/legacy_mapping.json').read_text()).items()}
    for q in states|{254}:mapping.setdefault(q,q+1000)
    need(len({mapping[q]for q in states|{254}})==210,'Noninjective runtime conjugacy')
    inverse={mapping[q]:q for q in states|{254}}
    literal={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in table.items()}
    need(mapping[84]==96 and mapping[254]==254 and s.HEADER_BASE==56,'Dispatcher/frame mismatch')
    start=time.monotonic();lemmas,blocks=s.prove_blocks(literal);cases=[];used=set()
    for index,site in enumerate(sites):
        for positive in((False,True)if site[1]=='CD'else(False,)):
            answer=s.case(literal,lemmas,site,positive);used.update(answer['rows'])
            answer['rows']=sorted((inverse[q],b)for q,b in answer['rows']);answer.pop('trace')
            cases.append({'site_index':index,'positive':positive,**answer})
        if(index+1)%1000==0:print(f'Rederived {len(cases)} arbitrary-value contracts',flush=True)
    for block in blocks:
        for event in block['trace']:used.add(tuple(event[1][:2]))
    need(len(sites)==3909 and len(cases)==5084 and used==set(literal),'Case/row coverage')
    need(all(len(c['duration'])==13 and c['duration'][0]>0 and all(n>=0 for n in c['duration'])for c in cases),'Positive affine duration')
    steps=sum(c['symbolic_steps']for c in cases);need(steps==1250049,'Changed derivation census')
    cases=json.loads(json.dumps(cases))
    if compare:
        with gzip.open(ROOT/'evidence/runtime_cases.json.gz','rt')as f:need(cases==json.load(f),'Fresh cases differ from independent discovery run')
    result={'status':'FULL_UNIVERSAL_RUNTIME_PASS','working_states':209,'transition_rows':418,
      'source_primitives':3909,'cases':len(cases),'row_coverage':len(used),'symbolic_inferences':steps,
      'minimum_duration_constant':min(c['duration'][0]for c in cases),'all_duration_coefficients_nonnegative':True,
      'arbitrary_primary_registers':9,'arbitrary_natural_gap':True,'arbitrary_nonempty_finite_spares':True,
      'header_base':56,'blocks':blocks,'blocks_use_legacy_labels':True,'legacy_to_native':inverse,
      'native_sha256':sha((machine/'u209.native.tm').read_bytes()),'source_sha256':sha((machine/'sites.json').read_bytes()),
      'engine_sha256':PINS,'seconds':time.monotonic()-start,'saved_cases_match_fresh':compare,
      'scope':'Ordinary mathematical induction over unary runs and finite lists; not a proof-assistant kernel certificate.'}
    write_json(output/'runtime.json',result)
    with gzip.GzipFile(filename=str(output/'runtime_cases.json.gz'),mode='wb',mtime=0)as f:f.write((json.dumps(cases,separators=(',',':'))+'\n').encode())
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,default=ROOT/'machine');p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=check(a.machine,a.output);print(json.dumps({k:v for k,v in r.items()if k not in('blocks','legacy_to_native')},indent=2))
