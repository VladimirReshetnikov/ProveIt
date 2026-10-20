#!/usr/bin/env python3
"""Replay all unbounded Rel224 instruction cases with the retained proof engine.

No concrete register bound or concrete execution horizon is used. The engine
proves unary-run and finite-list induction schemas from this exact literal
transition table. --audit-stored checks retained proof data integrity/coverage;
it does not freshly rederive those induction arguments.
"""
from pathlib import Path
import argparse,hashlib,json,sys,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT));import check224 as independent
sys.path.insert(0,str(ROOT/'vendor'));import symbolic_runtime as engine
ENGINE_SHA='c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
HELPER_SHA='0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'
TABLE_SHA='e8467b9745c7a05860797a209ed05ce0b41b72a44d96f00aad43630a589ccc2f'
CASES_SHA='76d28d291b1c4a2087af7123417720b431d87c27b8d1a6e953c54ac7deca8e64'

def need(condition,message):
    if not condition:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
def inputs(results):
    need(__debug__ and not sys.flags.optimize,'Assertions must be enabled; do not use Python -O')
    need(sha(ROOT/'vendor/symbolic_runtime.py')==ENGINE_SHA,'Proof engine changed')
    need(sha(ROOT/'vendor/independent_runtime.py')==HELPER_SHA,'Runtime helper changed')
    tablepath=results/'candidate224.legacy.tm';sourcepath=results/'sites.json'
    need(sha(tablepath)==TABLE_SHA and sha(sourcepath)==independent.SOURCE_SHA,'Pinned runtime input changed')
    table,start,halt,states=independent.parse(tablepath);need((start,halt,len(states),len(table))==(95,254,224,448),'Runtime table census differs')
    sites,graph,metrics=independent.source_graph(sourcepath)
    need(metrics['guarded_cases']==6238,'Source case census differs')
    return table,sites,metrics

def prove(results,output=None):
    output=output or results/'universal224.json';output.parent.mkdir(parents=True,exist_ok=True)
    table,sites,metrics=inputs(results);start=time.monotonic();cases=[];used=set()
    result=dict(status='IN_PROGRESS',working_states=224,rows=448,table_sha256=TABLE_SHA,source_sha256=independent.SOURCE_SHA,
        engine_sha256=ENGINE_SHA,helper_sha256=HELPER_SHA,adapter_sha256=sha(Path(__file__)),metrics=metrics,expected_cases=6238,
        physical_register_map=list(engine.r.PHY),
        scope='All nine independent natural logical registers; both decrement guards; arbitrary natural extra gap, arbitrary natural first spare, arbitrary finite remaining spare list; complete tape with blank exterior.',
        proof_status='Executable ordinary mathematical induction; no new proof-assistant endpoint.',
        fuel_scope='The 4000-step symbolic derivation limit does not bound concrete register values, spare-list length, or concrete execution time.')
    def save():result.update(cases=len(cases),seconds=time.monotonic()-start);dump(output,result)
    try:
        lemmas,blocks=engine.prove_blocks(table);result['blocks']=blocks
        print('Four exact-table list induction schemas proved',flush=True)
        for i,site in enumerate(sites):
            for positive in((False,True)if site[1]=='CD'else(False,)):
                answer=engine.case(table,lemmas,site,positive)
                used.update(answer.pop('rows'));answer.pop('trace')
                cases.append(dict(site_index=i,positive=positive,**answer))
                if len(cases)%1000==0:save();print('Proved',len(cases),'of 6238 cases',flush=True)
        need(len(cases)==6238 and used==set(table),'Incomplete source/row coverage')
        casepath=output.with_name(output.stem+'_cases.json');dump(casepath,cases)
        need(sha(casepath)==CASES_SHA,'Fresh proof-case array differs from the retained exact derivation')
        result.update(status='UNIVERSAL_MATHEMATICAL_PASS',symbolic_steps=sum(c['symbolic_steps']for c in cases),
            minimum_actual_steps=min(c['duration'][0]for c in cases),maximum_symbolic_steps=max(c['symbolic_steps']for c in cases),
            used_rows=[list(row)for row in sorted(used)],all_rows_used=True,cases_file=casepath.name,cases_sha256=sha(casepath))
        save();return result
    except Exception as error:
        result.update(status='NOT_PROVED',site_index=locals().get('i'),site=locals().get('site'),positive=locals().get('positive'),error=repr(error));save();raise

def audit_stored(results,output=None):
    output=output or results/'universal224.json';table,sites,metrics=inputs(results)
    receipt=json.loads(output.read_text());casepath=output.with_name(receipt['cases_file'])
    need(receipt['status']=='UNIVERSAL_MATHEMATICAL_PASS','Stored proof is incomplete')
    need(receipt['table_sha256']==TABLE_SHA and receipt['source_sha256']==independent.SOURCE_SHA,'Stored proof input differs')
    need(receipt['engine_sha256']==ENGINE_SHA and receipt['helper_sha256']==HELPER_SHA,'Stored proof engine differs')
    need(sha(casepath)==receipt['cases_sha256']==CASES_SHA,'Stored proof cases changed')
    cases=json.loads(casepath.read_text());expected=[(i,p)for i,site in enumerate(sites)for p in((False,True)if site[1]=='CD'else(False,))]
    need([(c['site_index'],c['positive'])for c in cases]==expected and len(cases)==6238,'Stored source-case coverage differs')
    need(all(len(c['duration'])==13 and all(type(x)is int and x>=0 for x in c['duration'])and c['duration'][0]>0 for c in cases),'Stored positive-duration form differs')
    need(set(map(tuple,receipt['used_rows']))==set(table)and receipt['all_rows_used'],'Stored row coverage differs')
    need(sum(c['symbolic_steps']for c in cases)==receipt['symbolic_steps']==1503342,'Stored symbolic-step total differs')
    return dict(status='STORED_RUNTIME_INTEGRITY_AND_COVERAGE_PASS',cases=6238,working_states=224,rows=448,cases_sha256=CASES_SHA,
        table_sha256=TABLE_SHA,scope='Hashes, complete guarded-case enumeration, row coverage and positive duration forms audited. Use the default full replay to freshly rederive all unbounded cases.')
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--results',type=Path,default=ROOT/'results');ap.add_argument('--output',type=Path);ap.add_argument('--audit-stored',action='store_true');args=ap.parse_args()
    result=(audit_stored if args.audit_stored else prove)(args.results,args.output)
    print(json.dumps({k:v for k,v in result.items()if k not in('blocks','used_rows')},indent=2))
