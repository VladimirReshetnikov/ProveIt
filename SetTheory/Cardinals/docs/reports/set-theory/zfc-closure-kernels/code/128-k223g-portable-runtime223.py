#!/usr/bin/env python3
"""Fresh unbounded symbolic runtime proof, or explicit stored-data audit."""
from pathlib import Path
import argparse, hashlib, json, sys, time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT));import build223 as b
sys.path.insert(0,str(ROOT/'runtime'));import symbolic_runtime as engine
ENGINE_SHA='c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
HELPER_SHA='0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'
TABLE_SHA='2825e053950da9a6a6bbdd96ef5d96b680542fdf1d307973c553a18ed5baffe0'
CANONICAL_SHA='0d4eb8ffbcd5dc025c8dac198c7d8a15404c35f63134b5e3ed0b7df7673d9231'
CASES_SHA='a012f3aea9fad2010086c1613a36217b81f3c5cba4148e8545ac8ff64e3cb7da'

def inputs(results):
    b.need(__debug__ and not sys.flags.optimize,'Do not use Python -O')
    b.need(b.sha(ROOT/'runtime/symbolic_runtime.py')==ENGINE_SHA,'Proof engine differs')
    b.need(b.sha(ROOT/'runtime/independent_runtime.py')==HELPER_SHA,'Runtime helper differs')
    b.need(b.sha(results/'candidate223.legacy.tm')==TABLE_SHA,'Literal runtime table differs')
    b.need(b.sha(results/'candidate223.tm')==CANONICAL_SHA,'Canonical table differs')
    table,start,halt,states=b.parse(results/'candidate223.legacy.tm')
    b.need((start,halt,len(states),len(table))==(95,254,223,446),'Runtime census differs')
    sites,metrics=b.source_metrics(results/'sites.json')
    return table,sites,metrics

def prove(results,output):
    table,sites,metrics=inputs(results);output.parent.mkdir(parents=True,exist_ok=True)
    started=time.monotonic();cases=[];used=set()
    receipt=dict(status='IN_PROGRESS',working_states=223,rows=446,expected_cases=5956,
        source_metrics=metrics,source_sha256=b.SOURCE_SHA,table_sha256=TABLE_SHA,
        canonical_table_sha256=CANONICAL_SHA,engine_sha256=ENGINE_SHA,helper_sha256=HELPER_SHA,
        adapter_sha256=b.sha(Path(__file__)),physical_register_map=list(engine.r.PHY),
        scope='All nine independent natural logical registers; both decrement guards; arbitrary natural extra gap, arbitrary natural first spare, arbitrary finite remaining spare list; complete tape with blank exterior.',
        proof_status='Executable ordinary mathematical induction; no new proof-assistant endpoint.',
        fuel_scope='The 4000-step symbolic proof-search limit bounds neither concrete values, spare-list length nor actual execution time.')
    def save():
        receipt.update(cases=len(cases),seconds=time.monotonic()-started);b.dump(output,receipt)
    try:
        lemmas,blocks=engine.prove_blocks(table);receipt['blocks']=blocks
        print('Four exact-table list induction schemas proved',flush=True)
        for i,site in enumerate(sites):
            for positive in ((False,True) if site[1]=='CD' else (False,)):
                answer=engine.case(table,lemmas,site,positive)
                used.update(answer.pop('rows'));answer.pop('trace')
                cases.append(dict(site_index=i,positive=positive,**answer))
                if len(cases)%1000==0:save();print('Proved',len(cases),'of 5956 cases',flush=True)
        b.need(len(cases)==5956 and used==set(table),'Incomplete case or transition coverage')
        casepath=output.with_name(output.stem+'_cases.json');b.dump(casepath,cases)
        b.need(b.sha(casepath)==CASES_SHA,'Fresh symbolic proof cases differ from retained derivations')
        receipt.update(status='UNIVERSAL_MATHEMATICAL_PASS',symbolic_steps=sum(x['symbolic_steps'] for x in cases),
            minimum_actual_steps=min(x['duration'][0] for x in cases),maximum_symbolic_steps=max(x['symbolic_steps'] for x in cases),
            used_rows=sorted(used),all_rows_used=True,cases_file=casepath.name,cases_sha256=CASES_SHA)
        save();return receipt
    except Exception as error:
        receipt.update(status='NOT_PROVED',site_index=locals().get('i'),site=locals().get('site'),
            positive=locals().get('positive'),error=repr(error));save();raise

def audit(results,receipt_path):
    table,sites,metrics=inputs(results);receipt=json.loads(receipt_path.read_text())
    b.need(receipt['status']=='UNIVERSAL_MATHEMATICAL_PASS','Stored runtime is incomplete')
    b.need(receipt['source_sha256']==b.SOURCE_SHA and receipt['table_sha256']==TABLE_SHA,'Stored runtime input differs')
    b.need(receipt['engine_sha256']==ENGINE_SHA and receipt['helper_sha256']==HELPER_SHA,'Stored engine differs')
    path=receipt_path.with_name(receipt['cases_file']);b.need(b.sha(path)==receipt['cases_sha256']==CASES_SHA,'Stored cases differ')
    cases=json.loads(path.read_text())
    expected=[(i,p) for i,s in enumerate(sites) for p in ((False,True) if s[1]=='CD' else (False,))]
    b.need([(x['site_index'],x['positive']) for x in cases]==expected and len(cases)==5956,'Stored case coverage differs')
    b.need(all(len(x['duration'])==13 and x['duration'][0]>0 and all(type(v)is int and v>=0 for v in x['duration']) for x in cases),'Invalid positive affine duration')
    b.need(set(map(tuple,receipt['used_rows']))==set(table) and receipt['all_rows_used'],'Stored row coverage differs')
    b.need(sum(x['symbolic_steps'] for x in cases)==receipt['symbolic_steps']==1431799,'Stored symbolic-step census differs')
    return dict(status='STORED_RUNTIME_INTEGRITY_AND_COVERAGE_PASS',working_states=223,rows=446,cases=5956,
        cases_sha256=CASES_SHA,scope='Hashes, coverage, and positive duration forms audited. Use --full in reproduce.py to rederive the unbounded cases.')

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--results',type=Path,default=ROOT/'results')
    ap.add_argument('--output',type=Path);ap.add_argument('--audit-stored',action='store_true');a=ap.parse_args()
    path=a.output or a.results/'runtime223.json';result=audit(a.results,path) if a.audit_stored else prove(a.results,path)
    print(json.dumps({k:v for k,v in result.items() if k not in ('blocks','used_rows')},indent=2))
