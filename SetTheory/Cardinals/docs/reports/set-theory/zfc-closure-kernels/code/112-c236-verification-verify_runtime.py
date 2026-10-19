#!/usr/bin/env python3
"""Reprove the complete literal runtime on the new, source-calibrated layout.

The bundled, unchanged symbolic engine proves unary and finite-list induction
from the exact table. Its finite proof-construction fuel does not bound runs.
"""
from pathlib import Path
import argparse, hashlib, json, sys, time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'upstream/zfc237/verification'))
import symbolic_runtime as s
import check_source_graph as g
sys.path.insert(0,str(ROOT/'verification'))
from verify_state_fold import parse_table

def sha(b):return hashlib.sha256(b).hexdigest()
def require(c,msg):
    if not c:raise ValueError(msg)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,default=ROOT/'machines/zfc236_old.tm')
    ap.add_argument('--sites',type=Path,default=ROOT/'source/sites_logical.json')
    ap.add_argument('--states',type=int,default=236)
    ap.add_argument('--output',type=Path,default=ROOT/'evidence/runtime236.json')
    a=ap.parse_args()
    require(__debug__ and not sys.flags.optimize,'Run without Python optimization')
    raw=a.table.read_bytes();sr=a.sites.read_bytes();table,start=parse_table(raw);sites=json.loads(sr)
    require(start==95 and len(table)==2*a.states,'Wrong table census')
    require(sha(sr)=='1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f','Wrong source pin')
    baseline=json.loads((ROOT/'upstream/zfc237/inputs/sites_logical.json').read_bytes())
    bo,bg,bi,_=g.graph(baseline);co,cg,ci,_=g.graph(sites)
    require([x[1:] for x in bo]==[x[1:] for x in co] and bg==cg and bi==ci,'Source graph changed')
    require(len(sites)==6455,'Wrong source census')
    began=time.monotonic();lemmas,blocks=s.prove_blocks(table);cases=[];rows=set()
    print('All four exact-table list induction schemas passed.',flush=True)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    for index,site in enumerate(sites):
        for positive in ((False,True) if site[1]=='CD' else (False,)):
            try:ans=s.case(table,lemmas,site,positive)
            except (AssertionError,KeyError) as ex:
                receipt={'status':'NOT_PROVED','site_index':index,'site':site,'positive':positive,'prior_cases':len(cases),'reason':str(ex)}
                a.output.write_text(json.dumps(receipt,indent=2)+'\n');raise
            rows.update(ans.pop('rows'));ans.pop('trace')
            cases.append({'site_index':index,'positive':positive,**ans})
            if len(cases)%1000==0:print('proved',len(cases),'guards',round(time.monotonic()-began,2),'seconds',flush=True)
    require(len(cases)==8386,'Incomplete guard coverage')
    require(rows==set(table),'Not every literal row was covered')
    receipt={'status':'UNIVERSAL_MATHEMATICAL_PASS','working_states':a.states,'transition_rows':len(table),
             'table_sha256':sha(raw),'sites_sha256':sha(sr),'checker_sha256':sha(Path(__file__).read_bytes()),
             'engine_sha256':sha(Path(s.__file__).read_bytes()),'helper_sha256':sha(Path(s.r.__file__).read_bytes()),
             'cases':len(cases),'symbolic_steps':sum(x['symbolic_steps'] for x in cases),
             'minimum_actual_steps':min(x['duration'][0] for x in cases),'blocks':blocks,
             'directly_used_rows':sorted(rows),'seconds':time.monotonic()-began,
             'scope':'All guarded source leaves; all natural primary values, arbitrary natural gap, arbitrary first spare and finite spare tail; exact whole tape and zero exterior. Ordinary mathematical checker, not a proof-assistant endpoint.'}
    a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    a.output.with_name(a.output.stem+'_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('blocks','directly_used_rows')},indent=2),flush=True)

if __name__=='__main__':main()
