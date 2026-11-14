#!/usr/bin/env python3
"""Fresh arbitrary-natural whole-tape derivations for all U213 source sites."""
import argparse,hashlib,json,sys,time
from pathlib import Path
import symbolic_runtime as s
import build_table as bt
import source_language as sl

def need(ok,msg):
    if not ok:raise ValueError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(root,out):
    root,out=Path(root),Path(out);out.mkdir(parents=True,exist_ok=True)
    table=root/'machine/u213.native.tm';source=root/'machine/sites.json'
    T=bt.parse(table.read_bytes());Q=bt.validate(T,213);rows=json.load(open(source));tree=sl.tree(rows)
    need(sl.metrics(tree)=={'dag_nodes':197,'leaf_occurrences':3909,'maximum_depth':42,'maximum_zero_run':6},'source census')
    g,checks=sl.graph_arithmetic(rows);need(g==sl.graph_intervals(rows),'source CFG disagreement')
    need(checks==5084,'successor census')
    mapping={int(k):int(v)for k,v in json.load(open(root/'inputs/legacy_mapping.json')).items()}
    for q in Q|{254}:mapping.setdefault(q,q+1000)
    need(len({mapping[q]for q in Q|{254}})==len(Q)+1,'native/legacy map not injective')
    need(mapping[84]==96 and mapping[254]==254,'dispatcher/halt mapping')
    L={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in T.items()}
    need(s.HEADER_BASE==56,'wrong header base')
    need(s.r.PHY==(6,2,0,4,3,7,8,5,1),'wrong physical register permutation')
    lemmas,blocks=s.prove_blocks(L);cases=[];used=set();start=time.monotonic()
    for i,site in enumerate(rows):
        for positive in ((False,True)if site[1]=='CD'else(False,)):
            ans=s.case(L,lemmas,site,positive);used.update(ans['rows']);ans['rows']=sorted(ans['rows']);ans.pop('trace')
            cases.append({'site_index':i,'positive':positive,**ans})
        if(i+1)%1000==0:print('Proved',len(cases),'cases',flush=True)
    need(len(cases)==5084,'case coverage')
    for block in blocks:
        for event in block['trace']:used.add(tuple(event[1][:2]))
    need(used==set(L),'literal row coverage')
    cases=json.loads(json.dumps(cases))
    saved=json.load(open(root/'evidence/runtime_cases.json'))
    need(cases==saved,'fresh symbolic derivations differ from frozen receipt')
    report={'status':'UNIVERSAL_MATHEMATICAL_PASS','table_sha256':digest(table),'source_sha256':digest(source),'working_states':213,'site_count':3909,'proved_cases':len(cases),'expected_cases':5084,'header_base':56,'literal_rows_covered':len(used),'symbolic_steps':sum(x['symbolic_steps']for x in cases),'minimum_duration_constant':min(x['duration'][0]for x in cases),'blocks':blocks,'seconds':time.monotonic()-start,'scope':'All natural primary registers at each decrement guard; arbitrary natural gap; arbitrary nonempty finite spare list; complete zero exterior. Unary and finite-list induction, not bounded register testing. Source calibration and blank startup are separate. No proof-assistant kernel certificate.'}
    (out/'runtime.json').write_text(json.dumps(report,indent=2)+'\n');(out/'runtime_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    return report
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--output',type=Path,required=True);a=p.parse_args();print(json.dumps(run(a.root,a.output),indent=2))
