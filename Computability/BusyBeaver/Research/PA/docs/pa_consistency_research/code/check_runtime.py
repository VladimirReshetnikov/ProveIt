#!/usr/bin/env python3
"""Replay symbolic whole-tape contracts with a specified header minimum.

This is a fresh execution of the inherited induction engine, not a kernel
certificate. The engine sources are pinned. Only its HEADER_BASE parameter
is changed in memory, and the selected value is recorded in the receipt.
"""
from pathlib import Path
import argparse,sys,json,time,hashlib,gzip
HERE=Path(__file__).resolve().parent
BASE=HERE/'runtime'
sys.path.insert(0,str(BASE))
import check_runtime as cr,symbolic_runtime as s,source_language as sl

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,required=True)
    p.add_argument('--source',type=Path,required=True);p.add_argument('--gap',type=int,required=True)
    p.add_argument('--states',type=int,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    report=dict(machine=str(a.machine),source=str(a.source),machine_sha256=sha(a.machine),
                source_sha256=sha(a.source),header_base=a.gap,expected_states=a.states,
                scope='Executable symbolic induction over arbitrary register values, nonempty finite spares, and every header gap at least header_base; not a proof-assistant kernel certificate.')
    start=time.monotonic();cases=[];index=-1;positive=None
    try:
        assert __debug__ and not sys.flags.optimize
        for name,h in cr.PINS.items():assert sha(BASE/name)==h,(name,'engine hash mismatch')
        s.HEADER_BASE=a.gap
        native,states=cr.read(a.machine,a.states)
        mapping={int(k):int(v) for k,v in json.loads((BASE/'legacy_mapping.json').read_text()).items()}
        for q in states|{254}:mapping.setdefault(q,q+1000)
        assert len({mapping[q] for q in states|{254}})==len(states)+1
        assert mapping[84]==96 and mapping[254]==254
        inverse={mapping[q]:q for q in states|{254}}
        table={(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in native.items()}
        sites=json.loads(a.source.read_text());oldsites=json.loads((BASE/'original.json').read_text())
        assert [x[1:] for x in sites]==[x[1:] for x in oldsites]
        assert sl.graph_arithmetic(sites)[0]==sl.graph_arithmetic(oldsites)[0]==sl.graph_intervals(sites)
        report['source_cfg_equal']=True;report['source_metrics']=sl.metrics(sl.tree(sites))
        lemmas,blocks=s.prove_blocks(table);used=set()
        for index,site in enumerate(sites):
            for positive in ((False,True) if site[1]=='CD' else (False,)):
                answer=s.case(table,lemmas,site,positive)
                used.update(answer['rows']);answer['rows']=sorted((inverse[q],b) for q,b in answer['rows'])
                answer.pop('trace');cases.append(dict(site_index=index,positive=positive,**answer))
            if (index+1)%1000==0:print('source',index+1,'contracts',len(cases),flush=True)
        for block in blocks:
            for event in block['trace']:used.add(tuple(event[1][:2]))
        assert len(cases)==sum(2 if x[1]=='CD' else 1 for x in sites)
        assert all(len(c['duration'])==13 and c['duration'][0]>0 and all(x>=0 for x in c['duration']) for c in cases)
        assert used<=set(table)
        report.update(status='FULL_UNIVERSAL_RUNTIME_PASS',cases=len(cases),row_coverage=len(used),blocks=blocks,
                      minimum_duration_constant=min(c['duration'][0] for c in cases),
                      symbolic_inferences=sum(c['symbolic_steps'] for c in cases))
        with gzip.GzipFile(filename=str(a.output/'runtime_cases.json.gz'),mode='wb',mtime=0) as f:
            f.write((json.dumps(cases,separators=(',',':'))+'\n').encode())
    except Exception as e:
        report.update(status='FAIL',case_index=index,positive=positive,proved_cases=len(cases),error=repr(e))
    report['seconds']=time.monotonic()-start
    (a.output/'runtime.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='blocks'},indent=2),flush=True)
    if report['status'] != 'FULL_UNIVERSAL_RUNTIME_PASS': raise SystemExit(1)

if __name__=='__main__':main()
