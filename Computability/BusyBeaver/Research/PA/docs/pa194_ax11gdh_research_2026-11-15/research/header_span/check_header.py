#!/usr/bin/env python3
"""Recheck literal arbitrary-register contracts at a smaller header span.

Uses the inherited independent whole-tape symbolic induction engine. It
rederives list traversals from the supplied runtime193 table. This does
not establish a blank startup or an arithmetic consistency calibration.
"""
import argparse, hashlib, json, pathlib, subprocess, sys, time
HERE=pathlib.Path(__file__).resolve().parent
REF=HERE/'reference'
sys.path.insert(0,str(REF))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('span',type=int)
    ap.add_argument('--table',type=pathlib.Path,default=HERE/'inputs/runtime193.native.tm')
    ap.add_argument('--append',type=int,default=1)
    args=ap.parse_args()
    sites_path=HERE/'inputs/primary.sites.json'
    sites=json.loads(sites_path.read_text())
    names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,names[o],a] for p,o,a in sites]
    assert source.graph_arithmetic(mapped)[0]==source.graph_intervals(mapped)
    native={}
    for ln in args.table.read_text().splitlines():
        if not ln or ln.startswith('#'):continue
        q,b,w,d,t=ln.split()
        native[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
    states={q for q,b in native}
    mapping={int(k):v for k,v in json.loads((REF/'legacy_mapping.json').read_text()).items()}
    for q in states|{254}:mapping.setdefault(q,q+10000)
    assert len({mapping[q]for q in states|{254}})==len(states)+1
    table={(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in native.items()}
    runtime.PHY=(6,2,0,4,3,7,8,5,1)
    sym.HEADER_BASE=args.span
    lemmas,blocks=sym.prove_blocks(table)
    assert len(blocks)==4
    start=time.time();events=outcomes=0;minimum=10**9;used=set()
    receipt={'header_span':args.span,'table_sha256':hashlib.sha256(args.table.read_bytes()).hexdigest(),
      'states':len(states),'max_source_address':max(len(p)for p,o,a in sites),
      'source_sites':len(sites),'append':args.append,'list_lemmas':4,
      'box_oracles':False,'scope':'universal local contracts only; no blank startup asserted'}
    try:
        for i,site in enumerate(mapped):
            for positive in ([False,True] if site[1]=='CD' else [False]):
                result=sym.case(table,lemmas,site,positive,append=args.append)
                outcomes+=1;events+=result['symbolic_steps']
                minimum=min(minimum,result['duration'][0]);used.update(result['rows'])
        receipt.update(status='PASS',source_outcomes=outcomes,symbolic_events=events,
          minimum_duration_constant=minimum,used_rows=len(used))
    except Exception as exc:
        receipt.update(status='FAIL',source_outcomes=outcomes,failed_site=i,
          positive=positive,error=str(exc))
    receipt['seconds']=round(time.time()-start,3)
    (HERE/f'header_{args.span}.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    if receipt['status']!='PASS':raise SystemExit(1)
if __name__=='__main__':main()
