#!/usr/bin/env python3
"""Independently check selected decoder grammars by register trace certificates.

The unchanged source09 verifier contracts only straight increment/control runs
between tests. Both exits of every decrement are checked. This is an RM result.
"""
from collections import deque
from pathlib import Path
import importlib.util, json, hashlib

HERE = Path(__file__).resolve().parent
path = HERE.parent / 'sources/09-decoder-decoder-verify.py'
spec = importlib.util.spec_from_file_location('rm_verify', path)
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)

def certificate(a,b):
    cache={};rows=[]
    def pause(x,y):
        ia,pa,_=v.segment(*a,x);ib,pb,_=v.segment(*b,y)
        if ia!=ib:raise ValueError('increment effects differ')
        pair=(pa,pb)
        if pair not in cache:
            cache[pair]=len(rows);rows.append([pa,pb,None,None])
        return cache[pair]
    assert pause('','')==0
    i=0
    while i<len(rows):
        x,y,_,_=rows[i]
        ea,qa=v.site(*a,x);eb,qb=v.site(*b,y)
        if ea==eb==('H',):i+=1;continue
        if ea!=eb or ea[0]!='D':raise ValueError('decrement tests differ')
        for index,nonzero in ((2,True),(3,False)):
            rows[i][index]=pause(v.nextpc(ea,qa,nonzero),v.nextpc(eb,qb,nonzero))
        i+=1
        if len(rows)>20000:raise ValueError('certificate relation exceeds declared limit')
    return rows

def main():
    baseline=v.program(HERE/'input/candidate_dag.json');results=[]
    for name in ['greedy','weighted8','right4','weighted8_extended','weighted4_extended']:
        target=HERE/name/'best_dag.json';candidate=v.program(target)
        cert=certificate(baseline,candidate)
        forward=v.check(baseline,candidate,cert)
        reverse=v.check(candidate,baseline,[[y,x,j,k] for x,y,j,k in cert])
        mutation=[list(row) for row in cert];mutation[0][0]='1'+mutation[0][0]
        try:v.check(baseline,candidate,mutation)
        except AssertionError:pass
        else:raise ValueError('corrupt initial path accepted')
        out=target.parent/'certificate.json';out.write_text(json.dumps(cert,separators=(',',':'))+'\n')
        results.append({'run':name,'metrics':v.metrics(candidate),'entries':len(cert),
                        'max_segment':max(forward,reverse),'both_directions_pass':True,
                        'corrupt_initial_path_rejected':True,
                        'dag_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
                        'certificate_sha256':hashlib.sha256(out.read_bytes()).hexdigest()})
    evidence={'baseline':v.metrics(baseline),'selected_candidates':results,
              'scope':'RM equivalence for every initial register vector; no binary simulation proof'}
    (HERE/'grammar_verification.json').write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps(evidence,indent=2))

if __name__=='__main__':main()
