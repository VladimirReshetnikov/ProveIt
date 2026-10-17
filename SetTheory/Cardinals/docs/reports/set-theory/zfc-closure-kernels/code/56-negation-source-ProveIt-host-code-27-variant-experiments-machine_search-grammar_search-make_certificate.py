#!/usr/bin/env python3
"""Construct and independently check a finite register-program bisimulation.

The certificate is between the source09 baseline203 DAG and one selected
closed-sequence reassociation. It proves register-program halting equivalence
under the documented path semantics; it does not itself prove the TM layer.
"""
from pathlib import Path
import json,hashlib
import prior_rm_verify as rm
import cost_search as s

def generate(p1,p2):
    n1,r1=p1;n2,r2=p2;index={};cert=[];pending=[]
    def normalize(a,b):
        ia,pa,_=rm.segment(n1,r1,a);ib,pb,_=rm.segment(n2,r2,b)
        assert ia==ib,('increment mismatch',a,b,ia,ib)
        pair=pa,pb
        if pair not in index:
            index[pair]=len(cert);cert.append([pa,pb,None,None]);pending.append(pair)
        return index[pair]
    assert normalize('','')==0
    k=0
    while k<len(pending):
        a,b=pending[k];k+=1;i=index[a,b]
        ea,qa=rm.site(n1,r1,a);eb,qb=rm.site(n2,r2,b)
        assert ea==eb and ea[0] in 'DH',('different test',a,b,ea,eb)
        if ea[0]=='H':cert[i][2:]=[i,i];continue
        for offset,positive in enumerate((True,False),2):
            cert[i][offset]=normalize(rm.nextpc(ea,qa,positive),rm.nextpc(eb,qb,positive))
    return cert

def main():
    n,e,kind=s.rot.options(s.NODES)[0];nodes,root=s.rot.mutate(s.NODES,s.ROOT,n,e)
    p1=s.NODES,s.ROOT;p2=nodes,root
    cert=generate(p1,p2)
    forward=rm.check(p1,p2,cert)
    reverse=rm.check(p2,p1,[[b,a,j,k] for a,b,j,k in cert])
    wrong=[row[:] for row in cert];wrong[0][0]='1'+wrong[0][0]
    try:rm.check(p1,p2,wrong)
    except AssertionError:pass
    else:raise AssertionError('corrupted certificate accepted')
    out=s.HERE/'results';out.mkdir(exist_ok=True)
    data=(json.dumps(cert,indent=2)+'\n').encode()
    (out/'rotation0_rm_certificate.json').write_bytes(data)
    result={'certificate_entries':len(cert),'forward':True,'backward':True,
            'maximum_segment':max(forward,reverse),'corrupted_initial_path_rejected':True,
            'baseline_metrics':rm.metrics(p1),'candidate_metrics':rm.metrics(p2),
            'certificate_sha256':hashlib.sha256(data).hexdigest(),
            'scope':'Finite bisimulation-up-to-commuting-increments certificate, both decrement branches at every related test. Register-program equivalence for every initial register vector; not a TM or set-theory kernel theorem.'}
    (out/'rotation0_rm_certificate_result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
