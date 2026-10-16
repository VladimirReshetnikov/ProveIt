#!/usr/bin/env python3
"""Check a new RM certificate with the prior report's independent path engine.

This uses verify_rm_certificate.py's Machine class, not the grammar generator
or compiler. It accepts the emitted reference DAG as an explicit input rather
than the prior verifier's fixed 219-node baseline. It supplies finite evidence,
not a kernel theorem or a binary-TM correctness proof.
"""
from pathlib import Path
import argparse,hashlib,importlib,json,sys
from collections import Counter

VERIFIER_SHA256='30fbd95b7a2a61004422558cfab4419de5239b67b88bc9ed19b7de8fcf585f18'

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--prior-machine-dir',type=Path,required=True)
    p.add_argument('--reference',type=Path,required=True)
    p.add_argument('--candidate',type=Path,required=True)
    p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    raw=(a.prior_machine_dir/'verify_rm_certificate.py').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=VERIFIER_SHA256:raise ValueError('independent verifier pin mismatch')
    sys.path.insert(0,str(a.prior_machine_dir.resolve()))
    engine=importlib.import_module('verify_rm_certificate')
    def load(path):
        data=json.loads(path.read_text());assert data['root']==0
        return engine.Machine({int(n):tuple(es) for n,es in data['nodes'].items()})
    old,new=load(a.reference),load(a.candidate)
    cert=json.loads(a.certificate.read_text());records=cert['pairs']
    assert cert['initial']==0 and cert['branch_order']=='EDecnz: zero, positive'
    assert old.contract('')==(records[0]['old'],records[0]['instruction'])
    assert new.contract('')==(records[0]['new'],records[0]['instruction'])
    seen=set()
    for rec in records:
        l,r,e=rec['old'],rec['new'],rec['instruction']
        assert (l,r) not in seen;seen.add((l,r))
        assert old.lookup(l)==(l,e) and new.lookup(r)==(r,e)
        succ=rec['successors'];xs,ys=old.targets(l,e),new.targets(r,e)
        assert len(succ)==len(xs)==len(ys)
        for i,x,y in zip(succ,xs,ys,strict=True):
            assert type(i) is int and 0<=i<len(records)
            nxt=records[i]
            assert x==(nxt['old'],nxt['instruction']) and y==(nxt['new'],nxt['instruction'])
    reachable=set();pending=[0]
    while pending:
        i=pending.pop()
        if i in reachable:continue
        reachable.add(i);pending.extend(records[i]['successors'])
    assert len(reachable)==len(records)
    result={'verified':True,'related_pairs':len(records),'reference_nodes':len(old.rows),
            'candidate_nodes':len(new.rows),'instruction_counts':dict(Counter(x['instruction'].split()[0] for x in records)),
            'reference_sha256':hashlib.sha256(a.reference.read_bytes()).hexdigest(),
            'candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),
            'certificate_sha256':hashlib.sha256(a.certificate.read_bytes()).hexdigest(),
            'independent_path_engine_sha256':VERIFIER_SHA256,
            'formal_kernel_proof':False,'binary_TM_and_ZFC_calibration_proved':False}
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
