#!/usr/bin/env python3
"""Independent executable verifier for a finite operation bisimulation.

Generalizes the source08 checker's source input to two arbitrary explicit
DAGs. It imports only its independent string-path machine semantics, never
the grammar generator or binary TM backend. This is not a kernel proof.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor/python'))
from upstream_verify_rm_certificate import Machine


def verify(reference,candidate,certificate):
    machines=[]
    for path in (reference,candidate):
        data=json.loads(path.read_text())
        assert data['root']==0
        machines.append(Machine({int(q):tuple(es) for q,es in data['nodes'].items()}))
    old,new=machines;cert=json.loads(certificate.read_text());records=cert['pairs']
    assert cert['initial']==0 and cert['branch_order']=='EDecnz: zero, positive'
    assert old.contract('')==(records[0]['old'],records[0]['instruction'])
    assert new.contract('')==(records[0]['new'],records[0]['instruction'])
    seen=set()
    for row in records:
        left,right,label=row['old'],row['new'],row['instruction']
        assert (left,right) not in seen;seen.add((left,right))
        assert old.lookup(left)==(left,label) and new.lookup(right)==(right,label)
        a,b=old.targets(left,label),new.targets(right,label)
        assert len(row['successors'])==len(a)==len(b)
        for index,x,y in zip(row['successors'],a,b,strict=True):
            assert type(index) is int and 0<=index<len(records)
            target=records[index]
            assert x==(target['old'],target['instruction'])
            assert y==(target['new'],target['instruction'])
    seen=set();todo=[0]
    while todo:
        q=todo.pop()
        if q in seen:continue
        seen.add(q);todo.extend(records[q]['successors'])
    assert len(seen)==len(records)
    return dict(verified=True,pairs=len(records),
                labels=dict(Counter(r['instruction'].split()[0] for r in records)),
                reference_sha256=hashlib.sha256(reference.read_bytes()).hexdigest(),
                candidate_sha256=hashlib.sha256(candidate.read_bytes()).hexdigest(),
                certificate_sha256=hashlib.sha256(certificate.read_bytes()).hexdigest(),
                binary_TM_correctness_proved=False,kernel_checked=False)


def main():
    if not __debug__:raise RuntimeError('assertions required')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--reference',type=Path,required=True)
    p.add_argument('--candidate',type=Path,required=True)
    p.add_argument('--certificate',type=Path,required=True)
    a=p.parse_args();print(json.dumps(verify(a.reference,a.candidate,a.certificate),indent=2,sort_keys=True))


if __name__=='__main__':main()
