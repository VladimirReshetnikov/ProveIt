#!/usr/bin/env python3
"""Read-only literal source audit; source-sized snapshot, no horizon polynomial."""
import hashlib
import json
from pathlib import Path
import sys
from collections import Counter
from certificate import read_machine, Certificate

ROOT=Path(__file__).resolve().parent
EXPECTED='38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a'


def check(ok,message):
    if not ok: raise RuntimeError(message)


def main():
    path=Path(sys.argv[1] if len(sys.argv)>1 else ROOT.parent/'source/source.json')
    machine,sha=read_machine(path,require_reversible=True)
    check(sha==EXPECTED,'unexpected source digest')
    hist=Counter(b.kind for b in machine.branches)
    check(dict(hist)==dict(A=30,Z=23429,P=52036,I=33436,D=32630),'unexpected primitive histogram')
    check(len(machine.controls)==122622 and len(machine.branches)==141561,'unexpected table dimensions')
    check(machine.no_incoming_start and machine.reversible,'source injection/start condition failed')
    ledgers={}
    for K in (0,1,2,10**30):
        c=Certificate(machine,K,machine.start,(1,0),clock=True,nonnegative_real=True)
        ledger=c.ledger()
        check(c.nvars==141565*K+1,'variable ledger')
        check(c.nrows==23436*K+2,'square ledger')
        if K:
            check(ledger['raw_residual_term_slots']==981480*K-66065,'raw written-term ledger')
        else:
            check(ledger['raw_residual_term_slots']==2,'zero-horizon term ledger')
        ledgers[str(K)]=ledger
    c=Certificate(machine,1,machine.start,(1,0),clock=True,nonnegative_real=True)
    blocked=[]
    for label,action in [('materialize',c.materialize),('witness',c.witness),('expanded',c.expanded)]:
        try: action()
        except ValueError: blocked.append(label)
        else: raise RuntimeError('universal operation was not bounded: '+label)
    first=machine.transition(machine.start,(1,0))
    check(first is not None and first[1]!=machine.halt,'clean horizon-one should not accept')
    full_h1=dict(source_sha256=sha,**ledgers['1'])
    full_h1.update(specialization='clean empty-tape source ID START(1,0)',horizon_one_accepts=False,
                   evidence='The unique first source transition does not reach HALT; no full witness was allocated',
                   universal_polynomial_materialized=False)
    (ROOT/'universal-h1-ledger.json').write_text(json.dumps(full_h1,indent=2)+'\n')
    receipt=dict(status='passed',source_sha256=sha,implementation_sha256=hashlib.sha256((ROOT/'certificate.py').read_bytes()).hexdigest(),
                 primitive_histogram=dict(hist),zero_counts=[sum(machine.branches[i].tested==k for i in machine.zero) for k in (0,1)],
                 positive_counts=list(map(len,machine.positive)),moving_counts=list(map(len,machine.moving)),
                 source_all_natural_determinism=True,source_all_natural_injection=True,no_incoming_start=True,no_outgoing_halt=True,
                 horizon_one_input=[1,0],horizon_one_accepts=False,bounded_universal_operations_rejected=blocked,
                 universal_residual_family_or_polynomial_materialized=False,ledgers=ledgers)
    (ROOT/'source-ledger-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='ledgers'},indent=2))

if __name__=='__main__': main()
