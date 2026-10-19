#!/usr/bin/env python3
"""Structural/source-pin audit and exact baseline exceptional-visit census.

The finite census establishes startup guards and the 144-step clock identity.
It does not stand in for the separate unbounded instruction proof.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,os
import independent_runtime as r
import symbolic_runtime as s
HERE=Path(__file__).resolve().parent
os.chdir(HERE)
T=r.table(HERE/'baseline240.tm')
U=r.table(HERE/'helper91_target106_239.tm')
S=json.loads((HERE/'sites_logical.json').read_text())
facts=s.validate_inputs(U,S)
assert facts['working_states']==239
assert len({q for q,b in U})==239 and len(U)==478
costs={(80,0):4,(169,0):2,(169,1):4,(91,1):8}
counts=Counter();ones=set();q=95;h=0
for tick in range(409691):
    b=int(h in ones)
    if (q,b) in costs:
        counts[q,b]+=1
        if q==80:assert h-1 in ones
        elif q==169:
            assert h-1 not in ones
            if b:assert h+1 in ones
        elif q==91:assert h-3 not in ones and h-2 in ones and h-1 in ones
    w,d,q=T[q,b]
    if w:ones.add(h)
    else:ones.discard(h)
    h+=d
assert (q,h)==(96,-5)
clock=sum(n*costs[k]for k,n in counts.items())
assert clock==144
# The complete clean baseline frame, including its zero exterior.
expected=r.frame('',[3,0,0,0,3,0,0,0,0],[1]*167,gap=117)
expected={i-5 for i in expected}
assert ones==expected and len(ones)==351
record=dict(status='PASS_INPUT_STRUCTURE_SOURCE_PIN_AND_BOOT_CLOCK',
 input_facts=facts,baseline_steps=409691,predicted_candidate_steps=409691+clock,
 extra_steps=clock,exceptional_visits=[dict(state=q,read=b,count=counts[q,b],extra_per_visit=costs[q,b])for q,b in costs],
 startup_guards_checked_at_every_exceptional_visit=True,baseline_whole_frame_checked=True,
 baseline_state=96,baseline_head=-5,logical_registers=[3,0,0,0,3,0,0,0,0],gap_extra=117,
 primary_count=9,spare_values=[1]*167,one_cell_count=len(ones),
 baseline_ones_sha256=hashlib.sha256((json.dumps(sorted(ones))+'\n').encode()).hexdigest(),
 candidate_sha256=hashlib.sha256((HERE/'helper91_target106_239.tm').read_bytes()).hexdigest(),
 source_sha256=hashlib.sha256((HERE/'sites_logical.json').read_bytes()).hexdigest(),
 scope='Finite exact old startup plus proven positive block simulation. Candidate startup is independently simulated elsewhere.')
(HERE/'input_boot_clock_239.json').write_text(json.dumps(record,indent=2)+'\n')
print({k:v for k,v in record.items()if k!='spare_values'})
