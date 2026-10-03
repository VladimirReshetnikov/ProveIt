#!/usr/bin/env python3
"""Count enabled zero/positive product cells and source-tail variables exactly."""
from verify_pins import verify_inputs
verify_inputs()
import json,hashlib
from pathlib import Path
from collections import Counter
R=Path(__file__).resolve().parent
raw=(R/'source.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3':raise ValueError('Source does not match the audited pin')
s=json.loads(raw)
if type(s['class_cut']) is not int or s['class_cut']!=0:raise ValueError('This ledger requires class_cut zero')
counts=Counter();B=r=P=0
for e in s['branches']:
    g=e['guard']
    for a in range(2):
        for b in range(2):
            c=(a,b)
            if g['op']=='true' and set(g)=={'op'}:yes=True
            elif g['op'] in ('eq','gt') and set(g)=={'op','counter','value'} and type(g['counter']) is int and g['counter'] in (0,1) and type(g['value']) is int and g['value']==0:
                yes=c[g['counter']]==0 if g['op']=='eq' else c[g['counter']]>0
            else:raise ValueError('Unsupported guard in literal class ledger')
            if yes:B+=1;r+=a+b;P+=e['delta']!=0
out=dict(status='passed',source_sha256=hashlib.sha256((R/'source.json').read_bytes()).hexdigest(),class_cut=0,enabled_branch_cells_B=B,tail_occurrences_r=r,moving_branch_cells_P=P,existing_residual_core_substitution=dict(variables_per_H=B+r+2,squares_per_H=2*B+4,constant_squares=1),scope='Exact indexed class-cell count; residual-core formulas are the existing Report15 dependency, no giant polynomial JSON materialized')
if (B,r,P)!=(350054,411291,199004):raise RuntimeError('Class count changed')
(R/'class-expansion-ledger.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
