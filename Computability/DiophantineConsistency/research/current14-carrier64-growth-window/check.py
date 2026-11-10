#!/usr/bin/env python3
"""Bounded recurrence controls for the external Pell growth argument."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
D=HERE.parents[1]
pins={
 'research/current14-carrier64-power-window-partial/result.json':'fb177a664e0ebde4ef8ee6fbf7291c4b7858111cd75c0349fb5b9e8f95d54e31',
 'research/current14-carrier64-growth-compatible-partial/result.json':'b86798618e49c9636fe989129818665c07da94ddebebcdb4fe463d7d76926703',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
 'Lean/DiophantineConsistency/Compact44/P72Power.lean':'f46584fb3977ae5fc33b31bee18e8c27435d97bea10138f163af2de5ee66d462'}
for file,expected in pins.items():
    if hashlib.sha256((D/file).read_bytes()).hexdigest()!=expected:
        raise RuntimeError(f'pin mismatch: {file}')
partial=json.loads((D/'research/current14-carrier64-power-window-partial/result.json').read_bytes())
if not (partial['R_odd'] and partial['R_gt_3B'] and partial['beta_mersenne_exponent']>=1):
    raise RuntimeError('unexpected symbolic partial witness')

recurrence_cases=0
for p in range(2,31):
    prev,cur=0,1
    for n in range(1,41):
        if not (p**(n-1)<=cur<=(2*p)**(n-1)):
            raise RuntimeError('Pell bounds control failed')
        prev,cur=cur,2*p*cur-prev
        recurrence_cases+=1

growth_cases=0
upper_cases=0
for R in range(27,100,2):
    X=1<<R; N=(R-1)//2
    for B in range(1,min(10,(R-1)//3)+1):
        if not R>3*B:
            continue
        Y=X*(1<<(3*B))
        if not (Y<X*X and X**N>2*(Y+1)*6**N):
            raise RuntimeError('growth contradiction control failed')
        growth_cases+=1
        Ylarge=1<<(R*R+3*B)
        if not (2*Ylarge>(18*X)**N and R*R+3*B>(R+5)*N):
            raise RuntimeError('upper growth contradiction control failed')
        upper_cases+=1
result={'pins':pins,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'recurrence_control_cases':recurrence_cases,'growth_control_cases':growth_cases,
        'upper_growth_control_cases':upper_cases,
        'partial_R_gt_3B':True,'partial_R_odd':True,
        'scope':'finite controls for external proof; no materialized actual witness, Lean run or full-zero claim'}
print(json.dumps(result,sort_keys=True,indent=2))
