#!/usr/bin/env python3
"""Replay the unique quotient from the diverse symbolic screen; it is rejected."""
from pathlib import Path
if not __debug__:
    raise SystemExit('Assertions are required; do not use -O or PYTHONOPTIMIZE.')

# Reuse only the driver's initialization, before any contextual search.
driver=Path(__file__).with_name('symbolic_diverse_merge.py')
exec(driver.read_text().split('\ncontexts=')[0])
saved=json.loads((PACKAGE/'recorded_outputs/symbolic_diverse_solutions.json').read_text())
solutions={tuple(map(int,key.split(','))):list(map(tuple,value)) for key,value in saved.items()}
candidates=[]
for a,b in itertools.combinations([q for q in controls if q not in c.BOXSTATES],2):
    options=[set(solutions[a,x]) & set(solutions[b,x]) for x in (0,1)]
    if all(options):
        for acts in itertools.product(*options):
            candidates.append((a,b,acts))
assert candidates==[(2002,2031,((0,True,12),(1,True,2003)))],candidates
a,b,acts=candidates[0]
trial={(q,x):(w,d,b if n==a else n) for (q,x),(w,d,n) in rows.items() if q!=a}
for x,(w,d,n) in enumerate(acts):
    trial[b,x]=w,d,b if n==a else n
receipt=c.validate(trial,contracts)
assert receipt=={'ok':False,'failed':(1164,None),'completed':1518},receipt
print(json.dumps({'status':'REJECTED_BY_SOURCE_CONTRACT_CHECK','working_states':len(trial)//2,
                  'remove':a,'keep':b,'replacement_rows':acts,'receipt':receipt,
                  'note':'This is a failed symbolic check, not a newly proved concrete countertrace.'},indent=2))
