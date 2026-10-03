import json
from reversible_binary import compile_source
C=compile_source(json.load(open('clean-target-sample-source.json')))
initial=C.encode(C.start,0,0);target=C.encode(C.halt,0,0)
theta=3+2*C.Z+1-4*C.S;first_target=2*theta+2;period=2*first_target+2
x=initial;rows=[];hits=[]
for t in range(period):
    if x==target:hits.append(t)
    rows.append(dict(t=t,ones=sorted(x),exact_target=x==target))
    x=C.step(x)
if x!=initial or len({tuple(r['ones']) for r in rows})!=period or hits!=[first_target]:
    raise RuntimeError('Clean-target orbit regression failed')
ledger=C.ledger()
json.dump(dict(source_file='clean-target-sample-source.json',input_counters=[0,0],ledger=ledger,forward_original_leg=theta,first_exact_target=first_target,reflection_period=period,exact_target_ones=sorted(target),states=rows),open('clean-target-sample-orbit.json','w'),indent=2)
receipt=dict(status='passed',ledger=ledger,initial_ones=sorted(initial),target_ones=sorted(target),theta=theta,first_exact_target=first_target,reflection_period=period,exact_target_hits=hits)
json.dump(receipt,open('clean-target-sample-receipt.json','w'),indent=2)
print(json.dumps(receipt,indent=2))
