"""Direct source-matrix replay in two semantics, independent of macrostep choices."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
raw=json.loads((ROOT/'source/UniversalTM15x2.twm.txt').read_text())
triggers=[row[1:] for row in raw[1:]]
a=[row[0] for row in raw[1:]];a[0]=14;a[-1]=2
h=27;deadlines=a[:];physical=a[:];time=0;events=[];counts=[0]*46
for _ in range(1000):
    minimum=min(deadlines);indices=[i for i,x in enumerate(deadlines) if x==minimum]
    dt=min(physical);physical_indices=[i for i,x in enumerate(physical) if x==dt]
    assert len(indices)==1 and physical_indices==indices
    time+=dt;assert time==minimum
    i=indices[0]
    if i==h:break
    events.append({'clock_one_based':i+1,'timestamp':time});counts[i]+=1
    physical=[x-dt+y for x,y in zip(physical,triggers[i])]
    deadlines=[x+y for x,y in zip(deadlines,triggers[i])]
    assert all(x>0 for x in physical) and deadlines==[time+x for x in physical]
else:raise AssertionError('Unexpected fixture event bound reached')
assert len(events)==189 and time==428
out={'status':'PASS','input':{'L':6,'R':0},'prehalt_firings':189,'halt_timestamp':428,
     'halt_clock_one_based':28,'counts':counts,'events':events,
     'method':'Two event-by-event engines; neither chooses events from a macrostep'}
(ROOT/'receipts/halting-example.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['events','counts']},indent=2))
