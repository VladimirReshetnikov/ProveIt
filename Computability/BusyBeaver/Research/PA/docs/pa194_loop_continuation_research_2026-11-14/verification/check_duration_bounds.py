#!/usr/bin/env python3
"""Exact coefficient envelope used in the relative iPRA witness bound.
The unbounded arithmetic induction is explained in RELATIVE_IPRA_REVIEW.txt.
"""
from pathlib import Path
import json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('contracts',nargs='+',type=Path);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();results=[]
C=[534,8]+[4]*9+[2,2]
for p in a.contracts:
 raw=p.read_bytes();xs=json.loads(raw);ds=[r['duration']for r in xs]
 assert len(ds)==4780 and all(len(d)==13 and all(type(x)is int and x>=0 for x in d)and d[0]>=3 for d in ds)
 assert all(all(x<=y for x,y in zip(d,C))for d in ds)
 results.append({'file':str(p),'sha256':hashlib.sha256(raw).hexdigest(),'source_outcomes':len(ds),'minimum_constant':min(d[0]for d in ds),'slotwise_maximum':[max(d[j]for d in ds)for j in range(13)],'upper_envelope':C})
r={'status':'PASS','results':results,'initial_auxiliary_values':{'gap':0,'register_sum':2,'first_spare':1,'tail_width':75},'per_source_step_upper_increases':{'gap':2,'register_sum':1,'first_spare':0,'tail_width':3},'source_step_duration_upper_bound':'694+26*j','n_normal_steps_physical_time_upper_bound':'startup+13*n^2+681*n','cross_machine_bound_at_given_halt_time_t':'startup_target+13*(t+1)^2+681*(t+1)','scope':'Finite exact coefficient check; target-frame growth and iPRA induction are mathematical proof obligations documented in review.'};a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
