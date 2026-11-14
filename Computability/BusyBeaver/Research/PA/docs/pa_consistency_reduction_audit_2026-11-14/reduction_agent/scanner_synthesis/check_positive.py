#!/usr/bin/env python3
"""Independent concrete replay of the finite compositional scanner contract."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
saved=json.loads((HERE/'seven_state_positive.json').read_text())
rows={(q,b):(w,d,z)for q,b,w,d,z in saved['rows']}
n=7;left=n;right=n+1;end=n+2
assert set(rows)=={(q,b)for q in range(n+2)for b in(0,1)}
assert all(w in(0,1)and d in(-1,1)and 0<=q<=end for w,d,q in rows.values())
for b in(0,1):
 assert rows[left,b]==(b,-1,left if b==0 else 0)
 assert rows[right,b]==(b,1,right if b==0 else end)
examples=[(f'run{m}',m+2,(1<<0)|(1<<(m+1)),m,0)for m in range(7)]
examples.append(('threshold',8,128,6,right))
records=[]
for name,width,bits,head,target in examples:
 q=0;tape={i for i in range(width)if bits>>i&1};initial=set(tape)
 for tick in range(1,saved['steps']+1):
  assert 0<=head<width and q!=end,(name,'read outside supplied prefix')
  w,d,q=rows[q,int(head in tape)]
  (tape.add if w else tape.discard)(head);head+=d
  if q==target and head==-1 and tape==initial:break
 else:raise AssertionError((name,'target contract not met'))
 records.append({'case':name,'steps':tick,'unchanged_tape':True,'target_state':q,'target_relative_head':-1})
print(json.dumps({'status':'PASS','counter_states':n,'helper_states':2,'cases':records},indent=2))
