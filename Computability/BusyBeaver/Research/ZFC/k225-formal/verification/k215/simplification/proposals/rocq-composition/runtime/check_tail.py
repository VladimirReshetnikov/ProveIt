"""Owned exact six-step tail windows, arbitrary exterior untouched."""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from pathlib import Path
import json
from check_decoder import table
D=Path(__file__).parent
out=[]
for name,a in [('K215_Formal',1),('ST215',0),('DR215',0)]:
 t=table(D/'inputs'/f'{name}.tm');cells=[0]*4;q=0;h=0;trace=[]
 for k in range(6):
  assert 0<=h<4,'Exterior read'
  b=cells[h];w,d,z=t[q,b];trace.append([q,h,b,w,d,z]);cells[h]=w;h+=d;q=z
 assert(q,h,cells)==(40,0,[1,0,1,a])
 out.append(dict(table=name,spare=a,trace=trace,endpoint=[q,h,cells]))
(D/'TAIL_WINDOWS.json').write_text(json.dumps(out,indent=2));print('PASS: six-step framed tail for both spare choices')
