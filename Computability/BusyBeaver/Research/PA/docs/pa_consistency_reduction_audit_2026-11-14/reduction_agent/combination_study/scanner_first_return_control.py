#!/usr/bin/env python3
"""Show why a first root return need not be a complete instruction boundary."""
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'inputs'))
import symbolic_runtime as s
base,_=s.machine();sites,instructions=s.program()
assert instructions[25]==('dec',8,27,26)
def frame(site):
 ones={-1,48}|{i for i,b in enumerate(sites[site][0])if b};pos=49
 for v in[0,0,0,0,0,0,2,0,0]+[1]*26:
  ones.update(range(pos+1,pos+v+2));pos+=v+2
 return ones
expected=frame(27);reports=[]
for shorten in(False,True):
 table=dict(base)
 if shorten:
  table[23,0]=(0,False,75);del table[34,0];del table[34,1]
 q,h,tape=84,0,frame(25);returns=[];matched=None
 for tick in range(1,2001):
  w,d,q=table[q,int(h in tape)];(tape.add if w else tape.discard)(h);h+=1 if d else-1
  if q==84:
   if len(returns)<5:returns.append({'step':tick,'head':h,'different_cells_from_successor':len(tape^expected)})
   if h==0 and tape==expected:matched=tick;break
  if q==254:break
 reports.append({'shortened':shorten,'first_root_returns':returns,'exact_successor_reached_at':matched,'tested_through':tick})
assert reports[0]['first_root_returns'][0]=={'step':120,'head':0,'different_cells_from_successor':43}
assert reports[0]['exact_successor_reached_at']==462
assert reports[1]['first_root_returns'][0]=={'step':118,'head':0,'different_cells_from_successor':43}
print(json.dumps({'scope':'Concrete supplied-frame control only. The parent itself has incomplete intermediate root returns; hence a first-return tape mismatch alone cannot reject the complete instruction contract. No inference about the candidate blank run is made.','runs':reports},indent=2))
