#!/usr/bin/env python3
"""Positive control of discovery, plus independent literal replay of every hit."""
from pathlib import Path
import importlib.util,json,subprocess,tempfile
HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('inv',HERE/'invariant.py');inv=importlib.util.module_from_spec(sp);sp.loader.exec_module(inv)
# States 1 and2 write the next symbol before returning through3 and4. State5
# can consequently be entered as5/0 only from3 and5/1 only from4. Existing
# controls8 and9 provide the two required branches, but neither has both rows.
T={
 (0,0):(0,1,1),(0,1):(1,1,2),
 (1,0):(0,-1,3),(1,1):(0,-1,3),
 (2,0):(1,-1,4),(2,1):(1,-1,4),
 (3,0):(0,1,5),(3,1):(1,1,5),
 (4,0):(0,1,5),(4,1):(1,1,5),
 (5,0):(0,1,6),(5,1):(1,1,7),
 (6,0):(0,1,8),(6,1):(1,1,8),
 (7,0):(0,1,9),(7,1):(1,1,9),
 (8,0):(0,1,6),(8,1):(0,1,254),
 (9,0):(1,1,254),(9,1):(1,1,7),
}
R=3;CAP=32;x=inv.analyze(T,0,R,False)
with tempfile.TemporaryDirectory(prefix='elimination-control-') as td:
 inp=Path(td)/'input.txt';out=Path(td)/'result.json'
 with inp.open('w') as f:
  print(R,0,254,10,file=f)
  for q in range(10):print(q,*T[q,0],*T[q,1],len(x['masks'][q]),*x['masks'][q],file=f)
 with out.open('w') as f:subprocess.run([str(HERE/'contextual_eliminate'),str(inp),str(CAP),'1'],stdout=f,check=True)
 result=json.loads(out.read_text());row=next(s for s in result['states'] if s['deleted']==5)
 assert row['passed']==row['total']==4,row
 assert [0,1,8] in next(i for i in row['incoming'] if i['row']==[3,0])['patches']
 assert [1,1,9] in next(i for i in row['incoming'] if i['row']==[4,1])['patches']
 # Independently validate the explicitly chosen whole table by dictionary tapes,
 # retaining all initial window bits and checking positive common configurations.
 U={k:v for k,v in T.items() if k[0]!=5}
 U[3,0]=(0,1,8);U[3,1]=(1,1,8)
 U[4,0]=(0,1,9);U[4,1]=(1,1,9)
 def trace(table,q,m):
  tape={i-R:(m>>i)&1 for i in range(2*R+1)};h=0;out=[]
  for _ in range(CAP):
   if h not in tape or q==254:break
   w,d,q=table[q,tape[h]];tape[h]=w;h+=d
   out.append((q,h,tuple(sorted(tape.items()))))
  return out
 checked=0
 for q in [3,4]:
  for m in x['masks'][q]:
   old=trace(T,q,m);new=trace(U,q,m)
   assert set(old)&set(new),(q,m)
   checked+=1
 assert checked>0
 # Neither existing provider is an identical two-row replacement for state5.
 assert not any((T[q,0],T[q,1])==(T[5,0],T[5,1]) for q in range(10) if q!=5)
 receipt={'status':'PASS','purpose':'Nonuniform predecessor targets and independent exact local replay; not a claim against every possible uniform-fold synthesis grammar','original_states':10,'reduced_states':9,'deleted_state':5,'nonvacuous_contexts_checked':checked,'different_providers':[8,9],'no_identical_two_row_provider':True,'search_found_deletion':True}
 (HERE/'results/control.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
