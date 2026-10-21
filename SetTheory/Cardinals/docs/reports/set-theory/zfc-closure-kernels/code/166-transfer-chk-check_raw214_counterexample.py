"""Owned exact complete-frame counterexample to the rejected raw allocation.
The input table is inert data. Sparse and dense independent stores are compared.
"""
from pathlib import Path
import json,hashlib
import independent_runtime as I

def verify(root):
 p=Path(root)/'negative_controls/rejected_raw214.native.tm';T=I.table(p)
 initial=I.frame('01010',[0]*9,[0],0)
 regs=[0]*9;regs[8]=1
 expected=I.frame('01011',regs,[0,1],0)
 q=h=q2=h2=0;q=q2=84;ones=set(initial);left=bytearray(512);right=bytearray(512)
 for x in initial:
  if x>=0:right[x]=1
  else:left[-1-x]=1
 partial_returns=[]
 for tick in range(603):
  if tick and q==84:
   if I.clean_dispatch(96,h,ones):
    assert tick==602;break
   partial_returns.append(tick)
  b=int(h in ones);w,d,q=T[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
  cells,i=(right,h2)if h2>=0 else(left,-1-h2)
  w,d,q2=T[q2,cells[i]];cells[i]=w;h2+=d
 else:raise AssertionError('Expected first complete redispatch not found')
 dense={i for i,b in enumerate(right)if b}|{-i-1 for i,b in enumerate(left)if b}
 assert (q,h)==(q2,h2)==(84,0)and ones==dense and ones!=expected
 assert partial_returns==[154,318]
 return dict(status='EXACT_COMPLETE_FRAME_MISMATCH',table_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),site=['01010','CI',8],input_registers=[0]*9,input_gap=0,input_spares=[0],input_one_cells=sorted(initial),steps_to_first_complete_redispatch=602,earlier_incomplete_dispatch_visits=partial_returns,actual_state=q,actual_head=h,actual_one_cells=sorted(ones),expected_state=84,expected_head=0,expected_registers=regs,expected_spares=[0,1],expected_one_cells=sorted(expected),sparse_dense_agree=True,scope='Counterexample to the intended primitive complete-boundary contract. Not a blank-run or arbitrary-machine nonhalting claim.')

if __name__=='__main__':
 import argparse
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);a.add_argument('--output',type=Path);args=a.parse_args();r=verify(args.root)
 s=json.dumps(r,indent=2)+'\n'
 if args.output:args.output.write_text(s)
 print(s)
