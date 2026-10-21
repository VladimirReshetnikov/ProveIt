#!/usr/bin/env python3
"""Exact arbitrary-completion diamond for native81/0:0L92 ->0L111.
The only assumed input bit is the trigger0; both choices of the left bit are
checked. No other tape cell is read. Shared exterior arbitrary bi-infinite.
"""
from pathlib import Path
import json,argparse,hashlib

def load(path):
 t={}
 for line in Path(path).read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
 return t

def run(t,bit,steps):
 tape={-1:bit,0:0};h=0;q=81;trace=[[q,h,dict(tape)]]
 for _ in range(steps):
  assert h in tape,'Reads outside the universally quantified two-cell window'
  w,d,q=t[q,tape[h]];tape[h]=w;h+=d;trace.append([q,h,dict(tape)])
 return(q,h,tape),trace

def main():
 ap=argparse.ArgumentParser();ap.add_argument('parent',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args()
 old=load(a.parent);assert old[81,0]==(0,-1,92)
 required={(92,0):(0,1,104),(111,0):(0,1,104),(92,1):(1,1,107),(111,1):(1,1,128),(107,0):(0,1,21),(128,0):(0,1,21)}
 assert all(old[k]==v for k,v in required.items())
 new=old.copy();new[81,0]=(0,-1,111)
 cases=[]
 for bit,steps in((0,2),(1,3)):
  end1,tr1=run(old,bit,steps);end2,tr2=run(new,bit,steps)
  assert end1==end2;assert end1[2]=={-1:bit,0:0}
  cases.append(dict(left_bit=bit,steps=steps,old_trace=tr1,new_trace=tr2))
 # An explicit wrong target must fail the exact diagram.
 corrupt=new.copy();corrupt[81,0]=(0,-1,254)
 try:run(corrupt,0,2)
 except KeyError:pass
 else:raise AssertionError('Negative control failed')
 out=dict(status='UNCONDITIONAL_TWO_CELL_DIAMOND_PASS',source_sha256=hashlib.sha256(a.parent.read_bytes()).hexdigest(),rewritten_row=[81,0,0,'L',111],cases=cases,scope='All binary tapes and every head position, whenever entering native81 scanning0. Both microcomputations preserve the entire tape, meet after2or3 positive steps, and never read an unspecified cell. Other rows unchanged, so exact halting equivalence follows for every corresponding start. No assumption about source ordinal, register values, or scanner invariant.')
 if a.output:a.output.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
