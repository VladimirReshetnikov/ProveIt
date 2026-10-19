#!/usr/bin/env python3
"""Independent symbolic base/step certificate for the closed copy-loop rewrite.

The two schemas quantify over natural n,m. The explicit induction proof is in
proof.md. No finite bound on either register is used and no optimizer is imported.
"""
from pathlib import Path
import json,argparse

def require(p,m):
 if not p:raise ValueError(m)

OLD=((('CD',6),(('CI',5),('CC',2))),('CI',5))
NEW=(('CI',5),(('CD',6),('CC',2)))
OUT='normal_return'

def leaves(t,p=''):
 if isinstance(t[0],str):return[(p,*t)]
 return leaves(t[0],p+'0')+leaves(t[1],p+'1')

def graph(t):
 ps=leaves(t);spans={}
 for i,(p,*_)in enumerate(ps):
  for k in range(len(p)+1):
   z=p[:k]
   if z not in spans:spans[z]=[i,i+1]
   else:spans[z][1]=i+1
 def target(j):return j if j<len(ps)else OUT
 def jump(p,ch,n):
  where=[i for i,c in enumerate(p)if c==ch]
  require(len(where)>=n,'escaping branch')
  prefix=p[:where[-n]]
  return target(spans[prefix][1 if ch=='0'else 0])
 rows=[]
 for i,(p,o,r)in enumerate(ps):
  if o=='CI':rows.append((o,r,target(i+1)))
  elif o=='CD':rows.append((o,r,jump(p,'0',1),target(i+1)))
  elif o=='CC':rows.append((o,r,jump(p,'1',r)))
  else:raise ValueError('unexpected leaf opcode')
 return rows

# Affine expressions: (constant, coefficient of n, coefficient of m).
def add1(a):return(a[0]+1,*a[1:])
def sub1(a):
 require(a[0]>=1 and all(x>=0 for x in a),'decrement not proved positive')
 return(a[0]-1,*a[1:])
ZERO=(0,0,0);N=(0,1,0);M=(0,0,1)

def segment(g,r6,steps):
 regs={5:M,6:r6};pc=0;trace=[]
 for _ in range(steps):
  require(pc!=OUT,'premature return')
  row=g[pc];old=pc;o,r=row[:2]
  if o=='CI':regs[r]=add1(regs[r]);pc=row[2]
  elif o=='CD':
   if regs[r]==ZERO:pc=row[2]
   else:regs[r]=sub1(regs[r]);pc=row[3]
  elif o=='CC':pc=row[2]
  trace.append(dict(pc=old,row=row,next=pc,R5=regs[5],R6=regs[6]))
 require(set(regs)=={5,6},'touched another register')
 return pc,regs,trace

def main():
 go,gn=graph(OLD),graph(NEW)
 require(go==[('CD',6,3,1),('CI',5,2),('CC',2,0),('CI',5,OUT)],'old graph differs')
 require(gn==[('CI',5,1),('CD',6,OUT,2),('CC',2,0)],'new graph differs')
 records=[]
 for name,r6,steps,expected_pc,expected_regs in [
  ('base_n_zero',ZERO,2,OUT,{5:add1(M),6:ZERO}),
  ('step_n_plus_one',add1(N),3,0,{5:add1(M),6:N})]:
  po,ro,to=segment(go,r6,steps);pn,rn,tn=segment(gn,r6,steps)
  require(po==pn==expected_pc and ro==rn==expected_regs,'symbolic schema differs')
  records.append(dict(schema=name,old_trace=to,new_trace=tn,matching_registers=ro,matching_control=po,primitive_steps=steps))
 report=dict(status='PASS_SYMBOLIC_INDUCTIVE_LOOP_SCHEMAS',register_domain='all natural n,m',other_registers='untouched',base_and_induction_step=records,source_instruction_duration='3*n+2',proof_scope='Independent symbolic base/step validation; uniform induction and contextual closure explained in proof.md. No binary TM state count or Rocq rebuild.')
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 args.output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items()if k!='base_and_induction_step'},indent=2))

if __name__=='__main__':main()
