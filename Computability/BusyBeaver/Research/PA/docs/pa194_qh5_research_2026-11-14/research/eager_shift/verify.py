#!/usr/bin/env python3
"""Rejected 196-state wrapper deletion and valid 197-state no-Shift-halt auxiliary.

This is research evidence, not a state-count improvement. Python 3.10+, stdlib.
The symbolic engine inherits the supplied generic arithmetic-box lemmas.
"""
from pathlib import Path
import argparse, hashlib, json, sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'runtime'))
import compiler as c

def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def read(path):
 rows={}
 for line in path.read_text().splitlines():
  q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d=='R',int(n))
 return rows
def table(rows):return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n' for(q,b),(w,d,n)in sorted(rows.items()))
def pair(a,b):return(a+b)*(a+b+1)//2+b
def unpair(n):
 a=b=0
 for _ in range(n):a,b=(a-1,b+1)if a else(b+1,0)
 return a,b
def onefree(w):
 while w:
  a,w=unpair(w)
  if a==1:return False
 return True
def run(code,pc,rs,stop):
 rs=list(rs)
 for steps in range(1000000):
  if steps and pc==stop:return pc,rs,steps
  r=code[pc]
  if r[0]=='halt':return 'halt',rs,steps
  if r[0]=='inc':rs[r[1]]+=1;pc=r[2]
  elif r[0]=='dec':v=rs[r[1]];rs[r[1]]=max(0,v-1);pc=r[3]if v else r[2]
  else:pc=r[1]
 raise AssertionError('Source fuel exceeded')
def startup(rows,path,limit):
 h=-2;file=[0,0,0,0,0,0,2,0,0]+[1]*26
 expected={h-1,h+48};expected.update(h+i for i,b in enumerate(path)if b)
 p=h+49
 for v in file:p+=1;expected.update(range(p,p+v+1));p+=v+1
 q,h,ones=74,0,set()
 for step in range(1,limit+1):
  w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else-1
  if q==254:return {'halted':True,'steps':step}
  if(q,h,ones)==(84,-2,expected):return {'complete_frame_equal':True,'steps':step,'control':q,'head':h,'one_cells':sorted(ones),'physical_file':file}
 return {'complete_frame_equal':False,'steps':step,'last_control':q,'last_head':h,'scope':'Bounded unsuccessful startup probe, not a nonhalting claim'}
def main(out):
 assert __debug__ and not sys.flags.optimize
 base=read(HERE/'inputs/base.native.tm')
 assert hashlib.sha256(table(base).encode()).hexdigest()=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
 roots={k:tup(v)for k,v in json.loads((HERE/'inputs/base_nodes.json').read_text()).items()}
 grammar=c.read_grammar(HERE/'inputs/grammar.json')
 eager={(164,1):(1,True,400),(400,0):(0,True,130),(400,1):(1,True,401),(401,0):(0,True,63),(401,1):(1,True,68)}
 result={'source_commit':'2337ce611a26e308697ccbddb2a1636f989f01c3','parent_archive':'docs/incoming/pa_sub194_research.zip','accepted_sub194_machine':False,'new_end_to_end_kernel_theorem':False,'variants':{}}
 out.mkdir(parents=True,exist_ok=True)
 for name in ['rejected196','no_shift_halt197']:
  ns=dict(roots);ns['node163']=('node6',('node51',(('leaf','inc',5),'node7')))
  rows=base|eager
  if name=='rejected196':
   ns['node21']=('node6','node20');rows[53,0]=(0,True,77);entry=24
  else:
   ns['node21']=(('node6',('leaf','dec',5)),'node20')
   rows.update({(53,0):(0,True,402),(402,0):(0,True,77),(402,1):(1,True,45)});entry=25
  c.raw_nodes=lambda:ns
  sites,code,contracts=c.source(grammar)
  shift=next(i for i,(p,_,_)in enumerate(sites)if p[:4]==(1,0,1,1))
  # A one-free, fully canonical counterexample avoids relying on consistency.
  rs0=[17,0,3,0,3,0,0,0,2]
  pc,rs,ticks=run(code,shift,rs0,entry)
  wanted=[17,0,0,0,3,2,0,0,2]
  counterexample={'input_registers':rs0,'actual_registers':rs,'intended_total_shift_registers':wanted,'source_steps':ticks,'entry':shift,'return':pc,'input_store_one_free':True}
  if name=='rejected196':assert pc==entry and rs!=wanted
  else:assert pc==entry and rs==wanted
  assert all(rows[q,b]==base[q,b] for q in c.BOXSTATES for b in (0,1))
  valid=c.validate(rows,contracts)
  blank=startup(rows,sites[entry][0],200000 if name=='rejected196' else 100000)
  if name=='rejected196':assert valid=={'ok':False,'failed':(130,(1,True)),'completed':174}
  else:
   assert valid=={'ok':True,'contracts':4769,'max_steps':497,'total_steps':1476396}
   assert blank.get('complete_frame_equal')and blank['steps']==58154
  seen={74};todo=[74]
  while todo:
   q=todo.pop()
   for b in(0,1):
    n=rows[q,b][2]
    if n!=254 and n not in seen:seen.add(n);todo.append(n)
  assert seen=={q for q,b in rows}
  cmdchecks=0
  if name!='rejected196':
   for t in [0,2,3,4]:
    for h in [0,2,3,4]:
     for w in range(40):
      if not onefree(w):continue
      pc,rr,steps=run(code,shift,[17,t,w,0,3,h,0,0,2],entry)
      hd,tl=unpair(w)
      assert pc==entry and rr==[17,h,tl,0,3,hd,0,0,2]
      cmdchecks+=1
  rec={'working_states':len(seen),'rows':len(rows),'source_sites':len(sites),'source_contracts':len(contracts),'symbolic':valid,'startup':blank,'one_free_source_case':counterexample,'bounded_one_free_shift_cases':cmdchecks,'native_sha256':hashlib.sha256(table(rows).encode()).hexdigest()}
  if not valid['ok']:
   i=valid['failed'][0];rec['first_physical_failure']={'site':i,'path':''.join(map(str,sites[i][0])),'instruction':code[i]}
  result['variants'][name]=rec
  (out/(name+'.native.tm')).write_text(table(rows))
  (out/(name+'.nodes.json')).write_text(json.dumps(ns,indent=2)+'\n')
  (out/(name+'.instructions.json')).write_text(json.dumps(code,indent=2)+'\n')
  print(name,json.dumps({k:v for k,v in rec.items()if k!='startup'}),flush=True)
 (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=HERE/'evidence');a=p.parse_args();main(a.output)
