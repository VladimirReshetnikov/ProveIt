#!/usr/bin/env python3
"""Build and verify two exact 3-to-1 physical accelerations.

Place this directory inside the AX11GH/GHS packet, or supply --packet.
The local guard checker uses only transition rows, not arithmetic-box oracles.
The optional complete source replay uses the packet's attributed executor.
"""
from pathlib import Path
import argparse,sys,json,hashlib,itertools,shutil
HERE=Path(__file__).resolve().parent
PATCH={(26,1):(1,True,91),(101,0):(0,True,17)}

def parse(path):
 r={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  assert(q,b)not in r and b in(0,1)and w in(0,1)and d in('L','R')
  r[q,b]=(w,d=='R',n)
 return r
def text(r):return ''.join(f"{q} {b} {w} {'R'if d else'L'} {n}\n"for(q,b),(w,d,n)in sorted(r.items()))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')

def check_guards(r,start=74,halt=254):
 """Finite structural hypotheses for the paper's predecessor induction."""
 assert start not in(11,26,101)
 pred=lambda q:[(p,b,w,d)for(p,b),(w,d,n)in sorted(r.items())if n==q]
 assert pred(101)==[(96,0,0,True)]
 assert pred(26)==[(11,0,0,False),(101,0,0,False)]
 assert pred(11)and all(w==0 for p,b,w,d in pred(11))
 assert r[101,0]==(0,False,26)and r[26,0]==(0,True,194)and r[194,0]==(0,True,17)
 assert r[26,1]==(1,True,42)and r[42,0]==(0,True,13)and r[13,0]==(0,False,91)
 assert halt not in(11,26,101,42,13,194,17,91)
 fast=dict(r);fast.update(PATCH)
 def run(rows,q,t,n):
  h=0;t=dict(t);trace=[]
  for _ in range(n):
   trace.append([q,h,dict(t)])
   w,d,q=rows[q,t.get(h,0)];t[h]=w;h+=1 if d else-1
  return q,h,tuple(sorted(t.items())),trace
 cases=[]
 for bits in itertools.product((0,1),repeat=5):
  t=dict(zip(range(-2,3),bits))
  for q in(26,101):
   guard=(t[0]==1 and t[1]==t[2]==0)if q==26 else(t[-1]==t[0]==0)
   if not guard:continue
   old=run(r,q,t,3);new=run(fast,q,t,1)
   assert old[:3]==new[:3]and all(x[0]!=halt for x in old[3])
   cases.append(dict(state=q,window=bits,old_steps=3,new_steps=1,final_state=old[0],head=old[1]))
 assert len(cases)==12
 return dict(status='PASS',start=start,halt=halt,predecessors_101=pred(101),predecessors_26=pred(26),
   predecessors_11=pred(11),local_cases=cases,
   guard_proof='Backward inspection of the last two or three transitions; see acceleration_proof.tex.',
   theorem_scope='Every parent run beginning in control74, on any complete tape at any head position; not merely the blank prefix.',
   arithmetic_claim='The two trace translations use primitive recursion and bounded case analysis, giving the relative halting equivalence in iPRA. This is a written argument, not a compiled Lean theorem.')

def build(packet,family,full):
 sys.path.insert(0,str(packet/'construction'))
 import compiler as c
 import support as support
 inp=packet/'machines'/family;name=family+'F';out=HERE/'machines'/name;out.mkdir(parents=True,exist_ok=True)
 parent=parse(inp/'machine.native.tm');guards=check_guards(parent)
 child=dict(parent);child.update(PATCH)
 dense,labels=support.dense_table(child,194)
 assert len(child)==388 and len({q for q,b in child})==194
 sites=json.loads((inp/'sites.json').read_text());ins=json.loads((inp/'instructions.json').read_text())
 def frame(i,extra=0,effect=c.PLAIN):return c.frame(tuple(map(int,sites[i][0])),extra,effect)
 def target(i,extra=0,effect=c.PLAIN):return c.canonical(frame(i,extra,effect))
 contracts=[]
 for i,code in enumerate(ins):
  st=frame(i)
  if code[0]=='inc':
   _,r,n=code;contracts.append((i,None,st,target(n,0,('x','inc',c.PHYSICAL[r]))))
  elif code[0]=='dec':
   _,r,z,p=code;contracts.append((i,(c.PHYSICAL[r],True),st,target(z)));contracts.append((i,(c.PHYSICAL[r],False),st,target(p,1,('x','dec',c.PHYSICAL[r]))))
  elif code[0]=='jump':contracts.append((i,None,st,target(code[1])))
  else:contracts.append((i,None,st,None))
 runtime=c.validate(child,contracts)if full else None
 if full:assert runtime['ok']
 startup=support.startup(child,tuple(map(int,sites[25][0])))
 before=json.loads((inp/'receipt.json').read_text())['startup']
 for key in('state','head','physical_file','complete_tape_equality','one_cells'):assert startup[key]==before[key]
 # Literal synchronization through the complete initialization, with an exact
 # parent/new clock relation at every candidate transition, not sampled traces.
 q=74;head=0;ones=set();old_clock=0;uses={26:0,101:0}
 for tick in range(startup['steps']):
  b=int(head in ones);k=3 if(q,b)in PATCH else 1
  if k==3:uses[q]+=1
  oq,oh,ot=q,head,set(ones)
  for j in range(k):
   w,d,oq=parent[oq,int(oh in ot)];(ot.add if w else ot.discard)(oh);oh+=1 if d else-1
  w,d,q=child[q,b];(ones.add if w else ones.discard)(head);head+=1 if d else-1
  assert(q,head,ones)==(oq,oh,ot)
  old_clock+=k
 assert old_clock==before['steps']and(q,head,sorted(ones))==(startup['state'],startup['head'],startup['one_cells'])
 (out/'machine.native.tm').write_text(text(child));(out/'machine.tm').write_text(text(dense));dump(out/'labels.json',labels)
 for filename in('sites.json','instructions.json'):shutil.copyfile(inp/filename,out/filename)
 dump(out/'guard_certificate.json',guards)
 receipt=dict(family=name,parent=family,status='PASS',working_states=194,transition_rows=388,
    physical_patch=[[q,b,list(parent[q,b]),list(v)]for(q,b),v in PATCH.items()],
    full_source_replay=full,source_sites=len(sites),source_outcomes=len(contracts),runtime=runtime,
    startup=startup,parent_startup_steps=before['steps'],startup_shortcut_uses=uses,
    exact_clock_identity='parent_steps = accelerated_steps + 2*(uses26 + uses101)',
    whole_prefix_synchronized=True,dense_sha256=sha(out/'machine.tm'),native_sha256=sha(out/'machine.native.tm'),
    iPRA_consistency_equivalence='Uses the separate parent calibration assessed in the enclosing report; the acceleration itself has a complete written primitive-recursive simulation proof.',kernel_checked=False)
 dump(out/'receipt.json',receipt);print(json.dumps(receipt),flush=True);return receipt

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--packet',type=Path,default=HERE.parent);ap.add_argument('--full',action='store_true');args=ap.parse_args()
 assert __debug__
 for family in('PA194AX11GH','PA194AX11GHS'):build(args.packet,family,args.full)
