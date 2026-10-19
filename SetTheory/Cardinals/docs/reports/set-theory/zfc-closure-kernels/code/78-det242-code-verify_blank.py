#!/usr/bin/env python3
"""Independent sparse/dense exact blank initialization for detour242."""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def table(p):
 rows={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):start=int(line.split()[-1]);continue
  if not line or line.startswith('#'):continue
  q,b,w,d,t=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(t))
 return rows,start
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 if not __debug__:raise RuntimeError('Run with assertions enabled')
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output',type=Path,default=ROOT/'evidence/blank.json')
 args=ap.parse_args()
 oldp=ROOT/'reference/zfc_combined243_old.tm';newp=ROOT/'machine/zfc_detour242_old.tm';canp=ROOT/'machine/zfc_detour242.tm'
 old,oldstart=table(oldp);new,start=table(newp);canonical,canonical_start=table(canp)
 assert oldstart==start==95 and canonical_start==0
 # Run the pinned predecessor independently, recording the proved detour count.
 assert sha(oldp)=='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
 state,head,ones=oldstart,0,set();count=0;bad27=0
 for _ in range(407967):
  read=int(head in ones);count+=int((state,read)==(15,0));bad27+=int((state,read)==(27,1))
  w,d,state=old[state,read]
  if w:ones.add(head)
  else:ones.discard(head)
  head+=d
 assert (state,head,len(ones))==(96,-5,351) and not bad27
 expected=(state,head,frozenset(ones));old_ones=sorted(ones)
 # Discover the new prefix by literal execution, independently of predicted time.
 state,head,ones=start,0,set();found=None
 for tick in range(3000001):
  if state==96 and head==-5 and len(ones)==351 and frozenset(ones)==expected[2]:found=tick;break
  if tick==3000000:break
  w,d,state=new[state,int(head in ones)]
  if w:ones.add(head)
  else:ones.discard(head)
  head+=d
 assert found is not None
 assert (state,head,frozenset(ones))==expected
 assert found==407967+2*count
 # Fresh dense interpreter using the canonical numbered table and an array tape.
 rows=[None]*(2*242)
 for (q,b),(w,d,t)in canonical.items():rows[2*q+b]=(w,d,t)
 origin=found+1;tape=bytearray(2*found+3);p=origin;q=0
 for _ in range(found):
  w,d,q=rows[2*q+tape[p]];tape[p]=w;p+=d
 denseones=[i-origin for i,b in enumerate(tape)if b]
 mapping=json.loads((ROOT/'machine/renumbering.json').read_text())
 oldmap=mapping.get('old_to_canonical',mapping)
 if 'old_to_new' in mapping:oldmap=mapping['old_to_new']
 dispatcher=int(oldmap['96'])
 assert (q,p-origin,denseones)==(dispatcher,-5,old_ones)
 pos=177;values=[]
 while pos<=max(ones):
  assert pos not in ones and pos+1 in ones
  end=pos+1
  while end in ones:end+=1
  values.append(end-pos-2);pos=end
 physical=values[:9];logical=[physical[i]for i in [6,2,0,4,3,7,8,5,1]];spares=values[9:]
 assert logical==[3,0,0,0,3,0,0,0,0] and spares==[1]*167
 out=dict(status='PASS_EXACT_BLANK_PREFIX_TWO_INTERPRETERS',working_states=242,transitions=484,blank_steps=found,old_blank_steps=407967,old_15_read0_visits=count,
  clock_identity='new_steps=old_steps+2*old_15_read0_visits',old_27_read1_visits=bad27,
  start=0,old_start=95,dispatcher=dispatcher,old_dispatcher=96,head=-5,marker=-6,header=176,span=181,
  logical_registers=logical,physical_registers=physical,spare_count=167,spare_values=spares,
  one_count=351,all_one_positions=denseones,all_other_cells_zero=True,
  sparse_old_label_and_dense_canonical_exact_agreement=True,
  canonical_sha256=sha(canp),old_label_sha256=sha(newp),baseline_sha256=sha(oldp),
  scope='Exact finite initialization only. Universal source/runtime checks establish the unbounded continuation.')
 destination=args.output;destination.parent.mkdir(parents=True,exist_ok=True);destination.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k not in('all_one_positions','spare_values')},indent=2))
if __name__=='__main__':main()
