#!/usr/bin/env python3
"""Locate the first actual blank-run use of native row190/1, then stop.

Both final dense and native tables advance literally in lockstep on separate
finite-support tapes.  At the first hit, the whole resulting tape of the
accelerated one-step fragment is compared with the loop parent's three-step
fragment.  This bounded materiality check is not a consistency calibration.
"""
from pathlib import Path
import argparse,hashlib,json,time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def parse(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.startswith('#'):continue
  q,b,w,d,n=line.split();key=(int(q),int(b))
  assert key not in rows
  rows[key]=(int(w),1 if d=='R' else -1,int(n))
 return rows

def tape_info(ones):
 cells=sorted(ones)
 canonical=(json.dumps(cells,separators=(',',':'))+'\n').encode('ascii')
 return {'one_count':len(cells),'leftmost_one':cells[0]if cells else None,
         'rightmost_one':cells[-1]if cells else None,
         'complete_tape_sha256':hashlib.sha256(canonical).hexdigest()}

def fragment(rows,q,head,ones,steps):
 ones=set(ones);trace=[]
 for i in range(steps):
  read=int(head in ones);w,d,n=rows[q,read]
  (ones.add if w else ones.discard)(head)
  trace.append({'relative_transition_index':i,'before_state':q,'before_head':head,
                'read':read,'write':w,'move':'R'if d==1 else'L',
                'after_state':n,'after_head':head+d,**tape_info(ones)})
  q,head=n,head+d
 return q,head,ones,trace

def check(name,cap):
 path=ROOT/'machines'/name
 native=parse(path/'machine.native.tm');dense=parse(path/'machine.tm')
 parent=parse(path/'loop_parent.native.tm')
 labels=json.loads((path/'labels.json').read_text());index={q:i for i,q in enumerate(labels)}
 assert labels[0]==74 and labels[-1]==254
 assert {(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in dense.items()}==native
 assert native[190,1]==(0,-1,42)
 assert parent[190,1]==(1,-1,73)
 assert parent[73,1]==(1,1,83) and parent[83,1]==(0,-1,42)
 qn,qd,hn,hd=74,0,0,0
 on,dn=set(),set();uses={'26/1':0,'101/0':0,'190/1':0}
 base={'machine':name,'transition_cap':cap,
       'native_sha256':sha(path/'machine.native.tm'),
       'dense_sha256':sha(path/'machine.tm'),
       'loop_parent_sha256':sha(path/'loop_parent.native.tm'),
       'initial_configuration':'Native74/dense0, head0, all-zero two-way tape.',
       'dense_native_table_conjugacy_checked':True}
 started=time.time()
 for step in range(cap):
  assert labels[qd]==qn and hn==hd
  if qn==254:
   assert on==dn
   return dict(base,status='HALTED_BEFORE_HIT',literal_transitions=step,
               final_native_state=qn,final_dense_state=qd,final_head=hn,
               **tape_info(on),elapsed_seconds=time.time()-started)
  bn,bd=int(hn in on),int(hd in dn);assert bn==bd
  if(qn,bn)==(190,1):
   assert on==dn
   left=int(hn-1 in on);assert left==1
   before={'native_state':qn,'dense_state':qd,'head':hn,'left_bit':left,
           'current_bit':bn,'right_bit':int(hn+1 in on),**tape_info(on)}
   nq,nh,nt,newtrace=fragment(native,qn,hn,on,1)
   pq,ph,pt,oldtrace=fragment(parent,qn,hn,on,3)
   dq,dh,dt,densetrace=fragment(dense,qd,hd,dn,1)
   assert(nq,nh,nt)==(pq,ph,pt)
   assert(labels[dq],dh,dt)==(nq,nh,nt)
   assert(nq,nh)==(42,hn-1)
   init=json.loads((path/'receipt.json').read_text())['startup']['steps']
   return dict(base,status='FIRST_HIT_VERIFIED',
     first_zero_based_transition_index=step,
     preceding_literal_transitions=step,
     transition_number_one_based=step+1,
     native_and_dense_prefixes_simulated_literally=True,
     whole_prefix_tapes_agree=True,
     startup_steps=init,strictly_after_startup=step>=init,
     earlier_shortcut_uses=uses,before=before,
     after={'native_state':nq,'dense_state':dq,'head':nh,**tape_info(nt)},
     accelerated_native_trace=newtrace,accelerated_dense_trace=densetrace,
     loop_parent_three_step_trace=oldtrace,
     complete_tape_equality_checked_by_set_equality=True,
     accelerated_one_step_equals_loop_parent_three_steps=True,
     elapsed_seconds=time.time()-started)
  if(qn,bn)in((26,1),(101,0)):uses[f'{qn}/{bn}']+=1
  wn,mn,nn=native[qn,bn];wd,md,nd=dense[qd,bd]
  assert(wn,mn,nn)==(wd,md,labels[nd])
  (on.add if wn else on.discard)(hn)
  (dn.add if wd else dn.discard)(hd)
  qn,qd,hn,hd=nn,nd,hn+mn,hd+md
 assert on==dn
 return dict(base,status='NO_HIT_WITHIN_CAP',literal_transitions=cap,
             final_native_state=qn,final_dense_state=qd,final_head=hn,
             final_read=int(hn in on),**tape_info(on),elapsed_seconds=time.time()-started)

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--cap',type=int,default=2000000)
 ap.add_argument('--output',type=Path,required=True)
 a=ap.parse_args();assert a.cap>0
 results=[]
 for name in('PA194LCG','PA194LCGS'):
  result=check(name,a.cap);results.append(result)
  print(name,result['status'],result.get('first_zero_based_transition_index'),flush=True)
 result={'purpose':'Verify that the new continuation shortcut actually executes on each blank run.',
         'index_convention':'Zero-based transition index t is the configuration after exactly t preceding literal transitions.',
         'tape_hash_encoding':'SHA256 of ASCII JSON of the sorted complete finite set of one-cell coordinates, compact separators, followed by one newline; every other tape cell is zero.',
         'results':results,'both_hit':all(r['status']=='FIRST_HIT_VERIFIED'for r in results),
         'scope':'Finite blank-run materiality and full-configuration local synchronization only; not a proof of nonhalting or PA consistency.'}
 a.output.parent.mkdir(parents=True,exist_ok=True)
 a.output.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
