from pathlib import Path
import json,time
H=Path(__file__).resolve().parent
T={}
for l in(H/'B8_parity_folded.tm').read_text().splitlines():
 q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
# The previously proved baseline seed, modulo tape translation.
expected={-1,0,48};pos=49
for x in [0,0,0,0,0,0,2,0,0]+[1]*26:
 pos+=1;expected.update(range(pos,pos+x+1));pos+=x+1
ones=set();q=0;head=0;start=time.time();roots=0;found=None;first=[];bound=2_000_000
for i in range(bound+1):
 if q==75:
  roots+=1
  if {x-head for x in ones}==expected:found=dict(step=i,head=head);break
  if len(first)<10:first.append(dict(step=i,head=head,ones=sorted(ones)))
 if (q,int(head in ones))not in T:
  found=dict(step=i,state=q,head=head,halt=True);break
 w,d,q=T[q,int(head in ones)]
 if w:ones.add(head)
 else:ones.discard(head)
 head+=d
out=dict(status='BASELINE_SEED_REACHED'if found and not found.get('halt') else'HALTED'if found else'BASELINE_SEED_NOT_REACHED_WITHIN_BOUND',bound=bound,result=found,roots=roots,final_state=q,final_head=head,final_ones=len(ones),first_root_visits=first,seconds=time.time()-start,scope='Finite startup search, not a proof of failure to initialize or of nonhalting.')
(H/'B8_startup_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items()if k!='first_root_visits'})
