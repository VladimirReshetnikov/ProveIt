"""Owned finite-PC-patch synthesis against exact universal219 return frames."""
import direct_screen as D
from itertools import product
from collections import Counter
import json,time,signal
RADIUS=7;WIDTH=15;CAP=2_000_000;cnt=Counter()
def const_prefix(atoms,n):
 out=[]
 for a in atoms:
  if a[0]=='blank':out += [0]*(n-len(out));break
  assert a[0]=='run',('non-run nearby',a)
  bit,c=a[1],a[2];need=n-len(out)
  if c[0]>=need:out += [bit]*need;break
  assert not any(c[1:]),('nonconstant nearby boundary',a,need)
  out += [bit]*c[0]
  if len(out)==n:break
 assert len(out)==n
 return out
def patch(a):
 if a['direction']==1:l=const_prefix(a['left'],7);r=const_prefix(a['right'],8)
 else:l=const_prefix(a['left'],8);r=const_prefix(a['right'],7)
 bits=l[::-1]+r;assert len(bits)==15
 return sum(b<<i for i,b in enumerate(bits))
def step(T,q,h,x):
 b=x>>(h+7)&1;w,m,z=T[q,b];xx=(x&~(1<<(h+7)))|(w<<(h+7));cnt['transitions']+=1
 if cnt['transitions']>CAP:raise TimeoutError('2 million transitions')
 return z,h+m,xx,[q,h,b,w,m,z]
def main():
 began=time.monotonic();signal.signal(signal.SIGALRM,lambda *a:(_ for _ in ()).throw(TimeoutError('60 second cap')));signal.alarm(60)
 T=D.table(D.BASE/'k219.native.tm');mp={int(q):v for q,v in json.loads((D.D/'NATIVE_TO_LEGACY.json').read_text()).items()};inv={v:q for q,v in mp.items()};frames=json.loads((D.D/'RETURN_FULL_CONTRACTS.json').read_text());groups={(103,1):{},(113,0):{}};data=[]
 for a in frames:
  x=patch(a);q=inv[a['state']];row=(q,x>>7&1);groups[row].setdefault(x,[]).append(a['site']);data.append(dict(row=row,word=x,case=a['first_case']))
 D.dump('RETURN_FIXED_PATCHES.json',dict(radius=7,frames=len(data),instances=data,unique={str(k):len(v)for k,v in groups.items()},all_queried_bits_proved_constant=True))
 outcomes=[];status='COMPLETE_RETURN_ACTION_SCREEN';current=None;cache={}
 try:
  for row,words in groups.items():
   goals={}
   for x in words:
    q,h,y=row[0],0,x;tr=[];g={}
    for _ in range(16):
     if not -7<=h<=7 or q==254:break
     q,h,y,r=step(T,q,h,y);tr.append(r)
     if q!=302:g[q,h,y]=tr[:]
    goals[x]=g
   options=[];rejects=Counter()
   for act in product((0,1),(-1,1),sorted({q for q,b in T}-{302})):
    current=dict(row=row,action=act);cnt['actions']+=1;U={r:a for r,a in T.items()if r[0]!=302};U[row]=act;proof=[]
    for x in words:
     q,h,y=row[0],0,x;tr=[];seen=set();found=False
     for _ in range(64):
      if not -7<=h<=7:rejects['patch_escape']+=1;break
      if q==254 or q==302:rejects['deleted_or_halt']+=1;break
      rr=(q,y>>(h+7)&1)
      if rr in groups and rr!=row:rejects['other_pending_edit']+=1;break
      key=q,h,y
      if key in seen:rejects['cycle']+=1;break
      seen.add(key);q,h,y,r=step(U,q,h,y);tr.append(r)
      if(q,h,y)in goals[x]:proof.append(dict(word=x,old=goals[x][q,h,y],new=tr,endpoint=[q,h,y]));found=True;break
     else:rejects['step_cap']+=1
     if not found:break
    else:
     opt=dict(row=row,action=act,cases=len(proof),max_old=max(len(p['old'])for p in proof),max_new=max(len(p['new'])for p in proof),proof=proof);options.append(opt);print('OPTION',json.dumps({k:v for k,v in opt.items()if k!='proof'}),flush=True)
   outcome=dict(row=row,patches=len(words),options=options,rejections=dict(rejects));outcomes.append(outcome);print('ROW',row,'options',len(options),'patches',len(words),flush=True)
 except TimeoutError as e:status='INCOMPLETE_CAP';current=dict(current=current,error=str(e))
 finally:
  signal.alarm(0);out=dict(status=status,counts=dict(cnt),outcomes=outcomes,current=current,seconds=time.monotonic()-began,radius=7,old_step_cap=16,new_step_cap=64,cap=CAP);D.dump('RETURN_SYNTHESIS_RESULT.json',out);print('TERMINAL',json.dumps({k:v for k,v in out.items()if k!='outcomes'}),flush=True)
if __name__=='__main__':main()
