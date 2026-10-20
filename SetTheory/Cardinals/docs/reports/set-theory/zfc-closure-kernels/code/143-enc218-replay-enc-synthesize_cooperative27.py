"""Joint fixed caller reroutes plus one unknown existing helper row.

No candidate is accepted on finite samples: gates and captures are symbolic
whole tapes over all natural parameters. Full source replay is a later gate.
"""
import sys,json,time,signal
from collections import Counter
import synthesize_full_returns as F
D,S=F.D,F.S

def fullframe(pos):
 site=['000','CD',8];values=[S.var(2+i)for i in range(9)];values[8]=S.add(S.num(1),values[8])if pos else S.ZERO
 phy=[None]*9
 for i,j in enumerate(S.r.PHY):phy[j]=values[i]
 s=S.State(96,[S.bit(1),S.BLANK],[S.bit(0)]*3+[S.run(0,S.add(S.var(1),S.num(61))),S.bit(1)]+S.file_bits(phy));q,d,l,r=s.key()
 return dict(state=q,direction=d,left=l,right=r,site=[0,site,pos],first_case=-2 if pos else -1)

def goal(f):
 if f['first_case']>=0:return F.target(f)
 pos=f['site'][2];values=[S.var(2+i)for i in range(9)]
 if not pos:values[8]=S.ZERO
 phy=[None]*9
 for i,j in enumerate(S.r.PHY):phy[j]=values[i]
 pc='001'if pos else'01';delta=1 if pos else 0
 # Zero CD strips final0 from000 to00, then increments00 to01.
 return S.State(96,[S.bit(1),S.BLANK],[S.bit(int(b))for b in pc]+[S.run(0,S.add(S.var(1),S.num(64+delta-len(pc)))),S.bit(1)]+S.file_bits(phy)).key()

def main():
 began=time.monotonic();F.CAP=1_000_000;F.LIMIT=512;F.counts.clear();Q=sorted({q for q,b in F.N}-{302});row=F.mp[27],0
 assert not any(tuple(e[1][:2])==row for b in F.blocks for e in b['trace']if e[0]!='list')
 frames=[fullframe(False),fullframe(True)];priority=[4570,4588,4602,4711,4597,4717,0];pending=F.frames.copy()
 pending.sort(key=lambda f:(priority.index(f['site'][0])if f['site'][0]in priority else len(priority),f['site'][0]))
 frames+=pending;cache={};outcomes=[];reasons=Counter();best=0;near=[];status='COMPLETE_BOUNDED_COOPERATIVE27_SCREEN';current=None
 signal.signal(signal.SIGALRM,lambda*a:(_ for _ in()).throw(TimeoutError('90 second cap')));signal.alarm(90)
 try:
  for w,d in[(0,-1),(0,1),(1,-1),(1,1)]:
   for z in Q:
    F.counts['actions']+=1;current=[w,d,z];T={r:a for r,a in F.T.items()if r[0]!=F.mp[302]};T[F.mp[103],1]=(0,-1,F.mp[162]);T[F.mp[113],0]=(0,-1,F.mp[27]);T[row]=(w,d,F.mp[z]);proof=[]
    try:
     for f in frames:
      key=f['first_case']
      if key not in cache:g=goal(f);cache[key]=g,F.old_run(f,g)
      g,old=cache[key];a=F.run(T,f,g);assert a['motion']==old['motion'],('motion',a['motion'],old['motion']);proof.append(dict(case=key,index=f['site'][0],old=old,new=a))
    except(AssertionError,RuntimeError,KeyError)as e:
     why=type(e).__name__+':'+str(e).split('(')[0][:80];reasons[why]+=1
     if len(proof)>best:best=len(proof);near=[]
     if len(proof)==best and len(near)<12:near.append(dict(action=current,passed=best,failed_case=f['first_case'],failed_index=f['site'][0],error=repr(e)))
    else:
     outcomes.append(dict(action=current,proof=proof));out=D.D/f'cooperative27-hit-{len(outcomes):02d}';out.mkdir(exist_ok=True)
     native={(F.iv[q],b):(w,d,F.iv[z])for(q,b),(w,d,z)in T.items()};import mixed_detours as M
     (out/'candidate.native.tm').write_bytes(M.enc(native));(out/'proof.json').write_text(json.dumps(outcomes[-1],indent=2)+'\n');print('HIT',current,flush=True)
 except TimeoutError as e:status='INCOMPLETE_CAP';current=dict(action=current,error=str(e))
 finally:
  signal.alarm(0);receipt=dict(status=status,counts=dict(F.counts),rejections=dict(reasons),best_passed=best,near=near,hits=outcomes,seconds=time.monotonic()-began,current=current,scope='Fixed103/1=0L162,113/0=0L27; all872 existing-state27/0 actions,512rules/case; no302; two full CD8 guards then captured complete return contracts. Unsupported symbolic traces and caps are inconclusive. Full source replay and startup required for any survivor.');D.dump('COOPERATIVE27_RESULT.json',receipt);print(json.dumps({k:v for k,v in receipt.items()if k!='hits'}),flush=True)
if __name__=='__main__':main()
