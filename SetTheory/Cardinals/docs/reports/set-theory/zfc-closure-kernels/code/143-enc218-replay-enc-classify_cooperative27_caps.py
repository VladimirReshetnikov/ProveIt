"""Exact outward-sweep/translated-half-tape divergence certificates only."""
import json,time,signal,hashlib
import diagnose_cooperative27 as C
F,D,R=C.F,C.D,C.R

def blank_sweep(T,q,h,ones):
 for d in(-1,1):
  if not(h<min(ones,default=0)if d==-1 else h>max(ones,default=0)):continue
  seen={};rows=[];state=q
  while state not in seen:
   seen[state]=len(rows)
   if(state,0)not in T:break
   w,m,z=T[state,0]
   if m!=d:break
   rows.append([F.iv[state],0,w,m,F.iv[z]]);state=z
  else:return dict(kind='ONE_WAY_FRESH_BLANK_SWEEP',direction=d,head=h,support_min=min(ones,default=None),support_max=max(ones,default=None),rows=rows,cycle_start=seen[state],repeated_state=F.iv[state])
 return None

def translated(T,q,h,ones,limit=512):
 initial=ones.copy();state0=q;head0=h;lo=hi=h;trace=[]
 for k in range(limit):
  if(q,int(h in ones))not in T:return None
  b=int(h in ones);w,d,z=T[q,b];trace.append([F.iv[q],h,b,w,d,F.iv[z]])
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d;q=z;C.TOTAL+=1;lo=min(lo,h);hi=max(hi,h)
  if C.TOTAL>C.CAP:raise TimeoutError('1m new step cap')
  shift=h-head0
  if q!=state0 or shift==0:continue
  if shift>0 and lo>0:
   a={x for x in initial if x>=lo};b={x-shift for x in ones if x>=lo+shift};direction=1;boundary=lo
  elif shift<0 and hi<0:
   a={x for x in initial if x<=hi};b={x-shift for x in ones if x<=hi+shift};direction=-1;boundary=hi
  else:continue
  if a==b:return dict(kind='EXACT_TRANSLATED_HALF_TAPE',direction=direction,period=k+1,shift=shift,initial_state=F.iv[state0],initial_head=head0,final_head=h,head_min=lo,head_max=hi,boundary=boundary,initial_live_ones=sorted(a),final_live_ones=sorted(x+shift for x in b),trace=trace)
 return None

def main():
 begun=time.monotonic();C.TOTAL=0;C.CAP=1_000_000;C.PER=10_000;source=json.load(open(D.D/'COOPERATIVE27_ALL_ACTIONS_CONCRETE.json'));pending=[x for x in source['actions']if x['status']=='UNKNOWN_CAPPED'];regs=[0]*9;spares=[0];gap=0;out=[];status='COMPLETE_BOUNDED_CAP_CLASSIFICATION'
 signal.signal(signal.SIGALRM,lambda*a:(_ for _ in()).throw(TimeoutError('10 second watchdog')));signal.alarm(10)
 try:
  for rec in pending:
   w,d,z=rec['action'];T={r:a for r,a in F.T.items()if r[0]!=F.mp[302]};T[F.mp[103],1]=(0,-1,F.mp[162]);T[F.mp[113],0]=(0,-1,F.mp[27]);T[F.mp[27],0]=(w,d,F.mp[z]);a=C.run(T,regs,spares,gap);assert a['reason']=='per_case_cap';q,h,ones=a['configuration'];entry=R.describe((q,h,ones));entry['state']=F.iv[q]
   proof=blank_sweep(T,q,h,ones)
   if proof is None:proof=translated(T,q,h,ones.copy())
   result=dict(action=rec['action'],fixture=0,prefix_steps=a['steps'],prefix_endpoint=entry,status='PROVED_INTERFACE_DIVERGENCE'if proof else'UNKNOWN',certificate=proof);out.append(result)
  print('classified',len(out),'proved',sum(x['certificate']is not None for x in out),flush=True)
 except TimeoutError as e:status='INCOMPLETE_CAP';out.append(dict(error=str(e)))
 finally:
  signal.alarm(0);r=dict(status=status,cases=out,proved=sum(x.get('certificate')is not None for x in out),unknown=sum(x.get('status')=='UNKNOWN'for x in out),literal_steps=C.TOTAL,seconds=time.monotonic()-begun,proof_rule='A one-way0-reading state cycle advances forever into untouched blank cells. A translated-half-tape certificate repeats the same nonhalting control and head trace, with the entire future-readable half-tape translated by the same nonzero displacement; the discarded half is never read again. The head stays strictly on one side of the required endpoint head0 and moves farther away on each repetition. Both certify failure to complete this concrete primitive interface, not any claim about every equiconsistent interpretation.',source_receipt_sha256=hashlib.sha256((D.D/'COOPERATIVE27_ALL_ACTIONS_CONCRETE.json').read_bytes()).hexdigest());D.dump('COOPERATIVE27_CAP_CERTIFICATES.json',r);print(json.dumps({k:v for k,v in r.items()if k not in('cases',)}),flush=True)
if __name__=='__main__':main()
