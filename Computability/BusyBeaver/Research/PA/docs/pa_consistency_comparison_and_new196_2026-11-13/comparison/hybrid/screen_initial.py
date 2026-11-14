from pathlib import Path
import sys,json,argparse,time
sys.path.insert(0,str(Path(__file__).resolve().parent));from contracts import read

def screen(table,sites,bound):
 T=read(table);ss=json.loads(Path(sites).read_text());leaves={p:(i,o,a)for i,(p,o,a)in enumerate(ss)};maxd=max(map(len,leaves));reports=[];starttime=time.monotonic()
 def frame(q,head,ones):
  if q!=84 or head-1 not in ones or any(x<head-1 for x in ones):return
  path=''
  for _ in range(maxd+1):
   if path in leaves:break
   path+=str(int(head+len(path)in ones))
  else:return
  suffix=[x for x in ones if x>=head+len(path)]
  if not suffix:return
  header=min(suffix)
  if header-head<48:return
  here=header+1;regs=[];last=max(ones)
  while here<last:
   if here in ones or here+1 not in ones:return
   end=here+1
   while end in ones:end+=1
   regs.append(end-here-2);here=end
  if len(regs)<10:return
  assert here==last+1
  return {'source_ordinal':leaves[path][0],'source_address':path,'head':head,'header':header,'physical':regs[:9],'logical':[regs[j]for j in (6,2,0,4,3,7,8,5,1)],'spares':regs[9:]}
 for start in sorted({q for q,b in T}):
  q=start;head=0;ones=set();frames=[];status='BOUND'
  for t in range(bound):
   if q==254:status='HALT';break
   if q==84:
    f=frame(q,head,ones)
    if f:
     f['steps']=t;frames.append(f);status='FRAME';break
   b=int(head in ones);w,d,n=T[q,b]
   if n==q and b==0 and ((d==1 and (not ones or head>max(ones)))or(d==-1 and(not ones or head<min(ones)))):
    status='OUTWARD_SELF_LOOP';break
   (ones.add if w else ones.discard)(head);q=n;head+=d
  r={'start':start,'status':status,'steps':t,'q':q,'head':head,'frames':frames};reports.append(r)
  if frames:print('FRAME',r,flush=True)
 print('screen seconds',time.monotonic()-starttime,flush=True)
 return reports
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('sites');p.add_argument('out');p.add_argument('--bound',type=int,default=100000);a=p.parse_args();r=screen(a.table,a.sites,a.bound);Path(a.out).write_text(json.dumps(r,indent=2)+'\n');from collections import Counter;print(Counter(x['status']for x in r))
