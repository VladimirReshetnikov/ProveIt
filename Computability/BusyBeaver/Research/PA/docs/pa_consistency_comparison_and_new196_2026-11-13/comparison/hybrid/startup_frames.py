from pathlib import Path
import json,sys,argparse,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent));from contracts import read

def search(table,sites,start,bound=200000):
 T=read(table);ss=json.loads(Path(sites).read_text());leaves={p:(i,o,a)for i,(p,o,a)in enumerate(ss)};maxd=max(map(len,leaves));frames=[]
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
  if header-head<56:return
  here=header+1;regs=[];last=max(ones)
  while here<last:
   if here in ones or here+1 not in ones:return
   end=here+1
   while end in ones:end+=1
   regs.append(end-here-2);here=end
  if len(regs)<10:return
  assert here==last+1
  return {'source_ordinal':leaves[path][0],'source_address':path,'head':head,'header':header,'gap':header-head-56,'physical':regs[:9],'logical':[regs[j]for j in (6,2,0,4,3,7,8,5,1)],'spares':regs[9:]}
 q=start;head=0;ones=set();digest=hashlib.sha256()
 for t in range(bound):
  if q==254:return {'status':'HALTED','steps':t,'start':start,'frames':frames}
  f=frame(q,head,ones)
  if f:
   f['steps']=t;frames.append(f)
   if len(frames)>=50:break
  b=int(head in ones);w,d,n=T[q,b];digest.update(f'{t} {q} {head} {b} {w} {d} {n}\n'.encode())
  (ones.add if w else ones.discard)(head);q=n;head+=d
 return {'status':'SEARCHED','start':start,'bound':bound,'steps':t,'frames':frames,'trace_sha256':digest.hexdigest()}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('sites');p.add_argument('out');p.add_argument('--start',type=int,default=0);p.add_argument('--bound',type=int,default=300000);a=p.parse_args();r=search(a.table,a.sites,a.start,a.bound);Path(a.out).write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items()if k!='frames'});print('frames',len(r['frames']));print(json.dumps(r['frames'][:4],indent=2))
