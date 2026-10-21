from pathlib import Path
import sys,itertools,json,time
root=Path('/workspace/scratch/3ca00e1c8dfb');r=root/'ProveIt/Computability/BusyBeaver/Research/ZFC/k218-continuation-search'
sys.path.insert(0,str(r));import filter_source as f;import check_joint_fold as c
old,s=c.read(root/'root_work/core217.native.tm');Q=sorted({q for q,b in old});I={q:set() for q in Q};rad=9
for line in(root/'root_work/core_contexts.txt').read_text().splitlines():
 v=list(map(int,line.split()));I[v[0]].update(v[1:])
start=time.monotonic();paths={};count=0;hits=[];new=dict(old)
actions=list(itertools.product((0,1),(-1,1),Q+[254]))
for qi,q in enumerate(Q):
 for b in (0,1):
  orig=new[q,b]
  for a in actions:
   if a==orig:continue
   count+=1;new[q,b]=a
   failure=f.local_filter(old,new,I,q,q,paths,197,rad)
   if failure is None:hits.append([q,b,*a])
  new[q,b]=orig
 if qi%25==0:print('PROGRESS',qi,count,len(hits),time.monotonic()-start,flush=True)
json.dump({'status':'FINITE_RUNTIME_DISCOVERY_ONLY','candidates':count,'seconds':time.monotonic()-start,'hits':hits},open(root/'root_work/runtime_rewrites_result.json','w'),indent=2)
(root/'root_work/runtime_rewrites.txt').write_text(''.join(' '.join(map(str,a))+'\n' for a in hits))
print('DONE',len(hits),time.monotonic()-start,flush=True)
