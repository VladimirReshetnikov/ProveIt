from pathlib import Path
import sys,itertools,collections,json,time
root=Path('/workspace/scratch/3ca00e1c8dfb');r=root/'ProveIt/Computability/BusyBeaver/Research/ZFC/k218-continuation-search'
sys.path.insert(0,str(r));import filter_source as f;import check_joint_fold as c
old,s=c.read(r.parent/'candidate-k218/k218.native.tm');Q=sorted({q for q,b in old});I={q:set()for q in Q};rad=9
for line in(root/'root_work/runtime_contexts_complete.txt').read_text().splitlines():
 v=list(map(int,line.split()));I[v[0]].update(v[1:])
ones=set();q=0;h=0
for tick in range(312909):
 I[q].add(sum(int(h+k in ones)<<(k+rad)for k in range(-rad,rad+1)))
 w,d,q=old[q,int(h in ones)]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
assert(q,h)==(84,-5)
json.dump({q:sorted(v)for q,v in I.items()},open(root/'root_work/discovery_domain9_complete.json','w'))
start=time.monotonic();paths={};count=0;hits=[]
for j,(keep,drop)in enumerate(itertools.combinations(Q,2)):
 phi=lambda q:keep if q==drop else q
 new={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=drop}
 actions=[sorted({(old[q,b][0],old[q,b][1],phi(old[q,b][2]))for q in(keep,drop)})for b in(0,1)]
 common=[b for b in(0,1)if len(actions[b])==1]
 variants=list(itertools.product(*actions))
 if len(common)==1:
  fixed=common[0];other=1-fixed
  for a in itertools.product((0,1),(-1,1),sorted(set(Q)-{drop}|{254})):
   if a in actions[other]:continue
   pair=[None,None];pair[fixed]=actions[fixed][0];pair[other]=a;variants.append(pair)
 for a0,a1 in variants:
  count+=1;new[keep,0]=a0;new[keep,1]=a1
  failure=f.local_filter(old,new,I,keep,drop,paths,197,rad)
  if failure is None:
   out=root/f'root_work/complete_hit{len(hits):04d}.native.tm';out.write_bytes(f.encode(new,phi(s)))
   hits.append({'keep':keep,'drop':drop,'a0':a0,'a1':a1,'file':str(out)});print('HIT',hits[-1],flush=True)
 if j%5000==0:print('PROGRESS',j,count,'hits',len(hits),'time',time.monotonic()-start,flush=True)
json.dump({'status':'FINITE_DISCOVERY_ONLY','candidates':count,'pairs':j+1,'seconds':time.monotonic()-start,'hits':hits},open(root/'root_work/complete_search_result.json','w'),indent=2)
print('DONE',len(hits),time.monotonic()-start,flush=True)
