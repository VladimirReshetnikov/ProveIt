from pathlib import Path
import sys,json,time,random,hashlib
root=Path('/workspace/scratch/3ca00e1c8dfb');p=root/'baselines/K221_Construction_2026-10-20/portable/runtime';sys.path.insert(0,str(p/'vendor'));import symbolic_runtime as r
sys.path.insert(0,str(root/'ProveIt/Computability/BusyBeaver/Research/ZFC/k218-continuation-search'));import check_joint_fold as c
mp={int(q):z for q,z in json.loads((p/'reference_results/legacy_mapping.json').read_text()).items()};mp.update({301:1301,302:1302})
sites=json.loads((root/'ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k218/sites218.json').read_text());pairs=[(i,b)for i,s in enumerate(sites)for b in((0,1)if s[1]=='CD'else(0,))]
random.Random(217).shuffle(pairs)
# First cover every literal source type and risky right-decrement leaf.
priority=[];seen=set()
for i,s in enumerate(sites):
 key=tuple(s[1:])+(s[0][-1],)
 if key not in seen:
  seen.add(key);priority.extend((i,b)for b in((0,1)if s[1]=='CD'else(0,)))
pairs=list(dict.fromkeys(priority+pairs))
hits=json.loads((root/'root_work/restricted_search_result.json').read_text())['hits']
results=[];start=time.monotonic()
for hit in hits:
 pth=Path(hit['file']);tab,_=c.read(pth);tab={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in tab.items()};i=positive=None
 try:
  lemmas,blocks=r.prove_blocks(tab);nr=0;rows=set();dur=[];steps=0
  for i,positive in pairs:
   ans=r.case(tab,lemmas,sites[i],positive);nr+=1;steps+=ans['symbolic_steps'];rows|=ans['rows'];dur.append(ans['duration'])
   if nr==120:print('120_PASS',pth.name,'time',round(time.monotonic()-start,2),flush=True)
  result={**hit,'status':'ALL_PRIMITIVE_INTERFACES_PROVED','cases':nr,'symbolic_steps':steps,'min_duration':min(d[0]for d in dur),'coverage':len(rows)}
 except Exception as e:result={**hit,'status':'REJECTED','site_index':i,'positive':positive,'reason':str(e)}
 results.append(result);print(json.dumps({k:v for k,v in result.items()if k!='file'}),flush=True)
 (root/'root_work/hit_checks.json').write_text(json.dumps(results,indent=2)+'\n')
 if result['status']=='ALL_PRIMITIVE_INTERFACES_PROVED':break
print('END',time.monotonic()-start,flush=True)
