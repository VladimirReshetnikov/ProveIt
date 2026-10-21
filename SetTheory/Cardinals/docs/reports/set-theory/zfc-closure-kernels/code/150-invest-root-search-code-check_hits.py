#!/usr/bin/env python3
"""Replay the 40 rejected proof checks, reconstructing tables from recorded fold specifications."""
from pathlib import Path
import argparse,sys,json,time,random,hashlib
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--packet-root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();root=a.packet_root.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(root/'core217/vendor'));import symbolic_runtime as r
sys.path.insert(0,str(HERE));import check_joint_fold as c;import filter_source as f
mp={int(q):int(z)for q,z in json.loads((root/'core217/vendor/legacy_mapping.json').read_text()).items()};mp.update({301:1301,302:1302})
sites=json.loads((root/'baseline218/sites218.json').read_text());pairs=[(i,b)for i,s in enumerate(sites)for b in((0,1)if s[1]=='CD'else(0,))]
random.Random(217).shuffle(pairs)
priority=[];seen=set()
for i,s in enumerate(sites):
 key=tuple(s[1:])+(s[0][-1],)
 if key not in seen:
  seen.add(key);priority.extend((i,b)for b in((0,1)if s[1]=='CD'else(0,)))
pairs=list(dict.fromkeys(priority+pairs))
hits=json.loads((HERE.parent/'data/rejected-folds.json').read_text())
old,initial=c.read(root/'baseline218/k218.native.tm');results=[];start=time.monotonic()
for index,hit in enumerate(hits):
 keep,drop=hit['keep'],hit['drop'];phi=lambda q:keep if q==drop else q
 native={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=drop}
 native[keep,0]=tuple(hit['a0']);native[keep,1]=tuple(hit['a1'])
 pth=out/f'rejected-hit{index:04d}.native.tm';pth.write_bytes(f.encode(native,phi(initial)))
 tab={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in native.items()};i=positive=None
 try:
  lemmas,blocks=r.prove_blocks(tab);nr=0;rows=set();dur=[];steps=0
  for i,positive in pairs:
   ans=r.case(tab,lemmas,sites[i],positive);nr+=1;steps+=ans['symbolic_steps'];rows|=ans['rows'];dur.append(ans['duration'])
  result={**hit,'status':'ALL_PRIMITIVE_INTERFACES_PROVED','cases':nr,'symbolic_steps':steps,'min_duration':min(d[0]for d in dur),'coverage':len(rows)}
 except Exception as e:result={**hit,'status':'REJECTED','site_index':i,'positive':positive,'reason':str(e)}
 result['table_sha256']=hashlib.sha256(pth.read_bytes()).hexdigest();results.append(result)
 print(index,result['status'],i,positive,flush=True)
 (out/'hit_checks.json').write_text(json.dumps(results,indent=2)+'\n')
print('END',len(results),'REJECTED',sum(x['status']=='REJECTED'for x in results),time.monotonic()-start,flush=True)
