"""Reproducible bounded walks through closed, neutral decoder rotations."""
from pathlib import Path
import sys,json,time,random
from collections import Counter
# Load definitions without executing the earlier search loop.
namespace={'__file__':str(Path(__file__).with_name('rotation_search.py')),'__name__':'rotation_library'}
exec(Path(namespace['__file__']).read_text().split('qmap,moves=analysis(a.T,a.nodes)')[0],namespace)
a=namespace['a'];analysis=namespace['analysis'];apply=namespace['apply'];OUT=Path(__file__).resolve().parent
rng=random.Random(246245);began=time.monotonic();limit=240
T,N=a.T,a.nodes;history=[];seen=set();stats=Counter();journal=[]
while time.monotonic()-began<limit:
 try:mp,moves=analysis(T,N)
 except Exception:T,N=a.T,a.nodes;history=[];stats['mapping_reset']+=1;continue
 rng.shuffle(moves)
 progressed=False
 for m in moves:
  stats['move_considered']+=1
  try:tt,nn=apply(T,N,mp,m)
  except Exception:continue
  key=tuple(sorted(tt.items()))
  if key in seen:continue
  seen.add(key);stats['distinct_tables']+=1
  count=len(tt)//2
  if count>246:continue
  # Check the complete source equivalence only on candidate reductions.
  if count<246:
   stats['sub246']+=1
   try:
    cert,bisim=a.h.bisimulation(a.nodes,nn)
    affine=a.check(tt,nn)
   except Exception as ex:affine={'status':'ERROR','error':str(ex)}
   e={'moves':history+[m],'states':count,'affine':affine}
   journal.append(e);print('SMALL',stats['sub246'],'depth',len(history)+1,affine,flush=True)
   if affine['status']=='PASS':
    p=OUT/'rotation_walk_winner';p.mkdir(exist_ok=True)
    (p/'machine.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(tt.items())))
    (p/'source.json').write_text(json.dumps(nn)+'\n');(p/'bisimulation.json').write_text(json.dumps(cert)+'\n');(p/'result.json').write_text(json.dumps(e,indent=2)+'\n')
    stats['winner']+=1;break
   continue
  # A deterministic spread of exact symbolic sites is a discovery-only screen.
  sites=a.enumerate_sites(nn)
  if max(max(map(len,p.split('1'))) for p,op,r in sites)>7:stats['zero_run_reject']+=1;continue
  old_enum=a.enumerate_sites
  sample=sorted(set(range(0,len(sites),73))|{894,1024,2048,4096,6459})
  a.enumerate_sites=lambda ignored:[sites[j] for j in sample if j<len(sites)]
  try:screen=a.check(tt,nn)
  except Exception:screen={'status':'FAIL'}
  finally:a.enumerate_sites=old_enum
  if screen['status']!='PASS':stats['fixture_reject']+=1;continue
  T,N=tt,nn;history=history+[m];progressed=True;stats['accepted_walk_step']+=1
  if stats['accepted_walk_step']%10==0:print('PROGRESS',dict(stats),'depth',len(history),flush=True)
  break
 if stats['winner']:break
 if not progressed or len(history)>=24 or rng.random()<.10:
  T,N=a.T,a.nodes;history=[];stats['walk_reset']+=1
print('DONE',dict(stats),time.monotonic()-began,flush=True)
(OUT/'rotation_walk_result.json').write_text(json.dumps({'seed':246245,'budget_seconds':limit,'elapsed_seconds':time.monotonic()-began,'statistics':dict(stats),'journal':journal},indent=2)+'\n')
