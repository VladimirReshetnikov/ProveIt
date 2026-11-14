from pathlib import Path
import sys,json,itertools,subprocess,random,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'reference/pa194/construction'))
from build194 import read_table,table_text
rows=read_table(HERE.parents[1]/'construction/output/pa194C.native.tm')
sk=[51,36,25,48,32,33,22,55,60]
old=[6,2,0,4,3,7,8,5,1]
routers={key:old.index(sk.index(act[2])) for key,act in rows.items() if key[1]==1 and act[0]==0 and act[1] and act[2] in sk}
print('ROUTERS',routers,flush=True)
out=HERE/'permutations';out.mkdir(exist_ok=True)
rng=random.Random(2026111412345);done=set();start=time.monotonic()
candidates=[tuple(p) for p in itertools.permutations(range(3))]
# Try all isolated transpositions before random permutations.
perms=[tuple(old)]
for a,b in itertools.combinations(range(9),2):
 p=old.copy();p[a],p[b]=p[b],p[a];perms.append(tuple(p))
for i in range(10000):
 if i<len(perms):p=perms[i]
 else:p=tuple(rng.sample(range(9),9))
 if p in done:continue
 done.add(p)
 r=rows.copy()
 for key,logical in routers.items():
  w,d,_=r[key];r[key]=(w,d,sk[p[logical]])
 (out/'input.tm').write_text(table_text(r))
 result=subprocess.run([str(HERE/'action_merge_boxes'),str(out/'input.tm'),'4','100'],stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,text=True,check=True)
 if result.stdout.strip():
  print('HIT',i,p,result.stdout.strip(),flush=True)
  (out/f'hit{i}.tm').write_text(table_text(r));(out/f'hit{i}.json').write_text(json.dumps({'physical_map':p,'merges':[json.loads(s) for s in result.stdout.splitlines()]},indent=2))
 if (i+1)%100==0:print('ITER',i+1,'SEC',time.monotonic()-start,flush=True)
