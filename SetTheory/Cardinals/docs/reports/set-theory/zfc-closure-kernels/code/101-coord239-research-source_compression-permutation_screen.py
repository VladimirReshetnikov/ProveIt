from pathlib import Path
import independent_runtime as r
import symbolic_runtime as s
import json,itertools,time,collections,random
T=r.table('baseline240.tm');S=json.loads(Path('sites_logical.json').read_text())
CORE={2,4,6,7,9,10,13,14,19,20,28,29,31,38,40,41,42,44,48,56,58,60,63,64,69,73,75,83,84,95,96,109,112,131,255}
SKIP=(60,44,31,56,38,40,28,64,69);PHY=(6,2,0,4,3,7,8,5,1)
L,_=s.prove_blocks(T)
byop=collections.defaultdict(list)
for st in S:byop[tuple(st[1:])].append(st)
rnd=random.Random(818172);sample=[]
for op,ss in byop.items():
 selected=ss if len(ss)<=12 else [ss[0],ss[-1],*rnd.sample(ss[1:-1],10)]
 sample.extend(selected)
sample.sort(key=lambda x:(x[1]=='CH',len(x[0])))
results=[];t0=time.monotonic()
for a,b in itertools.combinations(range(9),2):
 perm=list(range(9));perm[a],perm[b]=b,a
 mapping={SKIP[i]:SKIP[j]for i,j in enumerate(perm)}
 U={k:(w,d,mapping.get(t,t)if k[0]not in CORE else t)for k,(w,d,t)in T.items()}
 r.PHY=tuple(perm[i]for i in PHY)
 checked=0;failure=None
 for st in sample:
  for pos in ([False,True]if st[1]=='CD'else[False]):
   try:s.case(U,L,st,pos);checked+=1
   except Exception as e:failure=[st,pos,str(e)];break
  if failure:break
 rec=dict(swap=[a,b],physical=list(r.PHY),sample_passed=checked,failure=failure)
 if not failure:
  path=f'perm_{a}_{b}.tm';Path(path).write_text('#! start 95\n'+''.join(f'{q} {c} {w} {"R"if d==1 else"L"} {t}\n'for(q,c),(w,d,t)in sorted(U.items())))
  rec['table']=path
 results.append(rec);print(a,b,checked,'FAIL'if failure else'PASS',round(time.monotonic()-t0,2),flush=True)
Path('permutation_screen.json').write_text(json.dumps(dict(sample_leaves=len(sample),results=results),indent=2)+'\n')
