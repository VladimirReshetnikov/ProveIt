from pathlib import Path
import json,itertools,random,subprocess,time
HERE=Path(__file__).resolve().parent
P=HERE/'generated'/'scanner_permutations';P.mkdir(parents=True,exist_ok=True)
SK=[51,36,25,48,32,33,22,55,60]
refs={'CSZ':(HERE/'pa194CSZ.native.tm'),'C_I_Z':(HERE/'inputs/C_I_Z.native.tm')}
def read(p):
 r={}
 for l in p.read_text().splitlines():
  q,b,w,d,n=l.split();r[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
 return r
def text(r):return ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n'for(q,b),(w,d,n)in sorted(r.items()))
bases={k:read(p)for k,p in refs.items()}
perms=[]
for i,j in itertools.combinations(range(9),2):
 p=list(range(9));p[i],p[j]=p[j],p[i];perms.append(p)
rng=random.Random(423017194);seen={tuple(p)for p in perms}
for _ in range(5000):
 p=list(range(9));rng.shuffle(p)
 if tuple(p) not in seen:seen.add(tuple(p));perms.append(p)
start=time.monotonic();checked=[];found=[]
for perm in perms:
 for name,base in bases.items():
  if time.monotonic()-start>90:break
  order=[SK[i]for i in perm];rows=dict(base)
  for i,q in enumerate(order):rows[q,0]=(0,1,order[i-1]if i else 16)
  (P/'working.tm').write_text(text(rows))
  run=subprocess.run([str(HERE/'action_merge_all'),str(P/'working.tm'),'5','300'],capture_output=True,text=True);assert run.returncode==0
  folds=[json.loads(s)for s in run.stdout.splitlines()]
  checked.append({'base':name,'order':order,'local_merges':folds})
  if folds:
   found.append(checked[-1]);(P/f'found_{len(found)}.tm').write_text(text(rows));print('FOUND',found[-1],flush=True)
  if len(checked)%100==0:print('checked',len(checked),'seconds',time.monotonic()-start,'found',len(found),flush=True)
 else:continue
 break
receipt={'bases':{k:str(p.relative_to(HERE))for k,p in refs.items()},'context_radius':5,'max_local_steps':300,'seed':423017194,'wall_budget_seconds':90,'seconds':time.monotonic()-start,'checked':len(checked),'found':found,
 'scope':'Scanner-chain permutations and conservative all-start-tape local quotient screening. No new permutation is accepted without subsequent source-frame and startup verification.'}
(P/'checked.json').write_text(json.dumps(checked,indent=2));(P/'receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2),flush=True)
