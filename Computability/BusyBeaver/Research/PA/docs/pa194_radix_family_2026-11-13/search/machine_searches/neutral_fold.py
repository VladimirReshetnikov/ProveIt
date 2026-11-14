import json,itertools,subprocess,time,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
OUT=HERE/'generated'/'neutral';OUT.mkdir(parents=True,exist_ok=True)
base={}
for l in (HERE/'pa194CSZ.native.tm').read_text().splitlines():
 q,b,w,d,n=l.split();base[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
def text(rows):return ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n' for(q,b),(w,d,n)in sorted(rows.items()))
checks=0;start=time.monotonic();found=[]
for l in (HERE/'csz_neutral.jsonl').read_text().splitlines():
 x=json.loads(l);q=x['state']
 for act0,act1 in itertools.product(*x['choices']):
  if tuple(act0)==base[q,0] and tuple(act1)==base[q,1]:continue
  rows=dict(base);rows[q,0]=tuple(act0);rows[q,1]=tuple(act1)
  (OUT/'neutral_work.tm').write_text(text(rows))
  r=subprocess.run([str(HERE/'action_merge_all'),str(OUT/'neutral_work.tm'),'5','300'],capture_output=True,text=True)
  assert r.returncode==0,r.stderr
  checks+=1
  if r.stdout.strip():
   record={'neutral_state':q,'neutral_actions':[act0,act1],'folds':[json.loads(z)for z in r.stdout.splitlines()]}
   print('FOUND',record,flush=True);found.append(record)
   (OUT/'neutral_found.json').write_text(json.dumps(found,indent=2))
   (OUT/f'neutral_found_{len(found)}.tm').write_text(text(rows))
  if checks%50==0:print('progress',checks,'seconds',time.monotonic()-start,'found',len(found),flush=True)
print('DONE',checks,'seconds',time.monotonic()-start,'found',len(found),flush=True)
(OUT/'neutral_fold_receipt.json').write_text(json.dumps({'checks':checks,'seconds':time.monotonic()-start,'found':found},indent=2))
