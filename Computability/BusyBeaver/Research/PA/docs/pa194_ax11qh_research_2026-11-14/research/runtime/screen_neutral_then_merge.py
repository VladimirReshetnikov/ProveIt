from pathlib import Path
import json,subprocess,concurrent.futures,time,hashlib
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1]/'candidate/machine/machine.native.tm'
rows={}
for l in BASE.read_text().splitlines():
 q,b,w,d,n=l.split();rows[int(q),int(b)]=int(w),1 if d=='R' else -1,int(n)
edits=[json.loads(l)for l in (HERE/'ax11qh_neutral_candidates.jsonl').read_text().splitlines()]
OUT=HERE/'neutral_then_merge';OUT.mkdir(exist_ok=True)
def task(p):
 i,e=p;rr=dict(rows);rr[e['state'],e['read']]=tuple(e['new'])
 inp=OUT/f'{i:03d}.tm';inp.write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n' for(q,b),(w,d,n)in sorted(rr.items())))
 r=subprocess.run([str(HERE/'joint_return_merge'),str(inp),'4','120',str(HERE/'ax11qh_source_k4.tsv')],capture_output=True,text=True)
 assert r.returncode==0
 hits=[json.loads(x)for x in r.stdout.splitlines()];out={'index':i,'edit':e,'hits':hits,'summary':r.stderr.splitlines()[-1]}
 (OUT/f'{i:03d}.json').write_text(json.dumps(out,indent=2)+'\n')
 if not hits:inp.unlink()
 return out
start=time.time();results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=4)as pool:
 for k,r in enumerate(pool.map(task,enumerate(edits))):
  results.append(r)
  if r['hits']or (k+1)%25==0:print(k+1,'of',len(edits),'hits',len(r['hits']),'elapsed',round(time.time()-start,1),flush=True)
summary={'baseline_sha256':hashlib.sha256(BASE.read_bytes()).hexdigest(),'neutral_proposals':len(edits),'completed_screens':len(results),'hits':sum(len(x['hits'])for x in results),'seconds':time.time()-start,'scope':'Heuristic two-stage screening: original source context envelopes reused after first edit; positives require fresh universal source and whole startup verification; negatives not exhaustive.','results':results}
(HERE/'neutral_then_merge_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('DONE',summary['hits'],flush=True)
