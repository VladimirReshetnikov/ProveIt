from pathlib import Path
import json,hashlib,subprocess,time
P=Path('/tmp/current-hierarchy2011-author-betz9tp8');R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';supp=json.loads((D/'research/arithmetic-current-hierarchy2011-current-supplement.json').read_text());s=json.loads((P/'AUTHOR.json').read_text());a=s['attempts'][-1]
assert s['status']=='FAILED' and a['failure']=='final HEAD' and len(s['records'])==94 and all(x['status']=='PASS' for x in s['records'])
n=0
def check(x):
 global n
 b=Path(x['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==x['sha256'],x['path'];assert 'bytes' not in x or len(b)==x['bytes'];n+=1
for x in supp['comparisons']:check(x)
for key in ['historical_snapshot','complete_diff','script']:check(supp[key])
inputs=json.loads(Path(a['inputs']['path']).read_text());check(a['inputs']);check(a['driver'])
assert len(inputs['sources'])==94 and len(inputs['providers'])==983
for x in inputs['sources']:
 check(x);check(x['snapshot']);assert x['sha256']==x['snapshot']['sha256']
for r in s['records']:
 assert r['exit_code']==0
 for k in ['source','snapshot','log','timing']:check(r[k])
 for o in r['objects']:check(o)
for x in inputs['providers']:check(x['actual']);check(x['expected'])
result={'status':'PASS','qualification':'All 94 commands passed; original author status FAILED exclusively on final HEAD identity after all its own hash checks passed. This independent byte-level postcheck does not rewrite that state.','original_head':supp['snapshot_head'],'current_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'comparisons':n,'records':len(s['records']),'provider':str(P/'lib'),'source_snapshots':94,'cached_providers':983,'target_records':s['records'][-2:]}
q=P/'postcheck.json';q.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2),flush=True)
