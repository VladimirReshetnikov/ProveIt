from pathlib import Path
import json,hashlib,shutil
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');D=ROOT/'Computability/DiophantineConsistency'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):p=Path(p);return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def save(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
paths=[Path(s) for s in Path('/tmp/native-adaptive-mersenne-attempts').read_text().splitlines()]
assert len(paths)==2 and len(set(paths))==2
final=paths[-1];state=json.loads((final/'state.json').read_text());inputs=json.loads((final/'inputs.json').read_text());assert state['status']=='PASS'
for p in inputs['pins']:assert sha(p['path'])==p['sha256']
for r in state['completed']:
 assert r['exit_code']==0
 for k in ['source','snapshot','log','timing','object']:assert sha(r[k]['path'])==r[k]['sha256']
bundle=D/'reviews/native-adaptive-mersenne-replay';assert not bundle.exists();bundle.mkdir()
for src,name in [(Path('/tmp/native-adaptive-mersenne-driver.py'),'driver.py'),(Path(__file__),'freeze-evidence.py'),(D/'research/adaptive-mersenne2011-proposal.md','proposal.md'),(D/'research/adaptive-mersenne2011-cache-audit.json','cache-audit.json')]:shutil.copy2(src,bundle/name)
for i,path in enumerate(paths,1):
 dest=bundle/('attempt-'+str(i));dest.mkdir()
 for name in ['inputs.json','state.json']:shutil.copy2(path/name,dest/name)
 shutil.copytree(path/'logs',dest/'logs')
files=[rec(p) for p in sorted(bundle.rglob('*')) if p.is_file()]
for f in files:f['relative_path']=str(Path(f['path']).relative_to(bundle))
manifest=D/'reviews/native-adaptive-mersenne-replay-files.json';assert not manifest.exists();save(manifest,files)
packet={'format':'adaptive-mersenne-private-replay-v1','status':'PASS','scope':'From original positive adaptive cuts and current Mersenne width: X=2^R, 3 does not divide q, q divides X, q=(2^94517)^N with N>0 and94517*N<=R.toNat. Generic factor-three exclusion/prime-power and width lemmas. No restored source, supplied power, canonical converse or graph/HA endpoint.',
 'private':str(final),'driver':rec('/tmp/native-adaptive-mersenne-driver.py'),'inputs_record':rec(final/'inputs.json'),'state_record':rec(final/'state.json'),'inputs':inputs,'completed':state['completed'],
 'attempts':[{'private':str(p),'state':rec(p/'state.json'),'status':json.loads((p/'state.json').read_text())['status']} for p in paths],
 'artifact_texts':files,'manifest':rec(manifest),'final_free_bytes':shutil.disk_usage('/tmp').free,
 'corrections':'First main rejected generic divisibility convert instance side goals, wrong sign in Bezout linear_combination, and unspaced <i parser; unused width binder warning. Changed to explicit divisibility witnesses, corrected equality combination and spacing; renamed unused binder. All public statements unchanged. Second main/check pass; no failed checks invocation.',
 'provider_note':'32 authenticated reused custom modules, including independently root-accepted PowerProjection and PowerRecovery;22 unchanged external names/66 companions. No dependency or Foundation build.'}
p=D/'reviews/native-adaptive-mersenne-replay.json';assert not p.exists();save(p,packet)
print(json.dumps({'packet':rec(p),'manifest':rec(manifest),'files':len(files)},indent=2))
