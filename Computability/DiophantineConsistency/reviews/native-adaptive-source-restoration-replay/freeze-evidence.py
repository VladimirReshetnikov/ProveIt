from pathlib import Path
import json,hashlib,shutil
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');D=ROOT/'Computability/DiophantineConsistency'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):p=Path(p);return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def save(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
paths=[Path(s) for s in Path('/tmp/native-adaptive-source-restoration-attempts').read_text().splitlines()]
assert len(paths)==5 and len(set(paths))==5
final=paths[-1];state=json.loads((final/'state.json').read_text());inputs=json.loads((final/'inputs.json').read_text());assert state['status']=='PASS'
for p in inputs['pins']:assert sha(p['path'])==p['sha256']
for r in state['completed']:
 assert r['exit_code']==0
 for k in ['source','snapshot','log','timing','object']:assert sha(r[k]['path'])==r[k]['sha256']
bundle=D/'reviews/native-adaptive-source-restoration-replay';assert not bundle.exists();bundle.mkdir()
for src,name in [(Path('/tmp/native-adaptive-source-restoration-driver.py'),'driver.py'),(Path(__file__),'freeze-evidence.py'),(D/'research/adaptive-source-restoration2011-proposal.md','proposal.md'),(D/'research/adaptive-source-restoration2011-cache-audit.json','cache-audit.json')]:shutil.copy2(src,bundle/name)
for i,path in enumerate(paths,1):
 dest=bundle/('attempt-'+str(i));dest.mkdir()
 for name in ['inputs.json','state.json']:shutil.copy2(path/name,dest/name)
 shutil.copytree(path/'logs',dest/'logs')
files=[rec(p) for p in sorted(bundle.rglob('*')) if p.is_file()]
for f in files:f['relative_path']=str(Path(f['path']).relative_to(bundle))
manifest=D/'reviews/native-adaptive-source-restoration-replay-files.json';assert not manifest.exists();save(manifest,files)
packet={'format':'adaptive-source-restoration-private-replay-v1','status':'PASS','scope':'Original positive A0=0,A1=0,Fs=1,Fa=1 under PortBox and beta=2^d-1,d>=4 produce 31 positive natural old-source coordinates, all22 literal SplitCertificate59.sourceRows zero, original J/F/alpha/f/i/eta/zeta/X/V/y and same nativeRank preserved. Quotient signs and main index/power facts are derived; no restored source premise. No complete graph binding, canonical converse, current polynomial endpoint or internal HA claim.',
 'private':str(final),'driver':rec('/tmp/native-adaptive-source-restoration-driver.py'),'inputs_record':rec(final/'inputs.json'),'state_record':rec(final/'state.json'),'inputs':inputs,'completed':state['completed'],
 'attempts':[{'private':str(p),'state':rec(p/'state.json'),'status':json.loads((p/'state.json').read_text())['status']} for p in paths],
 'artifact_texts':files,'manifest':rec(manifest),'final_free_bytes':shutil.disk_usage('/tmp').free,
 'corrections':'Four failed main attempts preserved: (1) unspaced <i syntax, a linear_combination sign, default-heartbeat vector-row simplification; (2) insufficient match reduction for positivity, malformed nested proof tactic sequencing, inferred R=eta, incomplete repeated natural cast rewriting; (3) diagnostic trace confirms only match positivity failures remained; (4) explicit positivity branches reintroduced two <i tokens. Final uses explicit index match/row changes and positivity cases, fixed parameter R and casts, no cap increase. Fifth main and first Checks pass, no warnings.',
 'provider_note':'33 authenticated reused custom source/object pairs with independently root-accepted Mersenne provider;22 explicit external names/66 companions;187 execution pins. No dependency or Foundation build.'}
p=D/'reviews/native-adaptive-source-restoration-replay.json';assert not p.exists();save(p,packet)
print(json.dumps({'packet':rec(p),'manifest':rec(manifest),'files':len(files)},indent=2))
