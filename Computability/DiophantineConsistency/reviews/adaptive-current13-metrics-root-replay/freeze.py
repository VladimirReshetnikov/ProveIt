from pathlib import Path
import json,hashlib,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';B=D/'reviews/adaptive-current13-metrics-root-replay'
p=Path(Path('/tmp/adaptive-current13-metrics-root-latest').read_text().strip())
s=json.loads((p/'state.json').read_text())
if s['status']!='PASS' or B.exists():raise RuntimeError('PASS and fresh evidence required')
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
for r in json.loads((p/'observations.json').read_text()):
 if rec(r['path'])['sha256']!=r['sha256']:raise RuntimeError('freeze hash '+r['path'])
B.mkdir()
for q in p.iterdir():
 if q.is_file():shutil.copyfile(q,B/q.name)
for name in ['adaptive-current13-metrics-root-console.log','adaptive-current13-metrics-root-preflight1.py','adaptive-current13-metrics-root-preflight1.log']:
 shutil.copyfile(Path('/tmp')/name,B/name)
shutil.copyfile(__file__,B/'freeze.py')
m=[dict(rec(q),path=str(q.relative_to(R))) for q in sorted(B.iterdir())];(B/'FILES.json').write_text(json.dumps(m,indent=2)+'\n')
packet=dict(status='PASS',scope='Independent ROOT full metric-proof/auditor review, supplemental complete leader/current-data checks and normal/optimized replays; zero Lean builds',state=rec(B/'state.json'),manifest=rec(B/'FILES.json'),preflight_failures=1,completed_audits=2,observations=s['observations'],distinct_paths=s['distinct_paths'],records=s['records'],independent_checks=s['independent_checks'])
pth=D/'reviews/adaptive-current13-metrics-root-replay.json';pth.write_text(json.dumps(packet,indent=2)+'\n')
print(json.dumps(dict(packet=rec(pth),manifest=rec(B/'FILES.json'),files=len(m),observations=s['observations'],distinct=s['distinct_paths'],seconds=[x['seconds'] for x in s['records']]),indent=2))
