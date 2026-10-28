from pathlib import Path
import hashlib,json,os,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
B=D/'reviews/arithmetic-radix-alignment-peer-replay';P=D/'reviews/arithmetic-radix-alignment-peer-replay.json'
pins={};comparisons=0

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global comparisons
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);need('bytes'not in x or a['bytes']==x['bytes'],'size')
 pins[a['path']]=a;comparisons+=1;return a
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def preserve(src,dst):
 need(Path(src).is_file()and not Path(src).is_symlink(),'regular source');need(not dst.exists(),'new destination')
 os.link(src,dst);need(rec(src)['sha256']==rec(dst)['sha256'],'copy');check(rec(dst))

paths=Path('/tmp/arithmetic-radix-alignment-peer-runs.txt').read_text().splitlines();need(len(paths)==1,'one independent attempt')
private=Path(paths[0]);state=json.loads((private/'state.json').read_text());need(state['status']=='PASS','terminal PASS')
need(not B.exists()and not P.exists(),'new evidence');need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
check(state['driver']);check(state['inputs']);inputs=json.loads((private/'inputs.json').read_text())
for pin in inputs['pins']:check(pin)
for key in ['author_packet','author_manifest','author_receipt','plan','compiler','providers']:check(inputs[key])
providers=json.loads(Path(inputs['providers']['path']).read_text());need(len(providers)==474,'providers')
for pair in providers:check(pair['expected']);check(pair['actual'])
author=json.loads(Path(inputs['author_packet']['path']).read_text());records=state['records']
need(len(records)==2 and len(records[1]['axiom_reports'])==8,'eight reports')
for row,old in zip(records,author['final']['records']):
 need(row['exit_code']==0 and row['matches_author'],'clean match')
 for key in ['source','snapshot','object','log','timing']:check(row[key])
 need(row['object']['sha256']==old['object']['sha256']and row['log']['sha256']==old['log']['sha256'],'author byte equality')
 need(row['axiom_reports']==old['axiom_reports'],'author reports')
 row['peak_rss_kib']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',Path(row['timing']['path']).read_text()).group(1))
B.mkdir()
for p in [private/'state.json',private/'inputs.json',private/'providers.json',private/'driver.py',*sorted((private/'logs').iterdir())]:preserve(p,B/p.name)
for row in records:preserve(row['object']['path'],B/Path(row['object']['path']).name)
preserve(__file__,B/'freeze.py')
save(B/'freeze-authentication.json',dict(comparisons=comparisons,unique_paths=len(pins),pins=list(pins.values())))
manifest=[rec(p)for p in sorted(B.iterdir())if p.is_file()]
for x in manifest:x['path']=str(Path(x['path']).relative_to(R))
save(B/'FILES.json',manifest);need(shutil.disk_usage('/tmp').free>=512*1024**2,'final reserve')
packet=dict(status='PASS',reviewer='complemented47_review',author='controller_certificate',
 scope='Independent full final source/Checks/author-driver/plan review, exact source/header DAG and complete provenance/provider authentication, then only two fresh private leaves. Generic all-internal IΣ1 factor/exponent alignment; no concrete current-polynomial or HA equivalence claim.',
 counts=inputs['counts'],private_provider=str(private/'lib'),state=rec(private/'state.json'),records=records,
 inputs=rec(private/'inputs.json'),providers=rec(private/'providers.json'),driver=state['driver'],freeze_driver=rec(__file__),
 author_packet=inputs['author_packet'],author_receipt=inputs['author_receipt'],author_manifest=inputs['author_manifest'],plan=inputs['plan'],
 compiler=inputs['compiler'],LEAN_PATH=inputs['LEAN_PATH'],manifest=rec(B/'FILES.json'),freeze_authentication=rec(B/'freeze-authentication.json'),
 independent_attempts=1,compiler_invocations=2,failures=0,observations=state['comparisons'],observed_paths=state['unique_paths'],
 freeze_comparisons=comparisons,freeze_paths=len(pins),free_bytes=shutil.disk_usage('/tmp').free,
 storage='Regular hardlinks to immutable terminal metadata, source snapshots, logs/timings/drivers and regular proof outputs; all original paths retained. Outer packet/receipt outside manifest to avoid cyclic hashes.',
 roles='Reviewer earlier challenged the draft source only. Reviewer authored no new Radix theorem and none of the 90 Foundation prerequisites; prior Pell/current-source authorship is outside this selected mathematical DAG. Author first failed attempt and final source-only qualification repair are authenticated and retained; no source changes or dependency rebuild.')
save(P,packet)
print(json.dumps(dict(packet=rec(P),manifest=rec(B/'FILES.json'),files=len(manifest),freeze_driver=rec(__file__),records=records,comparisons=comparisons,paths=len(pins)),indent=2))
