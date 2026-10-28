from pathlib import Path
import hashlib,json,os,re,shutil
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
P=Path('/tmp/arithmetic-signed-pairs-peer-f4gz2l0f')
B=DC/'reviews/arithmetic-signed-pairs-peer-replay'
OUT=DC/'reviews/arithmetic-signed-pairs-peer-replay.json'
observations=[]
def require(ok,msg):
    if not ok: raise RuntimeError(msg)
def record(path):
    p=Path(path);data=p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
def check(pin):
    actual=record(pin['path'])
    require(actual['sha256']==pin['sha256'],'hash '+pin['path'])
    require('bytes' not in pin or actual['bytes']==pin['bytes'],'size '+pin['path'])
    observations.append(actual);return actual
def save(path,value): Path(path).write_text(json.dumps(value,indent=2)+'\n')
def link(source,destination):
    source=Path(source);destination=Path(destination)
    require(source.is_file() and not source.is_symlink(),'regular input '+str(source))
    require(not destination.exists(),'new evidence')
    os.link(source,destination)
    check(dict(record(source),path=str(destination)))
require(shutil.disk_usage('/tmp').free>=512*1024**2+8*1024**2,'initial reserve')
require(not B.exists() and not OUT.exists(),'new packet')
runs=Path('/tmp/arithmetic-signed-pairs-peer-runs.txt').read_text().splitlines()
require(runs==[str(P)],'single peer attempt')
state=json.loads((P/'state.json').read_text());require(state['status']=='PASS','terminal PASS')
check(state['driver']);check(state['inputs'])
inputs=json.loads((P/'inputs.json').read_text())
for pin in inputs['observations']: check(pin)
for key in ['author_packet','plan','scope','author_receipt','author_manifest','providers','compiler']:check(inputs[key])
for pin in inputs['author_states']:check(pin)
providers=json.loads((P/'providers.json').read_text());require(len(providers)==455,'455 providers')
for row in providers:check(row['expected']);check(row['actual'])
require(inputs['counts']==dict(custom=86,Foundation=86,artifacts=344,external=37,
    boundary_artifacts=111,boundary_primaries=37,boundary_companions=74,
    actual_first_providers=455,fresh_prerequisites=0),'exact scope')
author=json.loads(Path(inputs['author_packet']['path']).read_text())
require(len(state['records'])==2,'two leaf commands')
for row,reference in zip(state['records'],author['records']):
    require(row['exit_code']==0 and row['matches_author'],'successful comparison')
    for key in ['source','snapshot','object','log','timing']:check(row[key])
    require(Path(row['object']['path']).is_file() and not Path(row['object']['path']).is_symlink(),'regular output')
    for key in ['source','object','log']:
        require(row[key]['sha256']==reference[key]['sha256'],'byte-identical '+key)
    require(row['axiom_reports']==reference['axiom_reports'],'exact reports')
    require(not re.search(r'\b(?:error|warning|sorryAx)\b',Path(row['log']['path']).read_text()),'clean logs')
    for name,axioms in row['axiom_reports']:
        require(set(re.findall(r'[A-Za-z][A-Za-z.]*',axioms))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
    row['peak_rss_kib']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',Path(row['timing']['path']).read_text()).group(1))
require(len(state['records'][1]['axiom_reports'])==7,'seven reports')
B.mkdir()
for name in ['state.json','inputs.json','providers.json','driver.py','author-packet.json']:
    link(P/name,B/name)
for path in sorted((P/'logs').iterdir()):link(path,B/path.name)
link('/tmp/arithmetic-signed-pairs-peer-attempt-1.log',B/'stdout.log')
link(__file__,B/'freeze.py')
save(B/'freeze-authentication.json',dict(observations=observations,count=len(observations),
    distinct_paths=len({x['path'] for x in observations})))
manifest=[dict(record(path),path=str(path.relative_to(ROOT))) for path in sorted(B.iterdir()) if path.is_file()]
save(B/'FILES.json',manifest)
require(shutil.disk_usage('/tmp').free>=512*1024**2,'final reserve')
packet=dict(status='PASS',reviewer='complemented47_review',findings=[],
    scope='Independent full final181-line main/37-line Checks/proposal, exact internal arithmetic contracts and author/peer drivers reviewed. Fresh only these two leaves; all four sign orientations and zero magnitudes retained; positive scale and four explicit negative-unit exclusions derive all five positive additive units, including transport with no extra premise. No literal evaluator or final PA/HA claim.',
    prior_roles='Reviewer authored NegativeNorms (not imported here) and the reused cache inventory. This source is ROOT-authored; no claim of independence for the inherited Foundation/cache provenance. Complete inherited pins and actual first providers were reauthenticated; no prerequisite rebuilt.',
    author_packet=inputs['author_packet'],author_receipt=inputs['author_receipt'],author_manifest=inputs['author_manifest'],
    plan=inputs['plan'],scope_supplement=inputs['scope'],counts=inputs['counts'],
    inputs=record(P/'inputs.json'),providers=record(P/'providers.json'),state=record(P/'state.json'),
    driver=record(P/'driver.py'),compiler=inputs['compiler'],LEAN_PATH=inputs['LEAN_PATH'],
    private_provider=str(P/'lib'),records=state['records'],attempts=1,failed_attempts=0,
    postflight_comparisons=state['comparison_count'],postflight_paths=state['observation_count'],
    postflight_free_bytes=state['final_free_bytes'],freeze_free_bytes=shutil.disk_usage('/tmp').free,
    freeze_authentication=record(B/'freeze-authentication.json'),manifest=record(B/'FILES.json'),
    evidence_storage='Regular hardlinks of immutable terminal peer evidence; new manifest/authentication/packet writes. Both source snapshots precede the first compiler. All author history is independently pinned and preserved in its original bundle; no source or object mutation.')
save(OUT,packet)
print(json.dumps(dict(packet=record(OUT),manifest=record(B/'FILES.json'),files=len(manifest),
    freeze_comparisons=len(observations),freeze_paths=len({x['path'] for x in observations}),
    records=state['records'],free_bytes=shutil.disk_usage('/tmp').free),indent=2))
