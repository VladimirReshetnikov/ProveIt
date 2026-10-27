from pathlib import Path
import hashlib, json, os, re, shutil

ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
REV=DC/'reviews'
BUNDLE=REV/'arithmetic-carrier-soundness2011-author-replay'
PACKET=REV/'arithmetic-carrier-soundness2011-replay.json'
observed={}; comparisons=0; snapshot_bindings=[]; attempt_objects=[]


def require(ok,message):
    if not ok: raise RuntimeError(message)


def record(path):
    p=Path(path); data=p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))


def save(path,value):
    Path(path).write_text(json.dumps(value,indent=2)+'\n')


def check(expected,actual=None):
    global comparisons
    found=record(actual or expected['path'])
    require(found['sha256']==expected['sha256'],'hash '+expected['path'])
    require('bytes' not in expected or found['bytes']==expected['bytes'],'size '+expected['path'])
    observed[(found['path'],found['sha256'])]=found; comparisons+=1
    return found


def preserve(source,dest):
    source=Path(source); dest=Path(dest)
    require(source.is_file() and not source.is_symlink(),'regular immutable input '+str(source))
    dest.parent.mkdir(parents=True,exist_ok=True)
    require(not dest.exists() and not dest.is_symlink(),'new durable destination')
    os.link(source,dest)
    check(record(source),dest)


paths=[Path(p) for p in Path('/tmp/arithmetic-carrier-soundness2011-author-runs.txt').read_text().splitlines()]
require(len(paths)==10,'exact ten attempts')
states=[json.loads((p/'state.json').read_text()) for p in paths]
require(all(s['status']=='FAILED' for s in states[:-1]) and states[-1]['status']=='PASS','chronology')
require(shutil.disk_usage('/tmp').free>=512*1024**2+16*1024**2,'freeze reserve')
require(not BUNDLE.exists() and not PACKET.exists(),'new frozen evidence')
BUNDLE.mkdir()
for index,(private,state) in enumerate(zip(paths,states),1):
    inputs=json.loads((private/'inputs.json').read_text())
    auth=json.loads((private/'authentication.json').read_text())
    providers=json.loads((private/'providers.json').read_text())
    replacements={s['path']:private/'logs'/Path(s['path']).name for s in inputs['sources']}
    for source in inputs['sources']:
        actual=check(source,replacements[source['path']])
        snapshot_bindings.append(dict(attempt=index,original=source,snapshot=actual))
    for pin in auth['pins']: check(pin,replacements.get(pin['path']))
    require(len(providers)==570,'complete first providers')
    for provider in providers: check(provider['expected']); check(provider['actual'])
    check(state['inputs']); check(state['driver'],private/'driver.py')
    check(inputs['plan']); check(inputs['proposal']); check(inputs['compiler'])
    for row in state['records']:
        for key in ['snapshot','log','timing']: check(row[key])
        if 'object' in row: check(row['object'])
    for source in inputs['sources']:
        output=private/'lib'/'DiophantineConsistency'/(Path(source['path']).stem+'.olean')
        if output.exists():
            require(output.is_file() and not output.is_symlink(),'regular attempt output')
            attempt_objects.append(dict(attempt=index,object=check(record(output))))
    for name in ['state.json','inputs.json','authentication.json','providers.json','driver.py']:
        preserve(private/name,BUNDLE/f'attempt-{index}'/name)
    for source in sorted((private/'logs').iterdir()):
        preserve(source,BUNDLE/f'attempt-{index}'/source.name)

final=states[-1]; private=paths[-1]
inputs=json.loads((private/'inputs.json').read_text())
require(inputs['counts']==dict(custom=135,Foundation=95,artifacts=420,external=50,
    boundary_artifacts=150,boundary_primaries=50,boundary_companions=100,
    actual_first_providers=570,fresh_prerequisites=0),'approved profile')
require(len(final['records'])==2 and len(final['records'][1]['axiom_reports'])==5,'five reports')
for row in final['records']:
    check(row['source']); check(row['object']); require(row['exit_code']==0,'zero exit')
    log=Path(row['log']['path']).read_text()
    require(not re.search(r'\b(?:warning|error|sorryAx)\b',log),'clean diagnostics')
    row['peak_rss_kib']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',
        Path(row['timing']['path']).read_text()).group(1))
for theorem,axioms in final['records'][1]['axiom_reports']:
    require(set(x.strip() for x in axioms.split(','))<={'propext','Classical.choice','Quot.sound'},'axioms '+theorem)
for key,name in [('plan','plan.json'),('proposal','proposal.md')]:
    preserve(inputs[key]['path'],BUNDLE/name)
for name in ['arithmetic-carrier-soundness2011-plan-root.md','arithmetic-carrier-soundness2011-plan-root.json']:
    preserve(REV/name,BUNDLE/name)
preserve(Path(__file__),BUNDLE/'freeze.py')
save(BUNDLE/'freeze-authentication.json',dict(comparisons=comparisons,
    unique_paths=len({p for p,h in observed}),unique_observations=len(observed),
    observed=list(observed.values()),historical_source_bindings=snapshot_bindings,
    method='Every attempt authentication pin and all expected/actual first-provider pairs rehashed; historical source observations rebound only to their preserved attempt snapshots. Repeated identical path/hash records stored once; comparison count retains every check.'))
manifest=[record(p) for p in sorted(BUNDLE.rglob('*')) if p.is_file()]
for item in manifest:item['path']=str(Path(item['path']).relative_to(ROOT))
save(BUNDLE/'FILES.json',manifest)
require(shutil.disk_usage('/tmp').free>=512*1024**2,'final reserve')
packet=dict(status='PASS',author='complemented47_review',
    scope='In every internal IΣ1 arithmetic model, actual positive Fin14 splitNatural zero of ObjectCurrentEquation2011.expression implies all five maintained additive equations. Literal syntax binds via signed natural pairs; actual four negative-unit exclusions and positive discriminant extract all five units, transport first. Scalar_window derives q>F and positive tau before natural rank subtraction. Actual current beta/low/high bounds are proved, fourth source port is highPort+beta once. naturalExpression applies exactly one positive shift. No supplied product/transport/norm/index/source/port-bound oracle at current endpoints. No power/radix, word/carry/tableau, converse/cofinal or HA equivalence endpoint.',
    counts=inputs['counts'],records=final['records'],private_provider=str(private/'lib'),
    attempts=[dict(attempt=i,private=str(p),status=s['status'],state=record(p/'state.json'),
        durable=record(BUNDLE/f'attempt-{i}'/'state.json')) for i,(p,s) in enumerate(zip(paths,states),1)],
    attempt_objects=attempt_objects,failed_attempts=9,final_state=record(private/'state.json'),
    inputs=record(private/'inputs.json'),providers=record(private/'providers.json'),
    authentication=record(private/'authentication.json'),plan=inputs['plan'],proposal=inputs['proposal'],
    root_approval=record(REV/'arithmetic-carrier-soundness2011-plan-root.md'),
    root_audit=record(REV/'arithmetic-carrier-soundness2011-plan-root.json'),
    driver=final['driver'],freeze_driver=record(__file__),compiler=inputs['compiler'],LEAN_PATH=inputs['LEAN_PATH'],
    manifest=record(BUNDLE/'FILES.json'),freeze_authentication=record(BUNDLE/'freeze-authentication.json'),
    freeze_comparisons=comparisons,freeze_paths=len({p for p,h in observed}),
    final_free_bytes=final['final_free_bytes'],freeze_free_bytes=shutil.disk_usage('/tmp').free,
    evidence_storage='Regular hardlinks preserve immutable terminal-attempt evidence and frozen plans/root approvals; unique freeze observations avoid repeated inventory copies. No source/proof object/shared cache rewritten. Outer packet and author receipt are outside FILES to avoid cyclic hashes.',
    history='Ten complete capped attempts, both input snapshots before each pair, unchanged 168-line executed driver. Attempt1 had constructor/cast/normalization errors and kernel memory failure; attempts2-5 aborted at the 6GB interpreter cap. Attempts3-7 added ordinary diagnostic commands, all removed from final sources; their snapshots/logs and saved progress files are retained. Attempt6 exposed Expr constructor/numeral and diagnostic liftIO errors; attempt7 exposed further representation normalization and concrete-endpoint kernel expansion. Generic scalar identities and opaque vector binding resolved these without cap/import/statement changes. Attempt8 left only a Nat exponent rewrite selecting the wrong occurrence and threshold warning. Attempt9 compiled main but strict diagnostics rejected the threshold warning. Attempt10 uses the generic two_power_bound, passes both leaves cleanly, and emits five standard-only reports. No prerequisite build, imported-file edit, heartbeat/cap increase or reserve rejection. All final proof, Checks and driver bytes were fully read before execution.')
save(PACKET,packet)
print(json.dumps(dict(packet=record(PACKET),manifest=record(BUNDLE/'FILES.json'),files=len(manifest),
    freeze_driver=record(__file__),comparisons=comparisons,paths=len({p for p,h in observed}),
    records=final['records'],free_bytes=shutil.disk_usage('/tmp').free),indent=2))
