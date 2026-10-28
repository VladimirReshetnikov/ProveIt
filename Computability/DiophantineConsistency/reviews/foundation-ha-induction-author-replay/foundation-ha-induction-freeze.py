from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path('/home/codex/.codex/worktrees/46be/Proofs')
d=root/'Computability/DiophantineConsistency'
p=Path('/tmp/foundation-ha-induction-wjk4g3e1')
def sha(f):return hashlib.sha256(Path(f).read_bytes()).hexdigest()
def check(f,h):
 if sha(f)!=h:raise RuntimeError('Pin drift: '+str(f))
r=json.loads((p/'prerequisites.json').read_text())
for m in r['foundation']:
 check(m['source'],m['source_sha256']);check(m['trace'],m['trace_sha256'])
 for o in m['objects']:check(o['path'],o['sha256'])
for m in r['nonfoundation']:
 check(root/m['source'],m['source_sha256']);check(m['object'],m['object_sha256'])
for m in r['prior_manifests']:check(root/m['path'],m['sha256'])
for k,v in r['package_identity'].items():check(root/k,v['current_sha256'])
check(r['compiler']['path'],r['compiler']['sha256'])
check('/tmp/foundation-ha-induction-prepare.py',r['prepare_driver_sha256'])
if (p/'main-stage6.log').read_bytes():raise RuntimeError('Main diagnostic')
log=(p/'checks-stage2.log').read_text()
reports=re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.S)
if len(reports)!=30:raise RuntimeError('Wrong audit count')
for name,_,axs in reports:
 if not set(x.strip() for x in axs.split(',') if x.strip())<= {'propext','Quot.sound','Classical.choice'}:raise RuntimeError('Unexpected axiom '+name)
if re.search(r'error:|warning:|sorryAx',log):raise RuntimeError('Check diagnostic')
fresh=[]
for suffix,stage in [('', 'main-stage6'),('Checks','checks-stage2')]:
 mod='DiophantineConsistency.FoundationHAInduction'+suffix
 src=d/'Lean/DiophantineConsistency'/('FoundationHAInduction'+suffix+'.lean')
 if src.read_bytes()!=(p/(stage+'.lean')).read_bytes():raise RuntimeError('Final source mismatch')
 obj=p/Path(*mod.split('.')).with_suffix('.olean')
 fresh.append(dict(module=mod,source=str(src.relative_to(root)),source_sha256=sha(src),source_lines=len(src.read_text().splitlines()),object=str(obj),object_sha256=sha(obj),log=str(p/(stage+'.log')),log_sha256=sha(p/(stage+'.log')),exit_code=0,command=f'lake env bash -c \'export LEAN_PATH="{p}:$LEAN_PATH"; lean -M6000 -j1 {src.relative_to(root)} -o {obj}\''))
bundle=d/'reviews/foundation-ha-induction-author-replay';bundle.mkdir(exist_ok=True)
files=list(p.glob('*-stage*.lean'))+list(p.glob('*-stage*.log'))+[p/'prerequisites.json',Path('/tmp/foundation-ha-induction-prepare.py'),Path(__file__)]
for f in files:shutil.copy2(f,bundle/f.name)
r.update(snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),fresh_modules=fresh,axiom_reports=[dict(theorem=n,axioms=[x.strip() for x in a.split(',') if x.strip()]) for n,_,a in reports],freeze_driver_sha256=sha(__file__),replay_files=[dict(path=str((bundle/f.name).relative_to(root)),sha256=sha(bundle/f.name)) for f in sorted(files)],fresh_scope='Only FoundationHAInduction and Checks freshly compiled; 85 Foundation and 18 custom prerequisites reused with exact current source/object pins. Stage6 main and stage2 checks accepted; all earlier stages rejected development attempts.',source_snapshot_after_build='All selected source, trace, object, compiler, package and parent-manifest pins rechecked at freeze.')
out=d/'reviews/foundation-ha-induction-dependency-replay.json';out.write_text(json.dumps(r,indent=2)+'\n')
for m in fresh:print(m['module'],m['source_lines'],m['source_sha256'],m['object_sha256'])
print('manifest',sha(out));print('snapshot',r['snapshot']);print('audits',len(reports))
