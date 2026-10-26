from pathlib import Path
import json,hashlib,re,subprocess,shutil
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency';p=Path('/tmp/foundation-ha-equality-m09zc399')
def sha(f):return hashlib.sha256(Path(f).read_bytes()).hexdigest()
def check(f,h):
 if sha(f)!=h:raise RuntimeError('Pin drift '+str(f))
r=json.loads((p/'prerequisites.json').read_text())
for m in r['prior_manifests']:check(root/m['path'],m['sha256'])
for k,v in r['package_identity'].items():check(root/k,v['current_sha256'])
check(r['compiler']['path'],r['compiler']['sha256'])
for m in r['foundation']:
 check(m['source'],m['source_sha256']);check(m['trace'],m['trace_sha256'])
 for o in m['objects']:check(o['path'],o['sha256'])
for m in r['nonfoundation']:check(root/m['source'],m['source_sha256']);check(m['object'],m['object_sha256'])
if (p/'main-stage1.log').read_text():raise RuntimeError('Unexpected main diagnostics')
logs=(p/'checks-stage2.log').read_text();audit=[]
for name,body in re.findall(r"'([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)",logs):
 axioms=[] if body.startswith('does not') else [x.strip() for x in body.split('[',1)[1][:-1].split(',')]
 if set(axioms)-{'propext','Quot.sound','Classical.choice'}:raise RuntimeError('Unexpected axioms '+name)
 audit.append(dict(declaration=name,axioms=axioms))
if len(audit)!=31 or 'error' in logs or 'warning' in logs:raise RuntimeError('Unexpected check reports')
r['snapshot_head']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();r['fresh_modules']=[]
for name,stage in [('FoundationHAEquality','main-stage1'),('FoundationHAEqualityChecks','checks-stage2')]:
 source=d/'Lean/DiophantineConsistency'/f'{name}.lean';obj=p/'DiophantineConsistency'/f'{name}.olean';log=p/f'{stage}.log'
 check(source,sha(p/f'{stage}.lean'))
 content=source.read_text()
 if any(re.search(pat,content) for pat in [r'\bsorry\b',r'\bnative_decide\b',r'^axiom\s',r'\bBProv\b']):raise RuntimeError('Forbidden shortcut')
 r['fresh_modules'].append(dict(module='DiophantineConsistency.'+name,source=str(source.relative_to(root)),source_sha256=sha(source),lines=len(content.splitlines()),object=str(obj),object_sha256=sha(obj),log=str(log),log_sha256=sha(log),exit_code=0,command=f'lake env bash -c \'export LEAN_PATH="{p}:$LEAN_PATH"; lean -M6000 -j1 {source.relative_to(root)} -o {obj}\''))
r['axiom_audits']=audit;r['fresh_scope']='Two fresh new leaves only; all76 Foundation and16 PAHF/HA prerequisites authenticated and reused. Nine actual equality-theory cases. No order or induction axiom image, model, or full HA equation equivalence claimed.'
r['choice_scope']='The reused Foundation Derivation.imply_doubleNegation theorem reports Classical.choice in Lean metatheory. Its image is an actual intuitionistic HA.Derives proof. No choice/classical rule is added to HA; equality_stable and lt_transport themselves report only propext/Quot.sound.'
r['development_failures']=[dict(log=str(p/'checks-stage1.log'),sha256=sha(p/'checks-stage1.log'),exit_code=1,reason='Two shorthand source constructors lacked explicit language annotation. Corrected to Theory.eqAxiom.relExt/funcExt (L := oRing). Final proof statements unchanged; no failed object accepted.')]
bundle=d/'reviews/foundation-ha-equality-author-replay';bundle.mkdir(exist_ok=True)
files=[p/'main-stage1.lean',p/'main-stage1.log',p/'checks-stage1.lean',p/'checks-stage1.log',p/'checks-stage2.lean',p/'checks-stage2.log',p/'prerequisites.json',Path('/tmp/foundation-ha-equality-prepare.py'),Path(__file__)]
for f in files:shutil.copyfile(f,bundle/f.name)
r['bundle_files']={f.name:sha(bundle/f.name) for f in files}
r['freeze_driver_sha256']=sha(__file__)
out=d/'reviews/foundation-ha-equality-dependency-replay.json';out.write_text(json.dumps(r,indent=2)+'\n')
print('snapshot',r['snapshot_head']);print('manifest',sha(out));print('axiom reports',len(audit))
for m in r['fresh_modules']:print(m['module'],m['lines'],m['source_sha256'],m['object_sha256'])
