from pathlib import Path
import json,hashlib,re,tempfile
root=Path('/home/codex/.codex/worktrees/46be/Proofs'); d=root/'Computability/DiophantineConsistency'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(p,h):
 if sha(p)!=h:raise RuntimeError('Pin mismatch '+str(p))
oldpath=d/'reviews/foundation-ha-arithmetic-dependency-replay.json';check(oldpath,'3a3f7a2ad81e7dbf94e41e914635cd062e590813790009feca515f8c513cb050');old=json.loads(oldpath.read_text())
logicpath=d/'reviews/foundation-pahf-logic-dependency-replay.json';logic=json.loads(logicpath.read_text())
natpath=d/'reviews/ha-natural-cases-replay.json';nat=json.loads(natpath.read_text())
eqpath=d/'reviews/ha-equality-decidable-replay.json';eq=json.loads(eqpath.read_text())
mods=old['nonfoundation']+[m for m in old['fresh_modules'] if m['module'].endswith('.FoundationHAArithmetic')]+[m for m in logic['fresh_modules'] if m['module'].endswith('.FoundationPAHFLogic')]
for r,name in [(nat,'HANaturalCases'),(eq,'HAEqualityDecidable')]:
 m=next(m for m in r['results'] if m['module']==name)
 mods.append(dict(module='DiophantineConsistency.'+name,source=str(Path(m['source']).relative_to(root)),source_sha256=m['source_sha256'],object=m['object'],object_sha256=m['object_sha256']))
if len(mods)!=16:raise RuntimeError('Expected sixteen non-Foundation modules')
foundation=old['foundation']; by={m['module']:m for m in foundation}; selected=set();todo=['Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic','Foundation.FirstOrder.NegationTranslation.GoedelGentzen','Foundation.FirstOrder.Intuitionistic.Deduction','Foundation.FirstOrder.Intuitionistic.Rew']
base=Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation')
while todo:
 mod=todo.pop()
 if mod in selected:continue
 selected.add(mod)
 if mod not in by:raise RuntimeError('New Foundation import '+mod)
 for line in Path(by[mod]['source']).read_text().splitlines():
  m=re.match(r'\s*(?:(?:public|private)\s+)?import\s+(Foundation\.\S+)',line)
  if m:todo.append(m.group(1))
if selected!=set(by):raise RuntimeError('Closure changed')
for m in old['prior_manifests']:check(root/m['path'],m['sha256'])
for k,v in old['package_identity'].items():check(root/k,v['current_sha256'])
check(old['compiler']['path'],old['compiler']['sha256'])
for m in foundation:
 check(m['source'],m['source_sha256']);check(m['trace'],m['trace_sha256'])
 for o in m['objects']:check(o['path'],o['sha256'])
for m in mods:check(root/m['source'],m['source_sha256']);check(m['object'],m['object_sha256'])
p=Path(tempfile.mkdtemp(prefix='foundation-ha-equality-'))
for m in foundation:
 for o in m['objects']:
  suffix=Path(o['path']).name.removeprefix(Path(m['source']).stem);dst=p/Path(*m['module'].split('.')).with_suffix(suffix);dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(o['path'])
for m in mods:
 dst=p/Path(*m['module'].split('.')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(m['object'])
r=dict(private=str(p),foundation=foundation,nonfoundation=mods,compiler=old['compiler'],package_identity=old['package_identity'],prior_manifests=[dict(path=str(f.relative_to(root)),sha256=sha(f)) for f in [oldpath,logicpath,natpath,eqpath]],scope='76 Foundation plus16 custom prerequisites exact-source/object reuse; no new Foundation module, no prerequisite compilation.',prepare_driver_sha256=sha(__file__))
(p/'prerequisites.json').write_text(json.dumps(r,indent=2)+'\n');print(p)
