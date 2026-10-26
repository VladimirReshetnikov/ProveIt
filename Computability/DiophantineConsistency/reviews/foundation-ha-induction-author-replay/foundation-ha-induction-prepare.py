from pathlib import Path
import json,hashlib,re,tempfile
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency';base=Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(p,h):
 if sha(p)!=h:raise RuntimeError('Pin mismatch '+str(p))
eqpath=d/'reviews/foundation-ha-equality-dependency-replay.json';check(eqpath,'0e1256f899ab80021082845e54f28482c000e05f0760f2b8d833d688c4516a68');old=json.loads(eqpath.read_text())
clpath=d/'reviews/foundation-ha-closure-dependency-replay.json';cl=json.loads(clpath.read_text())
invpath=d/'reviews/arithmetic-machine215-replay/arithmetic215-foundation-trace-inputs.json';tsvpath=d/'reviews/arithmetic-machine215-replay/arithmetic215-foundation-lake-hashes.tsv'
check(invpath,'d7fbeeecc25a737abcbec4b9bf8b275444dbf84100a7d941eca3a605165c5d32');check(tsvpath,'ae21feaccda73df165ed7ad9374a296e5a8314ea4ad864ec4acc6008303c2b78')
inv={m['module']:m for m in json.loads(invpath.read_text())};lake=dict(line.split('\t') for line in tsvpath.read_text().splitlines())
selected=set();todo=['Foundation.FirstOrder.Arithmetic.Schemata','Foundation.FirstOrder.NegationTranslation.GoedelGentzen']
while todo:
 mod=todo.pop()
 if mod in selected:continue
 selected.add(mod)
 if mod not in inv:raise RuntimeError('New unauthenticated import '+mod)
 for line in (base/Path(*mod.split('.')).with_suffix('.lean')).read_text().splitlines():
  m=re.match(r'\s*(?:(?:public|private)\s+)?import\s+(Foundation\.\S+)',line)
  if m:todo.append(m.group(1))
if len(selected)!=85:raise RuntimeError('Unexpected Foundation closure')
foundation=[]
for mod in sorted(selected):
 m=inv[mod];check(m['source'],m['source_sha256']);check(m['trace'],m['trace_sha256']);trace=json.loads(Path(m['trace']).read_text());inputs=dict(trace['inputs'])
 if m['compiler']!=['Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35']:raise RuntimeError('Compiler mismatch')
 if inputs[m['source']]!=m['expected_source_lake_hash'] or lake[m['source']]!=m['expected_source_lake_hash']:raise RuntimeError('Source Lake mismatch')
 expected=trace['outputs']['o']+[trace['outputs']['r']]
 if len(m['objects'])!=4:raise RuntimeError('Companion count')
 for o in m['objects']:
  check(o['path'],o['sha256']);suffix=Path(o['path']).name.removeprefix(Path(m['source']).stem)
  if o['expected_lake_hash']+suffix not in expected or lake[o['path']]!=o['expected_lake_hash']:raise RuntimeError('Object Lake mismatch')
 foundation.append(m)
mods=old['nonfoundation']+[m for m in old['fresh_modules'] if m['module'].endswith('.FoundationHAEquality')]+[m for m in cl['fresh_modules'] if m['module'].endswith('.FoundationHAClosure')]
if len(mods)!=18:raise RuntimeError('Expected18 custom prerequisites')
for m in old['prior_manifests']:check(root/m['path'],m['sha256'])
for k,v in old['package_identity'].items():check(root/k,v['current_sha256'])
check(old['compiler']['path'],old['compiler']['sha256'])
for m in mods:check(root/m['source'],m['source_sha256']);check(m['object'],m['object_sha256'])
p=Path(tempfile.mkdtemp(prefix='foundation-ha-induction-'))
for m in foundation:
 for o in m['objects']:
  suffix=Path(o['path']).name.removeprefix(Path(m['source']).stem);dst=p/Path(*m['module'].split('.')).with_suffix(suffix);dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(o['path'])
for m in mods:
 dst=p/Path(*m['module'].split('.')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(m['object'])
r=dict(private=str(p),foundation=foundation,nonfoundation=mods,compiler=old['compiler'],package_identity=old['package_identity'],prior_manifests=[dict(path=str(f.relative_to(root)),sha256=sha(f)) for f in [eqpath,clpath,invpath,tsvpath]],scope='85 Foundation plus18 custom prerequisites exact-source/object reuse. Nine additional Foundation imports all authenticated against accepted95 inventory and original Lake source/output hashes. No prerequisite compilation.',prepare_driver_sha256=sha(__file__))
(p/'prerequisites.json').write_text(json.dumps(r,indent=2)+'\n');print(p)
