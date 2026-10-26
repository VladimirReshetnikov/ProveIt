from pathlib import Path
import json,hashlib,tempfile,os
root=Path('/home/codex/.codex/worktrees/46be/Proofs')
reviews=root/'Computability/DiophantineConsistency/reviews'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=json.loads(Path('/tmp/ha-natural-cases-author-sjurd49t/inputs.json').read_text())
rows=old['modules']+[dict(module='DiophantineConsistency.HANaturalCases',source=str(root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/HANaturalCases.lean'),source_sha256='7c1552f2f650238b04b7fc2fb142c2ab3aaf7885278f6e49aaaf66b8c5e1b1a3',object='/tmp/ha-natural-cases-author-sjurd49t/lib/DiophantineConsistency/HANaturalCases.olean',object_sha256='7e7aeef7beb97e0a8747af6c5553d6d0f81232c756106bcf16f07265ebee5e1e')]
out=Path(tempfile.mkdtemp(prefix='ha-equality-decidable-author-'))
lib=out/'lib'; lib.mkdir()
pins=[]
for r in rows:
 for key in ['source','cache_source','object']:
  if key in r:
   assert sha(r[key])==r[key+'_sha256'],r[key]
   pins.append(dict(path=r[key],sha256=r[key+'_sha256']))
 src=Path(r['object']); dest=lib/Path(*r['module'].split('.')).with_suffix('.olean'); dest.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['', '.private', '.server']:
  s=Path(str(src)+suffix)
  if s.exists():
   Path(str(dest)+suffix).symlink_to(s)
   pins.append(dict(path=str(s),sha256=sha(s)))
compiler=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
assert sha(compiler)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
pins.append(dict(path=str(compiler),sha256=sha(compiler)))
for p in [root/'lean-toolchain',root/'lake-manifest.json']:
 pins.append(dict(path=str(p),sha256=sha(p)))
manifest=dict(private=str(out),lib=str(lib),compiler=str(compiler),modules=rows,pins=pins,head=os.popen('git rev-parse HEAD').read().strip(),scope='Nine authenticated custom prerequisites reused; only the new EqualityDecidable pair freshly compiled; core Lean toolchain boundary.')
(out/'inputs.json').write_text(json.dumps(manifest,indent=2)+'\n')
Path('/tmp/ha-equality-decidable-current').write_text(str(out))
print(out)
