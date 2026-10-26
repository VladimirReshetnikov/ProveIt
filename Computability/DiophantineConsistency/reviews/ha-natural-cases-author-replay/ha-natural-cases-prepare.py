from pathlib import Path
import json,hashlib,tempfile,os
root=Path('/home/codex/.codex/worktrees/46be/Proofs')
reviews=root/'Computability/DiophantineConsistency/reviews'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
old=json.loads((reviews/'ha-basic-arithmetic-dependency-replay.json').read_text())
rows=old['modules']+[dict(module='DiophantineConsistency.HABasicArithmetic', source=str(root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/HABasicArithmetic.lean'),source_sha256='7922744c26ffd0b307b019696197aaa3cdb5acd49ed173e158d6e3a29011e3a2',object='/tmp/ha-basic-arithmetic-root-peer-3xa84gxk/DiophantineConsistency/HABasicArithmetic.olean',object_sha256='9ac98d23ef023abd264c329ecfdf3a628f94604157bfaf4419ace8c7be6b9bfd')]
out=Path(tempfile.mkdtemp(prefix='ha-natural-cases-author-'))
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
manifest=dict(private=str(out),lib=str(lib),compiler=str(compiler),modules=rows,pins=pins,head=os.popen('git rev-parse HEAD').read().strip(),scope='Eight authenticated custom prerequisites reused; only the new NaturalCases pair freshly compiled; core Lean toolchain boundary.')
(out/'inputs.json').write_text(json.dumps(manifest,indent=2)+'\n')
Path('/tmp/ha-natural-cases-current').write_text(str(out))
print(out)
