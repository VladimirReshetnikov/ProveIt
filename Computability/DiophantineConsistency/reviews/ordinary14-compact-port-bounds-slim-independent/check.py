from pathlib import Path
import hashlib, json, subprocess, sys
D = Path(__file__).resolve().parents[2]
a = D/'research/ordinary14-compact-port-bounds-slim-draft'
hashfile = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
old = (D/'Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean').read_text()
new = (a/'CompactPortBoundsSlim.lean').read_text()
oldblock = old[old.index('theorem port_bounds '):old.index('\n/-- `0 < K0`')].strip()
newblock = new[new.index('theorem port_bounds '):new.index('\n\nend DiophantineConsistency.CompactPortBoundsSlimDraft')].strip()
assert oldblock == newblock
context = 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]'
assert context in old and context in new
imports = [x.removeprefix('import ') for x in new.splitlines() if x.startswith('import ')]
assert imports == ['DiophantineConsistency.Compact44.CompactMaskBoundFinish', 'DiophantineConsistency.Compact44.CompactSymbolicPorts', 'DiophantineConsistency.ArithmeticStandardCasts']
paths = [D/'Lean'/Path(*name.split('.')).with_suffix('.lean') for name in imports]
assert all(p.is_file() for p in paths)
assert 'theorem bounds ' in paths[0].read_text()
ports = paths[1].read_text()
for token in ('def lowNat ', 'def highNat ', 'def ports '): assert token in ports
assert 'theorem cast_exp ' in paths[2].read_text() or 'lemma cast_exp ' in paths[2].read_text()
assert 'namespace DiophantineConsistency.CompactPortBoundsSlimDraft' in new
assert 'open CompactSymbolicPorts' in new
assert 'import DiophantineConsistency.Mixed121' not in new
result = subprocess.run([sys.executable, '-I', '-S', '-B', str(a/'check_source.py')],check=True,capture_output=True,text=True)
assert json.loads(result.stdout) == json.loads((a/'observation.json').read_text())
print(json.dumps({'original_source_sha256':hashfile(D/'Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean'),'slim_source_sha256':hashfile(a/'CompactPortBoundsSlim.lean'),'author_readme_sha256':hashfile(a/'README.md'),'author_checker_sha256':hashfile(a/'check_source.py'),'author_observation_sha256':hashfile(a/'observation.json'),'original_theorem_sha256':hashlib.sha256(oldblock.encode()).hexdigest(),'theorem_and_context_identical':True,'source_imports':[{'module':n,'sha256':hashfile(p)} for n,p in zip(imports,paths)],'author_receipt_replayed':True,'lean_elaborated':False},indent=2,sort_keys=True))
