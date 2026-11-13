from pathlib import Path
from hashlib import sha256
from collections import Counter
import json,re,subprocess,sys,tomllib
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-fixed85-frontier-source-independent');A=Path('research/ordinary13-fixed85-frontier-source-inventory');repo=Path.cwd().parents[1]
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
receipt=json.loads((A/'receipt.json').read_text()); manifest=json.loads(Path('research/ordinary13-fixed85-native-composition-draft/manifest.json').read_text())
lake=tomllib.loads((repo/'lakefile.toml').read_text());libs={x['name']:x.get('srcDir','.') for x in lake['lean_lib']}
for k,root in {'Foundation':'lib/FormalizedFormalLogic-Foundation','BusyBeaver':'Computability/BusyBeaver/Lean','PAHF':'Logic/Interpretability/PAHF/Lean','ZFCinPA':'Logic/Interpretability/ZFCinPA/Lean'}.items():assert libs[k]==root,(k,libs[k])
expected=Counter({'configured_foundation_source':26,'other_repository_source_root':24,'mathlib_package_source':42,'lean_toolchain_source':1,'missing_in_checked_roots':1})
assert Counter(x['status'] for x in receipt['frontier_modules'])==expected
assert len(receipt['frontier_modules'])==94 and [x['module'] for x in receipt['frontier_modules'] if x['status']=='missing_in_checked_roots']==['Mathlib.Tactic.Omega']
for row in receipt['frontier_modules']:
 if row['found_source']:
  p=Path(row['found_source']);assert p.is_file() and sha256(p.read_bytes()).hexdigest()==row['found_sha256']
foundation=repo/'lib/FormalizedFormalLogic-Foundation'
assert subprocess.check_output(['git','-C',str(foundation),'rev-parse','HEAD'],text=True).strip()==receipt['foundation_gitlink']
assert subprocess.check_output(['git','-C',str(foundation),'status','--porcelain=v1','--untracked-files=all'],text=True)==''
route=receipt['source_only_route_to_missing_mathlib_module']
for src,dst in zip(route,route[1:]):
 p=Path(manifest['local_modules'][src]['path']);assert sha256(p.read_bytes()).hexdigest()==manifest['local_modules'][src]['sha256']
 imports=[]
 for line in p.read_text().splitlines():
  m=re.match(r'^\s*import\s+([^/]+)',line)
  if m:imports.extend(m.group(1).split())
 assert dst in imports,(src,dst)
assert (repo/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.32.0'
math=repo/'.lake/packages/mathlib';assert math.is_dir()
assert not (math/'Mathlib/Tactic/Omega.lean').exists() and not (math/'.lake/build/lib/lean/Mathlib/Tactic/Omega.olean').exists()
assert Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Elab/Tactic/Omega.lean').is_file()
imp=Path(manifest['local_modules']['ResidueSignFreePower']['path']).read_text()
assert len(re.findall(r'\bomega\b',imp))>=3
print(json.dumps({'author_receipt_reproduces':True,'configured_roots_checked':4,'exact_route_edges_checked':len(route)-1,'frontier_counts':dict(sorted(expected.items())),'configured_mathlib_is_symlink':math.is_symlink(),'foundation_clean_at_gitlink':True,'omega_source_and_expected_package_object_absent':True,'lean_omega_toolchain_source_present':True,'lean_executed':False,'transitive_provider_trace_proved':False},sort_keys=True,indent=2))
