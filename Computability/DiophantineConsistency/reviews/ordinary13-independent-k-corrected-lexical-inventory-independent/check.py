from pathlib import Path
from hashlib import sha256
from collections import Counter,defaultdict
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-corrected-lexical-inventory-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-corrected-lexical-inventory')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
m=json.loads((p/'manifest.json').read_text());sel=m['selected'];base=json.loads(Path('research/ordinary13-fixed85-source-selection-plan/selection.json').read_text())['selected_modules']
assert m['root']=='IndependentKPositiveCorrectedComposition' and len(sel)==821 and not m['cycles'] and not m['ambiguous_frontier']
assert Counter(d['selection_basis'] for d in sel.values())=={'fixed85 JSON baseline':691,'single byte-equivalence class':129,'explicit root':1}
assert not any(d['baseline_alternative'] for d in sel.values())
# Independently index the stated bounded research basename scope.
idx=defaultdict(list)
for f in Path('research').rglob('*.lean*'):
 if f.name.endswith('.lean.src'):idx[f.name[:-9]].append(str(f))
 elif f.name.endswith('.lean'):idx[f.name[:-5]].append(str(f))
for name,d in sel.items():
 paths=sorted([str(Path('Lean')/('/'.join(name.split('.'))+'.lean'))] if '.' in name and (Path('Lean')/('/'.join(name.split('.'))+'.lean')).is_file() else (idx[name] if '.' not in name else []))
 actual=[{'path':x,'sha256':sha256(Path(x).read_bytes()).hexdigest()} for x in paths]
 assert actual==d['observed_candidates'] and len({x['sha256'] for x in actual})==1
 assert sha256(Path(d['path']).read_bytes()).hexdigest()==d['sha256']
 if d['selection_basis']=='fixed85 JSON baseline':
  assert d['path']==base[name]['source_path'] and d['sha256']==base[name]['sha256'] and not base[name]['alternative']
# Independent line-based header/import re-read, retaining scanner's lexical scope.
for name,d in sel.items():
 imports=[]
 for line in Path(d['path']).read_text().splitlines():
  line=line.strip().split('--',1)[0].strip()
  if line.startswith('public import '):line=line[7:]
  if line.startswith('import '):imports+=line[7:].split()
 assert imports==d['imports'],name
order=m['local_order'];pos={n:i for i,n in enumerate(order)};assert len(order)==len(pos)==len(sel)
for n,d in sel.items():
 for dep in d['imports']:
  if dep in sel:assert pos[dep]<pos[n]
  else:assert dep in m['missing_frontier']
front=m['missing_frontier'];assert Counter(n.split('.')[0] for n in front)=={'Mathlib':39,'Foundation':4,'BusyBeaver':3}
for name,obs in m['frontier_source_observations'].items():
 rel=Path('/'.join(name.split('.'))+'.lean')
 if name.startswith('Mathlib.'):paths=[Path('../../.lake/packages/mathlib')/rel]
 elif name.startswith('Foundation.'):paths=[Path('../../lib/FormalizedFormalLogic-Foundation')/rel]
 else:paths=[Path('../../Computability/BusyBeaver/Lean')/rel]+sorted(Path('reviews').glob('*/sources/'+str(rel)))
 actual=[{'path':str(x),'sha256':sha256(x.read_bytes()).hexdigest()} for x in paths if x.is_file()]
 assert actual==obs['candidates'] and len({x['sha256'] for x in actual})==1
 if name.startswith('BusyBeaver.'):assert len(actual)==32
 else:assert len(actual)==1
print(json.dumps({'author_receipt_reproduced':True,'selected_names':len(sel),'baseline_choices':691,'observed_single_candidate_names':821,'frontier_counts':{'Mathlib':39,'Foundation':4,'BusyBeaver':3},'busybeaver_identical_observed_sources_per_name':32,'local_dependency_order_checked':True,'actual_provider_or_object_selection_verified':False,'lean_executed':False},sort_keys=True,indent=2))
