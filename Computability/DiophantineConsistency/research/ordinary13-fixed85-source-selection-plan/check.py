from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-source-selection-plan')
expected=(D/'selection.json').read_bytes()
actual=subprocess.check_output([sys.executable,'-I','-S','-B',str(D/'plan.py')])
assert actual==expected,'local source plan changed'
m=json.loads(expected);selected=m['selected_modules'];order=m['dependency_first_order']
assert len(order)==len(selected)==len(set(order))
pos={n:i for i,n in enumerate(order)}
for n,r in selected.items():
 assert sha256(Path(r['source_path']).read_bytes()).hexdigest()==r['sha256']
 for dep in r['imports']:
  if dep in pos:assert pos[dep]<pos[n],(n,dep)
assert len({r['virtual_logical_path'] for r in selected.values()})==len(selected)
assert len({r['source_path'] for r in selected.values()})==len(selected)
assert len(m['local_alternatives'])==9
assert set(m['local_alternatives'])=={n for n,r in selected.items() if r['alternative']}
assert 'Fixed85Endpoint' in m['reverse_affected_order']
assert 'Mathlib.Tactic.Omega' not in m['external_frontier']
base=json.loads(Path('research/ordinary13-fixed85-native-composition-draft/manifest.json').read_text())
assert set(base['local_modules'])==set(selected)
assert set(base['external_frontier'])-set(m['external_frontier'])=={'Mathlib.Tactic.Omega'}
assert not (set(m['external_frontier'])-set(base['external_frontier']))
print(json.dumps({'selection_sha256':sha256(expected).hexdigest(),
 'plan_sha256':sha256((D/'plan.py').read_bytes()).hexdigest(),
 'selected_local_module_count':len(selected),'explicit_alternatives':len(m['local_alternatives']),
 'external_frontier_names_count':len(m['external_frontier']),
 'reverse_affected_local_count':m['reverse_affected_local_count'],
 'local_lexical_cycles':0,'external_files_or_objects_checked':False,
 'lean_executed':False,'status':'Read-only local source selection and lexical order; external/object/provider, Lean, axioms and PDF checks excluded.'},sort_keys=True,indent=2))
