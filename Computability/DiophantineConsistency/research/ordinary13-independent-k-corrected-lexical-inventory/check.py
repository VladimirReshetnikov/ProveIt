from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-corrected-lexical-inventory')
expected=(D/'manifest.json').read_bytes();actual=subprocess.check_output([sys.executable,'-I','-S','-B',str(D/'scan.py')])
assert actual==expected,'lexical source inventory changed'
m=json.loads(expected);selected=m['selected'];order=m['local_order'];assert len(order)==len(selected)==len(set(order)) and not m['cycles']
pos={n:i for i,n in enumerate(order)}
for n,x in selected.items():
 assert sha256(Path(x['path']).read_bytes()).hexdigest()==x['sha256']
 for dep in x['imports']:
  if dep in selected:assert pos[dep]<pos[n],(n,dep)
  else:assert dep in m['ambiguous_frontier'] or dep in m['missing_frontier'],(n,dep)
for x in m['frontier_source_observations'].values():
 for c in x['candidates']:assert sha256(Path(c['path']).read_bytes()).hexdigest()==c['sha256']
for n in ('IndependentKPositiveCorrectedComposition','IndependentKRankRepresentationCorrected',
 'IndependentKZeroGraphFacts','IndependentKFixedCompactPorts','IndependentKJPositive',
 'IndependentKUnitGraph','IndependentKUnitBridge','IndependentKFirstRankDiscrete','IndependentKZeroMainRank'):
 assert n in selected,n
print(json.dumps({'manifest_sha256':sha256(expected).hexdigest(),
 'scanner_sha256':sha256((D/'scan.py').read_bytes()).hexdigest(),
 'selected_local_names':len(selected),'ambiguous_frontier_names':len(m['ambiguous_frontier']),
 'unresolved_frontier_names':len(m['missing_frontier']),
 'frontier_with_observed_sources':sum(bool(x['candidates']) for x in m['frontier_source_observations'].values()),
 'local_lexical_cycles':len(m['cycles']),'lean_executed':False,'source_selection_is_provider_validation':False},sort_keys=True,indent=2))
