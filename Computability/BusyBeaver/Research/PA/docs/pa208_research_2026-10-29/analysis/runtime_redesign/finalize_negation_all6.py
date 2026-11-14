"""Produce and audit the six-occurrence direct-negation source variant."""
from pathlib import Path
import sys,json,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent));import build_fixed_cover as f
s=f.s;br=f.br;out=Path('analysis/runtime_redesign/direct_negation')
def tup(t):return tuple(map(tup,t)) if isinstance(t,list) else t
replacement=tup(json.loads((out/'n18_0.json').read_text())['direct_macro_tree'])
intervals=[(994,1041),(1070,1117),(2519,2566),(2595,2642),(3555,3602),(3685,3732)]
reference=s.graph_intervals(s.sites(f.M['m218']))
for a,b in intervals:
 oldword=br.serial(br.closed_forest(f.old_tree,a,b))
 assert s.graph_intervals(s.sites(oldword))==reference
 assert br.size(oldword)==47
 assert s.boundary(oldword)==(0,0,False)
tree=f.old_tree
for a,b in reversed(intervals):tree=br.splice(tree,a,b,replacement)
rows=s.sites(tree);g,checks=s.graph_arithmetic(rows);assert g==s.graph_intervals(rows)
delta=18-47
shift=lambda i:i+delta*sum(i>=b for a,b in intervals)
for i,(effect,targets) in enumerate(f.old_graph):
 if any(a<=i<b for a,b in intervals):continue
 assert all(not any(a<j<b for a,b in intervals) for j in targets)
 assert g[shift(i)]==[effect,[shift(j) for j in targets]]
assert rows[:137]==f.old_sites[:137]
raw=s.compact(rows)
preview=out/'n18_all6_preview.sites.json'
assert not preview.exists() or raw==preview.read_bytes()
(out/'n18_all6.sites.json').write_bytes(raw)
(out/'n18_all6.tree.json').write_text(json.dumps(tree,separators=(',',':'))+'\n')
receipt={'metrics':s.metrics(tree),'source_sha256':hashlib.sha256(raw).hexdigest(),
 'old_intervals':intervals,'new_intervals':[[a+k*delta,a+k*delta+18] for k,(a,b) in enumerate(intervals)],
 'old_macro_size':47,'new_macro_size':18,'occurrences':6,'total_primitive_saving':174,
 'startup_137_sites_equal':True,'all_old_intervals_have_exact_negation_cfg':True,
 'exterior_cfg_identity':True,'independent_cfg_resolvers_agree':True,
 'arithmetic_successor_checks':checks,'matches_previously_screened_preview':preview.exists()}
(out/'n18_all6.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
