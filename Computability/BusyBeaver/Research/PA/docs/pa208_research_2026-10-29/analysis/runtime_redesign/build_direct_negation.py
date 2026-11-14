"""Replace four stack-roundtrip negations by direct Cantor arithmetic.

All variants preserve the exact counter-machine partial function. Their
primitive graphs outside the four closed arithmetic intervals are audited.
"""
from pathlib import Path
import sys,json,functools,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent))
import build_fixed_cover as f
s=f.s;br=f.br
OUT=Path('analysis/runtime_redesign/direct_negation');OUT.mkdir(exist_ok=True)
def existing(n):
 t=f.node(n)
 matches=[u for u in f.old_nodes if br.size(u)==br.size(t) and s.boundary(u)==s.boundary(t) and s.graph_intervals(s.sites(u))==s.graph_intervals(s.sites(t))]
 assert len(matches)==1,(n,len(matches));return matches[0]
pair=existing(162);quad=existing(117);move=existing(216)
incs4=[u for u in f.old_nodes if br.size(u)==4 and all((op,arg)==('CI',1) for p,op,arg in s.sites(u))]
assert incs4
@functools.cache
def associations(parts):
 if len(parts)==1:return parts
 return tuple((a,b) for k in range(1,len(parts)) for a in associations(parts[:k]) for b in associations(parts[k:]))
original=f.M['m218'];hits=[]
def locate(t,path='',off=0):
 if t==original:hits.append((path,off,off+br.size(t)));return
 if not s.leaf(t):locate(t[0],path+'0',off);locate(t[1],path+'1',off+br.size(t[0]))
locate(f.old_tree);assert len(hits)==4 and all(a>=137 for p,a,b in hits)
def replace_all(t,replacement):
 if t==original:return replacement
 if s.leaf(t):return t
 return (replace_all(t[0],replacement),replace_all(t[1],replacement))
variants={
 'n20':(move,('CI',1),pair,quad),
 'n18':(('CI',7),('CI',7),pair,quad),
}
for k,t in enumerate(incs4):variants['n24_'+str(k)]=(pair,quad,t,t)
records=[]
for kind,parts in variants.items():
 for idx,replacement in enumerate(associations(parts)):
  assert s.boundary(replacement)==(0,0,False)
  tree=replace_all(f.old_tree,replacement);metric=s.metrics(tree)
  records.append((metric['dag_nodes'],metric['maximum_depth'],metric['maximum_zero_run'],kind,idx,tree,replacement))
records.sort(key=lambda r:r[:5]);summary=[]
for dag,height,zeros,kind,idx,tree,replacement in records:
 name=kind+'_'+str(idx);rows=s.sites(tree);g,checks=s.graph_arithmetic(rows);assert g==s.graph_intervals(rows)
 assert rows[:137]==f.old_sites[:137]
 size=br.size(replacement);delta=size-br.size(original)
 def shift(i):return i+delta*sum(i>=b for p,a,b in hits)
 def internal(i):return any(a<=i<b for p,a,b in hits)
 for i,(eff,targets) in enumerate(f.old_graph):
  if internal(i):continue
  assert all(not any(a<j<b for p,a,b in hits) for j in targets),('interior entry',i,targets)
  assert g[shift(i)]==[eff,[shift(j) for j in targets]],('exterior mismatch',i)
 raw=s.compact(rows)
 receipt={'name':name,'metrics':s.metrics(tree),'new_macro_size':size,'old_macro_size':47,
  'total_primitive_saving':-4*delta,'occurrences':hits,'new_intervals':[[a+k*delta,a+k*delta+size] for k,(p,a,b) in enumerate(hits)],
  'source_sha256':hashlib.sha256(raw).hexdigest(),'startup_137_sites_equal':True,'exterior_cfg_identity':True,'independent_cfg_resolvers_agree':True,'arithmetic_successor_checks':checks,
  'direct_macro_tree':replacement}
 (OUT/(name+'.sites.json')).write_bytes(raw)
 (OUT/(name+'.tree.json')).write_text(json.dumps(tree,separators=(',',':'))+'\n')
 (OUT/(name+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 summary.append({k:v for k,v in receipt.items() if k not in ['direct_macro_tree','occurrences','new_intervals']})
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
