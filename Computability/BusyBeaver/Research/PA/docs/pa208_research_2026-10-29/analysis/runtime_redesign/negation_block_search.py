from pathlib import Path
import sys,json,functools,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent));import build_fixed_cover as f
s=f.s;br=f.br
OUT=Path('analysis/runtime_redesign/direct_negation');q=f.M['m180'];e=(q,('CI',1))
for u in f.old_nodes:
 if br.size(u)==30 and s.boundary(u)==(0,0,False) and s.graph_intervals(s.sites(u))==s.graph_intervals(s.sites(e)):e=u;break
@functools.cache
def ass(parts):
 if len(parts)==1:return parts
 return tuple((a,b) for k in range(1,len(parts)) for a in ass(parts[:k]) for b in ass(parts[k:]))
def tup(t):return tuple(map(tup,t)) if isinstance(t,list) else t
macros={'old':f.M['m218']}
for kind in ['n18_0','n18_2','n20_0','n20_2','n24_0_2','n24_0_4']:
 macros[kind]=tup(json.loads((OUT/(kind+'.json')).read_text())['direct_macro_tree'])
best=None;results=[]
for kind,n in macros.items():
 entries=[]
 for i,a in enumerate(ass((q,n,q,n))):
  for j,b in enumerate(ass((e,n,q,n))):
   tree=f.old_tree
   for lo,hi,t in [(3685,3732,n),(3555,3602,n),(2489,2642,b),(965,1117,a)]:tree=br.splice(tree,lo,hi,t)
   m=s.metrics(tree)
   entries.append((m['dag_nodes'],m['maximum_zero_run'],m['maximum_depth'],i,j,tree))
 entries.sort(key=lambda r:r[:5]);valid=[x for x in entries if x[1]<=6 and x[2]<=56]
 if not valid:continue
 x=valid[0];tree=x[-1];rows=s.sites(tree);g,checks=s.graph_arithmetic(rows);assert g==s.graph_intervals(rows)
 assert rows[:137]==f.old_sites[:137]
 raw=s.compact(rows);name='blocks_'+kind
 (OUT/(name+'.sites.json')).write_bytes(raw);(OUT/(name+'.tree.json')).write_text(json.dumps(tree,separators=(',',':'))+'\n')
 receipt={'metrics':s.metrics(tree),'negation':kind,'first_block_association':x[3],'second_block_association':x[4],
          'source_sha256':hashlib.sha256(raw).hexdigest(),'startup_137_sites_equal':True,
          'independent_cfg_resolvers_agree':True,'candidate_counts':len(entries),
          'all_candidate_metrics':[x[:5] for x in entries]}
 (OUT/(name+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 results.append(receipt);print(name,receipt['metrics'],receipt['source_sha256'],flush=True)
(OUT/'block_search_summary.json').write_text(json.dumps(results,indent=2)+'\n')
