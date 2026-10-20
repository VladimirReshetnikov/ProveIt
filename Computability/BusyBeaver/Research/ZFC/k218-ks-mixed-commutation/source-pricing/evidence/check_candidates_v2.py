#!/usr/bin/env python3
"""Validate saved two-splice beam candidates against exact formulas and whole CFG."""
from pathlib import Path
import json,sys
sys.dont_write_bytecode=True
import source_language as s,build221 as b,measure_pinned as m
P=Path(__file__).resolve().parent;plan=json.loads((P/'input.json').read_text());dp=json.loads((P/'joint-v2-result.json').read_text())
seed=Path(plan['seed']);raw=(seed/'sites218.json').read_bytes();tab=(seed/'k218.native.tm').read_bytes()
assert m.sha(raw)==plan['seed_source_sha256']and m.sha(tab)==plan['seed_table_sha256']
tree=s.tree(json.loads(raw));table=b.read_table(tab);oldflat=m.flat(tree);oldrows=s.sites(tree);oldgraph=s.graph_arithmetic(oldrows)[0];assert oldgraph==s.graph_intervals(oldrows)
base=[]
for row in plan['nodes']:base.append(tuple(row['leaf'])if'leaf'in row else tuple(base[i]for i in row['children']))
macros={k:base[i]for k,i in plan['macro_ids'].items()}
def decode(w):
 stack=[]
 for c in w:
  if c in'IQ':r,l=stack.pop(),stack.pop();stack.append((c,l,r))
  else:stack.append(c)
 assert len(stack)==1;return stack[0]
I=lambda x,y:('I',x,y);Q=lambda x,y:('Q',x,y);N=lambda x:I(x,'F')
K=I('a',I('b','a'));S=I(I('a',I('b','c')),I(I('a','b'),I('a','c')));M=I(Q('a',N(N(Q('b','c')))),N(N(Q('b',Q('a','c')))))
def rename(f,p):
 return(f[0],rename(f[1],p),rename(f[2],p))if isinstance(f,tuple)else dict(zip('abc',p)).get(f,f)
for word,r in plan['recipes'].items():
 actual=[decode(x)for x in r['formula_postfix']]
 if r['kind']=='KS':
  expected=[rename(f,p)for f,p in zip([K,S],r['permutations'])];expected=[expected[i]for i in r['order']]
 else:expected=[rename(M,r['permutation'])]
 assert actual==expected and ''.join(r['formula_postfix'])==word

def restore(x):return base[x]if type(x)==int else(restore(x[0]),restore(x[1]))
def map_old(i,d0,d1):
 assert not(135<i<486 or 1474<i<1773),('Outside edge enters changed interior',i)
 return i+(d0 if i>=486 else 0)+(d1 if i>=1773 else 0)
out=P/'verified-v2';assert not out.exists();out.mkdir();results=[]
for k,c in enumerate(dp['candidates']):
 d=out/f'candidate{k:03}';d.mkdir();ks=restore(c['KS_replacement']);wide=restore(c['wide_M_replacement'])
 ksref=m.serial([macros[x]for x in c['KS_word']]);mr=m.serial([macros[x]for x in c['M_word']])
 assert m.flat(ks)==m.flat(ksref)and s.boundary(ks)==s.boundary(wide)==(0,0,False)
 assert m.flat(wide)==oldflat[648:1474]+m.flat(mr)+oldflat[1773:4433]
 whole=m.splice(s,m.splice(s,tree,648,4433,wide),135,486,ks)
 reference=m.splice(s,m.splice(s,tree,1474,1773,mr),135,486,ksref)
 rows=s.sites(whole);rr=s.sites(reference);graph,nchecks=s.graph_arithmetic(rows);rg=s.graph_arithmetic(rr)[0]
 assert graph==s.graph_intervals(rows)==rg==s.graph_intervals(rr)
 assert m.flat(whole)==oldflat[:135]+m.flat(ks)+oldflat[486:1474]+m.flat(mr)+oldflat[1773:]
 d0=len(m.flat(ks))-351;d1=len(m.flat(mr))-299;outside=0
 for i,(eff,targets)in enumerate(oldgraph):
  if 135<=i<486 or 1474<=i<1773:continue
  j=map_old(i,d0,d1);assert graph[j]==[eff,[map_old(t,d0,d1)for t in targets]],(i,j,graph[j],eff,targets)
  outside+=1
 met=s.metrics(whole);assert all(met[x]==c[x]for x in('dag_nodes','maximum_depth','maximum_zero_run'));assert met['maximum_zero_run']<=6 and met['maximum_depth']<=64
 source=s.compact(rows);(d/'sites.json').write_bytes(source)
 rec={'status':'EXACT_MIXED_MODAL_SOURCE_PASS','source_metrics':met,'KS_word':c['KS_word'],'M_word':c['M_word'],'recipes':{w:plan['recipes'][w]for w in(c['KS_word'],c['M_word'])},'AX_output_count':11,'all78_recipe_ASTs_checked':True,'closed_macro_sequence':True,'full_primitive_word_bound':True,'outside_guarded_edges_bound':outside,'two_full_CFG_resolvers':True,'reference_parse_CFG_equal':True,'decoder_successor_checks':nchecks,'initial37_source_paths_unchanged':rows[:37]==oldrows[:37],'source_sha256':m.sha(source),'scope':'Ordinarily calibrated K/S+M source form, not Lean/machine certification. No allocator, startup or runtime execution.'}
 assert rec['initial37_source_paths_unchanged'];(d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec);print(k,met,flush=True)
(P/'verified-v2-result.json').write_text(json.dumps({'status':'MIXED_MODAL_SOURCE_WINNERS_VERIFIED','candidate_count':len(results),'minimum_DAG':min(r['source_metrics']['dag_nodes']for r in results),'results':results,'no_allocator_or_runtime':True},indent=2)+'\n')
