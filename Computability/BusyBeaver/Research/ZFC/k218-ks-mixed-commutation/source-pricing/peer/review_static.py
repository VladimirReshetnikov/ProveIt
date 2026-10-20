"""Own source-data review only; no candidate module import or supplied execution."""
from pathlib import Path
import json,hashlib
from tree_reader import leaf,flat,rows,parse,boundary,cfg,serial
P=Path('/tmp/k218-mixed-modal-dp');O=Path(__file__).parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=json.loads((P/'input.json').read_text());base=[]
for r in plan['nodes']:base.append(tuple(r['leaf'])if'leaf'in r else tuple(base[i]for i in r['children']))
old=parse(json.loads((Path(plan['seed'])/'sites218.json').read_text()));of=flat(old);orr=rows(old);og=cfg(old)
assert old==base[plan['old_node_count']-1]and len(of)==4744
mac={k:base[i]for k,i in plan['macro_ids'].items()};assert all(boundary(t)==(0,0,False)for t in mac.values())
I=lambda a,b:('I',a,b);Q=lambda a,b:('Q',a,b);N=lambda a:I(a,'F')
K=I('a',I('b','a'));S=I(I('a',I('b','c')),I(I('a','b'),I('a','c')));M=I(Q('a',N(N(Q('b','c')))),N(N(Q('b',Q('a','c')))))
def rename(t,p):return(t[0],rename(t[1],p),rename(t[2],p))if isinstance(t,tuple)else dict(zip('abc',p)).get(t,t)
def decode(w):
 st=[]
 for x in w:
  if x in'IQ':b,a=st.pop(),st.pop();st.append((x,a,b))
  else:st.append(x)
 assert len(st)==1;return st[0]
for word,r in plan['recipes'].items():
 if r['kind']=='KS':fs=[rename(t,p)for t,p in zip([K,S],r['permutations'])];expected=[fs[i]for i in r['order']]
 else:expected=[rename(M,r['permutation'])]
 assert [decode(w)for w in r['formula_postfix']]==expected and ''.join(r['formula_postfix'])==word
assert len(plan['recipes'])==78 and len(plan['joint_recipes'])==432
for r in plan['reused_old_closed_subtree_patterns']:
 t=base[r['node']];ref=serial([mac[x]for x in r['word']]);assert flat(t)==flat(ref)and boundary(t)==(0,0,False)and cfg((t,('CH',None)))==cfg((ref,('CH',None)))
assert of[1474:1773]==flat(serial([mac[x]for x in'abcQQbacQQI']))
def restore(x):return base[x]if type(x)==int else(restore(x[0]),restore(x[1]))
allresults=[]
for version in(2,3):
 data=json.loads((P/f'joint-v{version}-result.json').read_text());verified=json.loads((P/f'verified-v{version}-result.json').read_text());assert len(data['candidates'])==16
 for k,c in enumerate(data['candidates']):
  d=P/f'verified-v{version}'/f'candidate{k:03}';r=json.loads((d/'receipt.json').read_text());rr=json.loads((d/'sites.json').read_text());t=parse(rr);graph=cfg(t)
  ks=restore(c['KS_replacement']);wide=restore(c['wide_M_replacement']);kr=serial([mac[x]for x in c['KS_word']]);mr=serial([mac[x]for x in c['M_word']]);kf,mf=flat(kr),flat(mr)
  assert flat(ks)==kf and flat(wide)==of[648:1474]+mf+of[1773:4433] and boundary(ks)==boundary(wide)==(0,0,False)
  assert flat(t)==of[:135]+kf+of[486:1474]+mf+of[1773:]
  assert rr[:37]==orr[:37]and H(d/'sites.json')==r['source_sha256']and r==verified['results'][k]
  delta0,delta1=len(kf)-351,len(mf)-299;seen=set();spans={}
  def visit(u,i=0):
   seen.add(u);j=i+len(flat(u));spans[i,j]=u
   if not leaf(u):visit(u[0],i);visit(u[1],i+len(flat(u[0])))
  visit(t)
  assert spans[135,135+len(kf)]==ks and spans[648+delta0,4433+delta0+delta1]==wide
  met={'dag_nodes':len(seen),'leaf_occurrences':len(rr),'maximum_depth':max(len(p)for p,_,_ in rr),'maximum_zero_run':max(len(v)for p,_,_ in rr for v in p.split('1'))}
  assert met==r['source_metrics']and all(met[x]==c[x]for x in('dag_nodes','maximum_depth','maximum_zero_run'))and met['maximum_zero_run']<=6
  def shift(i):
   assert not(135<i<486 or 1474<i<1773)
   return i+(delta0 if i>=486 else 0)+(delta1 if i>=1773 else 0)
  checked=set()
  for i,(eff,targets)in enumerate(og):
   if 135<=i<486 or 1474<=i<1773:continue
   j=shift(i);assert graph[j]==[eff,[shift(x)for x in targets]];checked.add(j)
  assert len(checked)==4094==r['outside_guarded_edges_bound']
  # Independent exhaustive partition of the new full graph: every unchanged
  # instruction plus every instruction of both closed serial-macro intervals.
  for lo,node in [(135,kr),(1474+delta0,mr)]:
   local=cfg((node,('CH',None)))
   for i,(eff,targets)in enumerate(local[:-1]):
    assert graph[lo+i]==[eff,[lo+x for x in targets]];assert lo+i not in checked;checked.add(lo+i)
  assert len(checked)==len(rr)
  allresults.append({'version':version,'candidate':k,'metrics':met,'source_sha256':r['source_sha256'],'all_new_CFG_rows_checked':len(checked),'unchanged_rows':4094})
original=json.loads((P/'joint-result.json').read_text());assert original['zero_compatible']==0
qs=Path('/tmp/k218-qs-span-dp/dp.cpp').read_text();mcpp=(P/'dp.cpp').read_text();assert qs.replace('if(best.size()>16)best.pop_back();','/* Keep all per-word beam candidates for joint two-hole scoring. */')==mcpp
v2=(P/'check_candidates_v2.py').read_text();v3=(P/'check_candidates_v3.py').read_text();assert v2.replace('joint-v2-result','joint-v3-result').replace("'verified-v2'","'verified-v3'").replace('verified-v2-result','verified-v3-result')==v3
report={'status':'INDEPENDENT_MIXED_MODAL_DP_SOURCE_REVIEW_PASS','reviewer':'review_upstream_reflection','scope':'Full delta/source read and own literal/formula/whole-CFG census of32 saved sources; no DP, allocator, compiler or runtime invocation.','findings':[],'formula_recipes':78,'joint_recipe_pairs':432,'candidate_results':allresults,'initial_invalid_splice_preserved':True,'limits':['Minimum209 is found under bounded beams2/4 inner and3 outer, not optimum or lower bound.','No allocation or runtime acceptance claimed.','The original input record was written before calibration; its pending-calibration scope is historical, superseded by the separate ordinary reviewed proof.','Macro all-natural numeric semantics are inherited; this review checks exact composition, formula outputs and complete CFG, not a fresh proof of every macro arithmetic contract.'],'inputs':[{'path':str(P/n),'sha256':H(P/n)}for n in ['README.md','prepare.py','prepare_v3.py','dp.cpp','joint.py','joint_v2.py','joint_v3.py','check_candidates_v2.py','check_candidates_v3.py','input.json','input-v3.json','dp-result.json','dp-v3-result.json','joint-result.json','joint-v2-result.json','joint-v3-result.json','verified-v2-result.json','verified-v3-result.json','freeze.json']],'own_reader':[{'path':str(p),'sha256':H(p)}for p in[Path(__file__),O/'tree_reader.py']]}
(O/'review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':report['status'],'candidates':len(allresults),'minimumDAG':min(x['metrics']['dag_nodes']for x in allresults),'receipt_sha256':H(O/'review.json')}))
