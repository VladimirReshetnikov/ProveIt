"""Own literal reader; no import or invocation of candidate programs."""
from pathlib import Path
from functools import cache
import json,hashlib
P=Path('/tmp/k218-qs-span-dp');out=Path(__file__).parent
plan=json.loads((P/'input.json').read_text());dp=json.loads((P/'dp-result.json').read_text());verified=json.loads((P/'verified-result.json').read_text())
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
I=lambda a,b:('I',a,b);Q=lambda a,b:('Q',a,b);N=lambda a:I(a,'F')
forms=[I('a',I('b','a')),I(I('a',I('b','c')),I(I('a','b'),I('a','c'))),I(N(N(Q('a','b'))),Q('a','b'))]
def perm(t,d):return (t[0],perm(t[1],d),perm(t[2],d)) if isinstance(t,tuple) else d.get(t,t)
def post(t):return post(t[1])+post(t[2])+t[0] if isinstance(t,tuple) else t
def decode(w):
 s=[]
 for x in w:
  if x in 'IQ':b,a=s.pop(),s.pop();s.append((x,a,b))
  else:s.append(x)
 assert len(s)==1;return s[0]
for w,r in plan['recipes'].items():
 fs=[perm(f,dict(zip('abc',p))) for f,p in zip(forms,r['permutations'])]
 expected=[fs[i] for i in r['order']]
 assert [decode(x) for x in r['formula_postfix']]==expected
 assert ''.join(map(post,expected))==w
assert len(plan['recipes'])==1296
base=[]
for row in plan['nodes']:base.append(tuple(row['leaf']) if 'leaf'in row else tuple(base[i] for i in row['children']))
leaf=lambda t:isinstance(t[0],str)
@cache
def flat(t):return (t,) if leaf(t) else flat(t[0])+flat(t[1])
def serial(ts):
 ans=ts[-1]
 for t in reversed(ts[:-1]):ans=(t,ans)
 return ans
@cache
def boundary(t):
 if leaf(t):
  op,a=t;return (1,0,False) if op=='CD' else (a,0,False) if op=='CB' else (0,a,False) if op=='CC' else (0,0,op=='CH')
 a,b=boundary(t[0]),boundary(t[1]);return max(a[0]-1,0,b[0]),max(a[1],b[1]-1,0),a[2] or b[2]
def rows(t,p=''):
 if leaf(t):return [[p,*t]]
 return rows(t[0],p+'0')+rows(t[1],p+'1')
def parse(rr):
 lookup={p:(op,a)for p,op,a in rr}
 def go(p):return lookup[p] if p in lookup else (go(p+'0'),go(p+'1'))
 t=go('');assert rows(t)==rr;return t
# Independent recursive subtree exits, using only ordinal spans and ancestor edges.
def cfg(t):
 rr=rows(t);ids={p:i for i,(p,_,_)in enumerate(rr)};spans={}
 def spans_at(p):
  if p in ids:v=(ids[p],ids[p]+1)
  else:
   l,r=spans_at(p+'0'),spans_at(p+'1');assert l[1]==r[0];v=(l[0],r[1])
  spans[p]=v;return v
 spans_at('')
 def dest(p,bit,k):
  ancestors=[p[:i] for i,b in enumerate(p) if b==bit]
  if len(ancestors)<k:return 0
  lo,hi=spans[ancestors[-k]];return lo if bit=='1' else hi%len(rr)
 gg=[]
 for k,(p,op,a)in enumerate(rr):
  aft=(k+1)%len(rr)
  gg.append([['increment',a],[aft]] if op=='CI' else [['decrement',a],[dest(p,'0',1),aft]] if op=='CD' else [['identity'],[dest(p,'0',a)]] if op=='CB' else [['identity'],[dest(p,'1',a)]] if op=='CC' else [['halt'],[]])
 return gg
seed=Path(plan['seed'])/'sites218.json';old=parse(json.loads(seed.read_text()));assert old==base[plan['old_node_count']-1];oldrr=rows(old);og=cfg(old)
mac={k:base[i]for k,i in plan['macro_ids'].items()};assert all(boundary(x)==(0,0,False) for x in mac.values())
for r in plan['reused_old_closed_subtree_patterns']:
 oldnode=base[r['node']];ref=serial([mac[k]for k in r['word']]);assert flat(oldnode)==flat(ref) and boundary(oldnode)==(0,0,False)
 assert cfg((oldnode,('CH',None)))==cfg((ref,('CH',None)))
def restore(x):return base[x]if type(x)==int else(restore(x[0]),restore(x[1]))
results=[]
for k,c in enumerate(dp['candidates']):
 d=P/'verified'/f'candidate{k:03}';r=json.loads((d/'receipt.json').read_text());rr=json.loads((d/'sites.json').read_text());t=parse(rr)
 assert H(d/'sites.json')==r['source_sha256']
 new=restore(c['replacement']);assert flat(new)==tuple(y for x in c['word']for y in flat(mac[x]));assert boundary(new)==(0,0,False)
 expected=new
 for side,sibling in plan['context_bottom_up']:expected=(expected,base[sibling])if side==0 else(base[sibling],expected)
 assert t==expected and flat(t)==flat(old)[:135]+flat(new)+flat(old)[486:]
 seen=set()
 def visit(u):
  if u in seen:return
  seen.add(u)
  if not leaf(u):visit(u[0]);visit(u[1])
 visit(t)
 met={'dag_nodes':len(seen),'leaf_occurrences':len(rr),'maximum_depth':max(len(p)for p,_,_in rr),'maximum_zero_run':max(len(v)for p,_,_in rr for v in p.split('1'))}
 assert met==r['source_metrics'];assert all(met[x]==c[x]for x in ('dag_nodes','maximum_depth','maximum_zero_run'))
 graph=cfg(t);delta=len(rr)-len(oldrr)
 def shift(i):
  assert i<=135 or i>=486
  return i if i<=135 else i+delta
 for i,(eff,targets)in enumerate(og):
  if 135<=i<486:continue
  assert graph[shift(i)]==[eff,[shift(j)for j in targets]]
 refnew=serial([mac[x]for x in c['word']]);ref=refnew
 for side,sibling in plan['context_bottom_up']:ref=(ref,base[sibling])if side==0 else(base[sibling],ref)
 assert cfg(t)==cfg(ref)
 assert verified['results'][k]==r
 results.append({'candidate':k,'metrics':met,'source_sha256':H(d/'sites.json'),'formula_outputs_match':True,'independent_whole_CFG_and_outside_edges_match':True})
allocation=json.loads((P/'global-allocations/result.json').read_text())
assert len(results)==16 and len(allocation['results'])==4 and all(r['status']=='ALLOCATION_REJECTED'for r in allocation['results'])
receipt={'status':'INDEPENDENT_SOURCE_DP_REVIEW_PASS','reviewer':'review_upstream_reflection','scope':'Full source read plus own literal/AST/whole-CFG reconstruction of all16 retained candidates; no DP/allocator/runtime rerun.','findings':[],'source_files':[{ 'path':str(P/n),'sha256':H(P/n)}for n in ['prepare.py','dp.cpp','check_candidates.py','global_allocations.py','global_allocator_v2.py']],'record_files':[{ 'path':str(P/n),'sha256':H(P/n)}for n in ['input.json','input.txt','dp-result.json','verified-result.json','global-allocations/result.json']],'exact_formula_recipes_checked':1296,'old_closed_reuse_patterns_checked':len(plan['reused_old_closed_subtree_patterns']),'candidate_results':results,'DP_limits':{'beam_per_leading_zero_run':2,'zero_run_limit':6,'processed_intervals':dp['processed'],'reported_join_combinations':dp['join_combinations']},'limitations':['All intervals/recipe words completed within beam2; best208 is a found result, not an exhaustive grammar or machine lower bound.','Hash-consed subtree score and local beam dominance can discard later globally useful shared alternatives.','All four existing global allocation attempts fail decoder-prefix binding; no candidate table/runtime/startup acceptance.','Exact macro numeric contracts are inherited from pinned source utilities and prior accepted modules; this review checks source composition rather than re-proving their arithmetic semantics.'],'reviewer_source':{'path':str(Path(__file__)),'sha256':H(Path(__file__))}}
(out/'review.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':receipt['status'],'source_candidates':len(results),'recipes':1296,'minimum_dag':min(x['metrics']['dag_nodes']for x in results),'receipt_sha256':H(out/'review.json')}))
