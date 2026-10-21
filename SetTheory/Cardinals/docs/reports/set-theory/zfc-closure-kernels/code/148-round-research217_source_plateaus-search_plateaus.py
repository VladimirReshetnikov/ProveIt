"""Owned closed-factor source-DAG search. No producer code is executed.
This file emits exact source transformations, NEVER physical machines.
"""
from pathlib import Path
from collections import defaultdict, Counter
from functools import lru_cache
import sys,json,hashlib,time
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_encoding'));import price_sources as P
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
B=ROOT/'latest218_baseline/candidate-k218'
compact=lambda x:(json.dumps(x,separators=(',',':'))+'\n').encode()
H=lambda x:hashlib.sha256(x).hexdigest()
def dump(name,x):(OUT/name).write_text(json.dumps(x,indent=2)+'\n')
ss=json.load(open(B/'sites218.json'));tree=P.tree(ss);T=A.R.table(B/'k218.native.tm')
groups,paths,gates=P.allocation(T,tree)
nodeqs=defaultdict(set)
for q,ns in groups.items():
 for n in ns:nodeqs[n].add(q)
ids={};terms=[];sizes=[];bounds=[];digests=[]
def intern(n):
 if P.leaf(n):r=('L',*n)
 else:r=('N',intern(n[0]),intern(n[1]))
 return term(r)
def term(r):
 if r in ids:return ids[r]
 i=len(terms);ids[r]=i;terms.append(r)
 if r[0]=='L':
  op,k=r[1:];sizes.append(1);bounds.append((1,0,False)if op=='CD'else(k,0,False)if op=='CB'else(0,k,False)if op=='CC'else(0,0,op=='CH'))
  digests.append(H(compact(r)))
 else:
  a,b=r[1:];sizes.append(sizes[a]+sizes[b]);x,y=bounds[a],bounds[b];bounds.append((max(max(x[0]-1,0),y[0]),max(x[1],max(y[1]-1,0)),x[2]or y[2]));digests.append(H(compact(['N',digests[a],digests[b]])))
 return i
root=intern(tree);baseqs={intern(n):sorted(qs)for n,qs in nodeqs.items()}
known_helpers={85,188,189,190,156,176}
reserved={n for n,qs in baseqs.items()if set(qs)&{157,200}}
@lru_cache(None)
def nodes(n):
 if terms[n][0]=='L':return frozenset([n])
 return frozenset([n])|nodes(terms[n][1])|nodes(terms[n][2])
base=nodes(root)
@lru_cache(None)
def ast(n):
 r=terms[n];return tuple(r[1:])if r[0]=='L'else(ast(r[1]),ast(r[2]))
def rotations(n):
 r=terms[n]
 if r[0]=='L':return
 l,r=r[1:]
 if terms[l][0]=='N':
  a,b=terms[l][1:];c=r
  if all(bounds[x]==(0,0,False)for x in(a,b,c)):yield 'right',(a,b,c),term(('N',a,term(('N',b,c))))
 if terms[r][0]=='N':
  a=l;b,c=terms[r][1:]
  if all(bounds[x]==(0,0,False)for x in(a,b,c)):yield 'left',(a,b,c),term(('N',term(('N',a,b)),c))
def change(r,n,m):
 @lru_cache(None)
 def walk(x):
  if x==n:return m
  z=terms[x]
  if z[0]=='L':return x
  return term(('N',walk(z[1]),walk(z[2])))
 return walk(r)
def inventory(r):
 current=nodes(r);rows=[]
 for n in sorted(current):
  if n in reserved:continue
  for direction,factors,new in rotations(n):
   child=terms[new][1:];qs=baseqs.get(n,[])
   rows.append(dict(node_id=n,node_merkle_sha256=digests[n],replacement_id=new,replacement_merkle_sha256=digests[new],states=qs,direction=direction,leaves=sizes[n],factor_leaves=[sizes[x]for x in factors],factor_boundaries=[bounds[x]for x in factors],existing_children=sum(x in current for x in child),existing_inner_node=(child[1]if direction=='right'else child[0])in current,known_mixed_role_states=sorted(set(qs)&known_helpers|{q for q in qs if len(groups[q])>1}),root_has_multiple_source_roles=any(len(groups[q])>1 for q in qs)))
 return rows
reference=A.continuation_cfg(tree)
assert reference==A.address_cfg(ss)
reference_word=[x[1:]for x in ss]
def verify(r):
 t=ast(r);s=A.flatten(t)
 assert len(s)==4744 and [x[1:]for x in s]==reference_word
 assert A.continuation_cfg(t)==reference and A.address_cfg(s)==reference
 return s

def save(r,chain):
 s=verify(r);data=compact(s);ah=H(compact(ast(r)));sh=H(data);name='source_'+sh[:16]
 (OUT/(name+'.sites.json')).write_bytes(data);(OUT/(name+'.ast.json')).write_bytes(compact(ast(r)))
 receipt=dict(source_file=name+'.sites.json',ast_file=name+'.ast.json',source_sha256=sh,ast_sha256=ah,root_merkle_sha256=digests[r],dag_nodes=len(nodes(r)),internal_subtrees=sum(terms[x][0]=='N'for x in nodes(r)),primitive_leaves=4744,exact_ordinal_cfg=True,rotations=chain,physical_states='NOT_CONSTRUCTED_OR_PRICED',physical_warning='Source identity only. Shared decoder, arithmetic, bootstrap, and selector roles require independent physical allocation and proofs. Rows188/1,189/1,190/0/1,156/1,176/1 are selector helpers even where decoder labels appear pure.')
 dump(name+'.receipt.json',receipt);return receipt

def main():
 start=time.monotonic();cap=60;rows=inventory(root)
 assert len(base)==205 and len(rows)==187
 dump('INVENTORY.json',dict(baseline_source_sha256=H((B/'sites218.json').read_bytes()),baseline_native_sha256=H((B/'k218.native.tm').read_bytes()),baseline_nodes=205,baseline_root_merkle_sha256=digests[root],excluded_baseline_states=[157,200],first_steps=len(rows),known_selector_helper_rows=[[188,1],[189,1],[190,0],[190,1],[156,1],[176,1]],first_step_inventory=rows,cap=dict(seconds=cap,second_step_seed_roots=24,second_steps_per_root=220,second_steps_total=5280)))
 print('INVENTORY_RECORDED',len(rows),flush=True)
 first=[];saved={};roots={root};parentrows={}
 for i,row in enumerate(rows):
  nr=change(root,row['node_id'],row['replacement_id']);counts=nodes(nr);rec={**row,'candidate_id':i,'root_id':nr,'dag_nodes':len(counts),'removed_nodes':len(base-counts),'added_nodes':len(counts-base),'distinct_root':nr not in roots}
  roots.add(nr);first.append(rec);parentrows[nr]=rec
  if len(counts)<=205 and nr not in saved:saved[nr]=save(nr,[row])
 dump('FIRST_STEP_RESULTS.json',dict(status='COMPLETE',histogram=dict(Counter(x['dag_nodes']for x in first)),results=first,exact_source_candidates=list(saved.values()),elapsed_seconds=time.monotonic()-start))
 print('FIRST_STEP',dict(Counter(x['dag_nodes']for x in first)),'saved',len(saved),'seconds',round(time.monotonic()-start,3),flush=True)
 shortlist=sorted([r for r in first if r['dag_nodes']<=205],key=lambda x:(x['dag_nodes'],-x['existing_children'],x['known_mixed_role_states']!=[],x['node_merkle_sha256'],x['direction']))
 unique=[];seen={root}
 for r in shortlist:
  if r['root_id']not in seen:unique.append(r);seen.add(r['root_id'])
  if len(unique)==24:break
 plans=[dict(first_step=r,second_step_inventory=inventory(r['root_id'])[:220])for r in unique]
 dump('SECOND_STEP_INVENTORY.json',dict(seeds=len(plans),rotation_tests=sum(len(p['second_step_inventory'])for p in plans),plans=plans))
 second=[];status='COMPLETE';newlow=[]
 for plan in plans:
  p=plan['first_step']
  for row in plan['second_step_inventory']:
   if time.monotonic()-start>=cap:status='CAP_UNKNOWN';break
   nr=change(p['root_id'],row['node_id'],row['replacement_id']);ns=nodes(nr);rec=dict(first_step=p['candidate_id'],second_step=row,root_id=nr,dag_nodes=len(ns),distinct_root=nr not in roots)
   roots.add(nr);second.append(rec)
   if len(ns)<=205 and nr not in saved and nr!=root:
    saved[nr]=save(nr,[{k:v for k,v in p.items()if k not in('root_id','candidate_id','dag_nodes','removed_nodes','added_nodes','distinct_root')},row]);newlow.append(saved[nr]);print('SECOND_USEFUL',len(ns),saved[nr]['source_sha256'],flush=True)
  if status!='COMPLETE':break
 dump('SECOND_STEP_RESULTS.json',dict(status=status,histogram=dict(Counter(r['dag_nodes']for r in second)),tests=len(second),results=second,new_exact_source_candidates=newlow,elapsed_seconds=time.monotonic()-start))
 dump('SUMMARY.json',dict(status=status,baseline_dag_nodes=205,first_step_tests=len(first),first_histogram=dict(Counter(x['dag_nodes']for x in first)),neutral_or_better_first=len([x for x in first if x['dag_nodes']<=205]),second_step_seeds=len(plans),second_tests=len(second),second_histogram=dict(Counter(r['dag_nodes']for r in second)),source_candidates=list(saved.values()),elapsed_seconds=time.monotonic()-start,scope='Exact closed-factor reassociation sourceDAG census, excluding baseline source roles at physical states157 and200. No physical machine produced. Negative result only within enumerated one-step and bounded plateau family.'))
 print('DONE',status,'first',len(first),'second',len(second),'best',min(len(nodes(r))for r in saved)if saved else None,'saved',len(saved),'seconds',round(time.monotonic()-start,3),flush=True)
if __name__=='__main__':main()
