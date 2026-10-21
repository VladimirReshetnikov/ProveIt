"""Owned216-case syntax-only H/PW family. No fourth-field/enumerator claim.
Integer hash-consing prices exact sourceDAGs; no physical allocator is run.
"""
import price_h_pw as B
from functools import lru_cache
from collections import Counter
import itertools,json,time,resource
OUT=B.OUT
resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,256*1024*1024))
ids={};terms=[];size=[];depth=[];lead=[];zerorun=[];bd=[];digest=[]
def intern(t):return term(('L',*t))if B.P.leaf(t)else term(('N',intern(t[0]),intern(t[1])))
def term(r):
 if r in ids:return ids[r]
 i=len(terms);ids[r]=i;terms.append(r)
 if r[0]=='L':
  op,k=r[1:];size.append(1);depth.append(0);lead.append(0);zerorun.append(0);bd.append((1,0,False)if op=='CD'else(k,0,False)if op=='CB'else(0,k,False)if op=='CC'else(0,0,op=='CH'));digest.append(B.H(B.compact(r)))
 else:
  a,b=r[1:];size.append(size[a]+size[b]);depth.append(1+max(depth[a],depth[b]));lead.append(lead[a]+1);zerorun.append(max(zerorun[a],zerorun[b],lead[a]+1));x,y=bd[a],bd[b];bd.append((max(max(x[0]-1,0),y[0]),max(x[1],max(y[1]-1,0)),x[2]or y[2]));digest.append(B.H(B.compact(['N',digest[a],digest[b]])))
 return i
root=intern(B.old);macros={k:intern(t)for k,t in B.macros.items()}
def count(n):
 seen=set();todo=[n]
 for n in todo:
  if n in seen:continue
  seen.add(n)
  if terms[n][0]=='N':todo.extend(terms[n][1:])
 return len(seen)
def combine(xs,kind):
 if len(xs)==1:return xs[0]
 if kind=='right':return term(('N',xs[0],combine(xs[1:],kind)))
 if kind=='left':return term(('N',combine(xs[:-1],kind),xs[-1]))
 k=len(xs)//2;return term(('N',combine(xs[:k],kind),combine(xs[k:],kind)))
def splice(inserted):
 removed=[]
 def walk(n,start):
  end=start+size[n]
  if end<=135 or start>=486:return n
  if 135<=start and end<=486:
   assert bd[n]==(0,0,False);removed.append((start,end));return inserted if start==135 else None
  assert terms[n][0]=='N';a,b=terms[n][1:];left=walk(a,start);right=walk(b,start+size[a]);return right if left is None else left if right is None else term(('N',left,right))
 nr=walk(root,0);assert sum(b-a for a,b in removed)==351;return nr
@lru_cache(None)
def ast(n):return tuple(terms[n][1:])if terms[n][0]=='L'else(ast(terms[n][1]),ast(terms[n][2]))
perms=list(itertools.permutations('abc'));inventory=[]
for hp in perms:
 for pp in perms:
  for order in('H_PW','PW_H'):
   for association in('right','left','balanced'):inventory.append(dict(H_roles=hp,PW_roles=pp,order=order,association=association))
assert len(inventory)==216
B.dump('NO_READER_INVENTORY.json',dict(status='INVENTORY_BEFORE_PRICING',variants=inventory,count=216,cap_seconds=5,memory_limit_mib=256,changed_encoding='AX consumes three Cantor fields, not four; the old U-reader is entirely absent. Finite-command compiler and enumerator equivalence NOT proved.',literal_replacement_interval=[135,486],macro_occurrences=dict(variable_pushes=11,implications=9),inserted_primitive_leaves=529))
started=time.monotonic();results=[];best={};status='COMPLETE'
for index,item in enumerate(inventory):
 if time.monotonic()-started>=5:status='CAP_UNKNOWN';break
 p,q,r=item['H_roles'];h=B.I(B.I(p,q),B.I(B.I(q,r),B.I(p,r)));p,q,r=item['PW_roles'];pw=B.I(B.I(B.I(p,q),p),B.I(r,p));forms=[h,pw]if item['order']=='H_PW'else[pw,h];words=[B.postfix(f)for f in forms]
 assert [B.decode(w)for w in words]==forms
 inserted=combine([macros[x]for word in words for x in word],item['association']);assert size[inserted]==529 and bd[inserted]==(0,0,False)
 nr=splice(inserted);assert size[nr]==4922
 rec=dict(index=index,**item,postfix=words,formula_constructor_dag_nodes=len(B.constructors(h)|B.constructors(pw)),source_dag_nodes=count(nr),primitive_leaves=size[nr],maximum_depth=depth[nr],maximum_zero_run=zerorun[nr],root_merkle_sha256=digest[nr],physical_states='NOT_ALLOCATED',root_id=nr,inserted_id=inserted)
 results.append(rec);key=(rec['source_dag_nodes'],rec['maximum_depth'],rec['maximum_zero_run'])
 for name in('overall',item['association']):
  if name not in best or key<best[name][0]:best[name]=(key,rec)
verified=[]
for rec in {x[1]['index']:x[1]for x in best.values()}.values():
 if time.monotonic()-started>=5:status='CAP_UNKNOWN_VERIFICATION';break
 nr=rec['root_id'];tree=ast(nr);inserted=ast(rec['inserted_id']);ns=B.verify_source(tree,inserted);data=B.compact(ns);stem=f"no_reader_{rec['index']:03d}";(OUT/(stem+'.sites.json')).write_bytes(data);(OUT/(stem+'.ast.json')).write_bytes(B.compact(tree));verified.append(dict(**rec,source_file=stem+'.sites.json',source_sha256=B.H(data),ast_file=stem+'.ast.json',ast_sha256=B.H(B.compact(tree)),outside_cfg_preserved=True,two_cfg_resolvers_agree=True))
report=dict(status=status,attempted=len(results),inventoried=216,source_histogram=dict(Counter(r['source_dag_nodes']for r in results)),formula_constructor_histogram=dict(Counter(r['formula_constructor_dag_nodes']for r in results)),best_by_association={k:v[1]for k,v in best.items()},verified_representatives=verified,seconds=time.monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,scope='Exact syntactic sourceDAG price only. Removing fourth-reader changes command encoding; proof compiler/enumerator bridge not proved. H/PW calculus equivalence separately proved. No physical allocation or state-count claim.',results=results)
B.dump('NO_READER_PRICES.json',report);print(json.dumps({k:v for k,v in report.items()if k not in('results','best_by_association','verified_representatives')},indent=2));print('BEST',[(k,v[1]['index'],v[1]['source_dag_nodes'],v[1]['maximum_depth'])for k,v in best.items()])
