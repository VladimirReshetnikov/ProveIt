"""Exhaust all 6^7 exact selector renamings, without huge expanded DAG caches.
The mathematical scope is seven independently and bijectively renamed rows.
No physical machine claim follows from a source DAG minimum.
"""
import json,itertools,time,collections,sys,hashlib
from pathlib import Path
from functools import lru_cache
import axiom_model
from paths import OUT
ns=vars(axiom_model)
e,s,sp,old,regions,choices,perms=[ns[x]for x in('e','s','sp','old','regions','choices','perms')]
start=time.monotonic();edits={}
for i,row in enumerate(choices):
 for p in row[0]:edits[p]=(i,tuple(r[p]for r in row))
fixed=set();unchanged=set();selector_nodes=set();templates={};template_nodes=[];sizes=[];deps=[]
def templ(n,p=''):
 if p in edits:
  i,variants=edits[p];key=('choice',i,variants)
  assert all(sp.size(e.expand(k))==sp.size(n)for k in variants)
  for k in variants:selector_nodes.update(ns['nodeset'](k));fixed.update(ns['nodeset'](k))
 elif not any(q.startswith(p)for q in edits):
  k=e.intern(n);unchanged.update(ns['nodeset'](k));fixed.update(ns['nodeset'](k));key=('fixed',k)
 else:
  a=templ(n[0],p+'0');b=templ(n[1],p+'1');key=('pair',a,b)
 if key not in templates:
  k=len(template_nodes);templates[key]=k;template_nodes.append(key);sizes.append(sp.size(n));deps.append(frozenset()if key[0]=='fixed'else frozenset({key[1]})if key[0]=='choice'else deps[key[1]]|deps[key[2]])
 return templates[key]
root=templ(old)
# Every selector macro's interior already occurs outside the editable rows.
# Therefore adding all selector variants to the constant set is exact for
# every assignment, not merely an overestimate of the union of variants.
assert selector_nodes<=unchanged
by_size=collections.defaultdict(list)
for i,key in enumerate(template_nodes):
 if key[0]=='pair':by_size[sizes[i]].append(i)
fixed_sizes=collections.defaultdict(set)
for k in fixed:fixed_sizes[sp.size(e.expand(k))].add(k)
unique_count=0;ambiguous=[]
for size,ts in by_size.items():
 if len(ts)==1 and size not in fixed_sizes:unique_count+=1
 else:ambiguous.extend(ts)
print('templates',len(template_nodes),'fixed',len(fixed),'unique_count',unique_count,'ambiguous',len(ambiguous),'maxdeps',max(map(lambda t:len(deps[t]),ambiguous)),flush=True)
@lru_cache(None)
def instantiate(t,combo):
 key=template_nodes[t]
 if key[0]=='fixed':return key[1]
 if key[0]=='choice':return key[2][combo[key[1]]]
 return e.pair(instantiate(key[1],combo),instantiate(key[2],combo))
# At most two/three rows interact inside any ambiguous-sized subtree.
# Store each template's possible ID using only those coordinates.
lookup=[]
for t in ambiguous:
 coordinates=tuple(sorted(deps[t]));vals=[]
 for sub in itertools.product(range(6),repeat=len(coordinates)):
  combo=[0]*7
  for j,v in zip(coordinates,sub):combo[j]=v
  vals.append(instantiate(t,tuple(combo)))
 lookup.append((coordinates,vals))
all_ids=fixed|set(k for _,vs in lookup for k in vs);position={k:i for i,k in enumerate(sorted(all_ids))};basebits=sum(1<<position[k]for k in fixed)
lookbits=[(c,[1<<position[k]for k in vs])for c,vs in lookup]
print('lookup_nodes',len(all_ids),'hashcons_nodes',len(e.nodes),'cache',instantiate.cache_info(),flush=True)
# Cross-check the decomposition on every one-coordinate mutation and 300
# deterministic random combinations against the independently retained model.
import random
rng=random.Random(97410);checks=[(0,)*7]
for i in range(7):
 for v in range(6):
  c=[0]*7;c[i]=v;checks.append(tuple(c))
checks += [tuple(rng.randrange(6)for _ in range(7))for _ in range(300)]
def cost(combo):
 bits=basebits
 for cc,vs in lookbits:
  index=0
  for c in cc:index=6*index+combo[c]
  bits |= vs[index]
 return unique_count+bits.bit_count()
for c in checks:assert cost(c)==len(ns['nodeset'](ns['make'](c))),(c,cost(c),ns['score'](c))
best=999;ties=[];hist=collections.Counter();total=0
for combo in itertools.product(range(6),repeat=7):
 val=cost(combo);hist[val]+=1;total+=1
 if val<best:best=val;ties=[combo];print('BEST',best,combo,'at',total,flush=True)
 elif val==best:ties.append(combo)
 if total%50000==0:print('progress',total,'seconds',time.monotonic()-start,flush=True)
report={'scope':'Independent selector permutations within seven complete unrestricted logical schema rows; source tree association and all other primitives held fixed','combinations':total,'minimum_dag_nodes':best,'minimizers':ties,'permutations':perms,'regions':regions,'histogram':dict(sorted(hist.items())),'decomposition':{'constant_nodes':len(fixed),'uncontested_dynamic_nodes':unique_count,'contested_dynamic_templates':len(ambiguous),'max_template_dependencies':max(map(lambda t:len(deps[t]),ambiguous)),'finite_lookup_nodes':len(all_ids),'independent_full_tree_crosschecks':len(checks)},'seconds':time.monotonic()-start}
out=OUT/'axiom_permutations_exhaustive';out.mkdir(exist_ok=True)
for combo in ties:
 node=ns['make'](combo);assert len(ns['nodeset'](node))==best
 (out/('perm'+''.join(map(str,combo))+'.json')).write_text(json.dumps(s.sites(e.expand(node)),separators=(',',':'))+'\n')
(out/'census.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
