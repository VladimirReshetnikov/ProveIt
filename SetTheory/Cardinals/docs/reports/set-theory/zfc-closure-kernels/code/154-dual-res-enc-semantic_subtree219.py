#!/usr/bin/env python3
"""Bounded semantic matching and exact disjoint-register commutations.

Finite function signatures discover candidates only. A semantic replacement
needs an unbounded proof, and compiled decoder counts need runtime proof.
"""
import json,itertools,time,collections
from pathlib import Path
from functools import cache
import inverse_mp as q
import recompile219 as compiler
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
ROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(ROWS)
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
F=json.loads((q.W/'source_facts219.json').read_text())['facts']
OUT=q.W/'semantic_subtree219';OUT.mkdir(exist_ok=True)
@cache
def footprint(n):
 if s.leaf(n):return frozenset([n[1]])if n[0]in('CI','CD')else frozenset()
 return footprint(n[0])|footprint(n[1])
@cache
def nodes(n):return frozenset([n])if s.leaf(n)else nodes(n[0])|nodes(n[1])|{n}
allnodes=nodes(OLD)
closed=[n for n in allnodes if not s.leaf(n)and s.boundary(n)==(0,0,False)]
closed.sort(key=lambda n:(len(q.x.flat(n)),repr(n)))
entries=collections.defaultdict(list)
def walk(n,lo=0):
 entries[n].append(lo)
 if not s.leaf(n):walk(n[0],lo);walk(n[1],lo+len(q.x.flat(n[0])))
walk(OLD)
@cache
def replace(n,a,bb):
 if n==a:return bb
 if s.leaf(n):return n
 return replace(n[0],a,bb),replace(n[1],a,bb)
records=[];seen=set();start=time.time()
def consider(a,bb,why,extra=None):
 if a==bb or(a,bb)in seen:return
 seen.add((a,bb));tr=replace(OLD,a,bb);m=s.metrics(tr)
 if m['dag_nodes']>206:return
 row={'kind':why,'old_subtree':a,'new_subtree':bb,'metrics':m,'entry_ordinals':entries[a],**(extra or{})}
 dd=OUT/f'hit{len(records)}';dd.mkdir(exist_ok=True);rr=s.sites(tr);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
 (dd/'sites.json').write_bytes(s.compact(rr))
 try:
  U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);row['compiler']=meta;(dd/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:
  row['error']=repr(exc)
  (dd/'candidate.tm').unlink(missing_ok=True)
 (dd/'receipt.json').write_text(json.dumps(row,indent=2)+'\n');records.append(row)
 print('HIT',why,m,row.get('compiler'),row.get('error'),flush=True)
# Closed disjoint-footprint blocks commute as partial functions on all naturals.
commutations=0
for n in allnodes:
 if s.leaf(n):continue
 a,bb=n
 if s.boundary(a)==s.boundary(bb)==(0,0,False)and not footprint(a)&footprint(bb):
  commutations+=1;consider(n,(bb,a),'UNBOUNDED_DISJOINT_REGISTERS')
 # Same-shaped adjacent block exchange inside a right or left comb.
 if not s.leaf(bb):
  c,d=bb
  if s.boundary(a)==s.boundary(c)==s.boundary(d)==(0,0,False)and not footprint(a)&footprint(c):
   commutations+=1;consider(n,(c,(a,d)),'UNBOUNDED_DISJOINT_REGISTERS')
 if not s.leaf(a):
  c,d=a
  if s.boundary(c)==s.boundary(d)==s.boundary(bb)==(0,0,False)and not footprint(d)&footprint(bb):
   commutations+=1;consider(n,((c,bb),d),'UNBOUNDED_DISJOINT_REGISTERS')
print('COMMUTATIONS',commutations,'hits',len(records),flush=True)
# Only small closed subtrees; all register combinations remain universally
# quantified in the intended contract, despite the bounded discovery tests.
small=[n for n in closed if len(q.x.flat(n))<=50]
zeros={n:sum((1<<r)for r in range(9)if all(F[i][r]==1 for i in entries[n]))for n in small}
@cache
def graph(n):
 gg=s.graph_intervals(s.sites((n,('CH',None))))
 return [(e[0],e[1]if len(e)>1 else 0,ts)for e,ts in gg]
@cache
def evaluate(n,r):
 R=list(r);g=graph(n);pc=0
 for _ in range(20000):
  op,a,ts=g[pc]
  if op=='halt':return tuple(R)
  if op=='increment':R[a]+=1;pc=ts[0]
  elif op=='decrement':
   bit=R[a]>0
   if bit:R[a]-=1
   pc=ts[bit]
  else:pc=ts[0]
 return None
census=[]
for mask in sorted(set(zeros.values())):
 free=[r for r in range(9)if not(mask>>r&1)];inputs=[(0,)*9]
 for r in free:
  for v in[1,2,3,8]:
   t=[0]*9;t[r]=v;inputs.append(tuple(t))
 for a,bb in itertools.combinations(free,2):
  t=[0]*9;t[a]=t[bb]=1;inputs.append(tuple(t))
 for v in[1,2]:inputs.append(tuple(0 if mask>>r&1 else v for r in range(9)))
 groups=collections.defaultdict(list);completed=0
 for n in small:
  signature=[]
  for rr in inputs:
   out=evaluate(n,rr)
   if out is None:break
   signature.append(out)
  else:groups[tuple(signature)].append(n);completed+=1
 matches=0
 for group in groups.values():
  if len(group)<2:continue
  for a in group:
   if zeros[a]!=mask:continue
   for bb in group:
    if a==bb or a in nodes(bb):continue
    matches+=1;consider(a,bb,'FINITE_SIGNATURE_ONLY',{'known_zero_registers':[r for r in range(9)if mask>>r&1],'input_cases':len(inputs),'step_cap':20000})
 census.append({'zero_mask':mask,'inputs':len(inputs),'completed_subtrees':completed,'finite_matches':matches})
 print('MASK',mask,'inputs',len(inputs),'matches',matches,'seconds',time.time()-start,flush=True)
report={'closed_nodes':len(closed),'small_closed_nodes':len(small),'commutations':commutations,'finite_census':census,'records':records,'seconds':time.time()-start}
(OUT/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
