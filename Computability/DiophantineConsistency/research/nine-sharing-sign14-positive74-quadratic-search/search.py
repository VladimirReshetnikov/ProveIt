import re,json,random,itertools,hashlib,sys
from functools import lru_cache
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
from pathlib import Path
SCRIPT_PATH=Path(__file__).resolve()
S=Path('Computability/DiophantineConsistency/research/nine-sharing-sign14-positive74-structural-search/search_canonical.py');src=S.read_text();assert hashlib.sha256(S.read_bytes()).hexdigest()=='5f683e6e9b3cc46450e4edcc566610862730b8e58ab574a4e12496dc67b71bb6','search engine pin';env={'__file__':str(S.resolve())};exec(compile(src[:src.index('assert len(graph(root)) == 74')],str(S),'exec'),env);globals().update(env)
P=1000000007
if P % 4 != 3 or any(P % d == 0 for d in range(2,int(P**0.5)+1)):raise RuntimeError('prime check')
assert len(N)==74 and len(graph(root))==74
rng=random.Random(0x46BE);leaves={}
for op,a,b in N:
 for x in (a,b):
  if isinstance(x,str):leaves[x]=None
for i in range(-4,9):leaves[f'lit:{i}']=None
for k in leaves:
 leaves[k]=(int(k[4:])%P,)*3 if k.startswith('lit:') else tuple(rng.randrange(1,P) for _ in range(3))
vals=dict(leaves)
def ev(op,a,b):return tuple(((x+y) if op=='add' else (x-y) if op=='sub' else (x*y))%P for x,y in zip(a,b))
# The first 74 source nodes are topological.
for i,(op,a,b) in enumerate(N[:74]):vals[i]=ev(op,vals[a],vals[b])
items=list(vals);pool={}
for i,a in enumerate(items):
 for b in items[i:]:
  for op in ('add','mul'):pool.setdefault(ev(op,vals[a],vals[b]),[]).append((op,a,b))
 for b in items:pool.setdefault(ev('sub',vals[a],vals[b]),[]).append(('sub',a,b))
inv={c:tuple(pow(x,-1,P) for x in vals[c]) for c in items if all(vals[c])};sample_zeros=[str(c) for c in items if c not in inv and c!='lit:0'];assert not sample_zeros,sample_zeros
roots=[out[i] for i in (23,41,48,61,64)];squares=[out[65+i] for i in range(5)]
forms=[(a,b,c) for a in range(1,4) for c in range(1,4) for b in range(-4,5) if 4*a*c>b*b]
found=[];stats={'pair_form_tests':0,'matching_0':0,'matching_1':0,'matching_2':0,'candidates_counted':0};one={}
for x,v in vals.items():one.setdefault(v,[]).append(x)
@lru_cache(None)
def add_trees(items):
 if len(items)==1:return (items[0],)
 variants=set();n=len(items)
 for mask in range(1,1<<n):
  if not mask&1 or mask==(1<<n)-1:continue
  left=tuple(items[i] for i in range(n) if mask>>i&1);right=tuple(items[i] for i in range(n) if not mask>>i&1)
  for x in add_trees(tuple(sorted(left))):
   for y in add_trees(tuple(sorted(right))):variants.add(node('add',x,y))
 return tuple(sorted(variants))
def check(q,pair,form,recipe):
 others=[squares[i] for i in range(5) if i not in pair]
 for z in add_trees(tuple(sorted([q]+others))):
  count=len(graph(z));stats['candidates_counted']+=1
  if count<74:
   result={'pair':pair,'form':form,'recipe':recipe,'live':count,'root':z};found.append(result);print('HIT',json.dumps(result),flush=True)
assert len(add_trees(('check:0','check:1','check:2','check:3')))==15,'add-tree coverage'
for i,j in itertools.combinations(range(5),2):
 r,s=vals[roots[i]],vals[roots[j]]
 for a,b,c in forms:
  target=tuple((a*x*x+b*x*y+c*y*y)%P for x,y in zip(r,s));assert all(target),'sample zero';stats['pair_form_tests']+=1
  for q in one.get(target,[]):stats['matching_0']+=1;check(q,(i,j),(a,b,c),['existing',str(q)])
  for op,x,y in pool.get(target,[]):stats['matching_1']+=1;check(node(op,x,y),(i,j),(a,b,c),[op,str(x),str(y)])
  for d in items:
   cv=vals[d];qs=[('add',tuple((t-v)%P for t,v in zip(target,cv))),('sub',tuple((t+v)%P for t,v in zip(target,cv))),('rsub',tuple((v-t)%P for t,v in zip(target,cv)))]
   if d in inv:qs.append(('mul',tuple(t*v%P for t,v in zip(target,inv[d]))))
   for op,need in qs:
    for o,x,y in pool.get(need,[]):
     stats['matching_2']+=1;tmp=node(o,x,y);q=node('sub',d,tmp) if op=='rsub' else node(op,tmp,d);check(q,(i,j),(a,b,c),[op,[o,str(x),str(y)],str(d)])
  # Also allow the second gate to use the freshly created first gate twice.
  twice=tuple(t*pow(2,-1,P)%P for t in target)
  needs=[('double',twice)]
  roots2=[pow(t,(P+1)//4,P) for t in target]
  if all(z*z%P==t for z,t in zip(roots2,target)):
   needs += [('square',tuple(z*sgn%P for z,sgn in zip(roots2,signs))) for signs in itertools.product((1,-1),repeat=3)]
  for tag,need in needs:
   for o,x,y in pool.get(need,[]):
    stats['matching_2']+=1;tmp=node(o,x,y);q=node('add' if tag=='double' else 'mul',tmp,tmp);check(q,(i,j),(a,b,c),[tag,[o,str(x),str(y)]])
# Positive control: replace residual r with (r+1)-1, then recover the original pair.
r=roots[0];control_r=node('sub',node('add',r,'lit:1'),'lit:1');control_sq=node('mul',control_r,control_r);control_sum=node('add',control_sq,squares[1])
for square in squares[2:]:control_sum=node('add',control_sum,square)
assert len(graph(control_sum))==76 and len(graph(root))==74
assert out[70] in one[tuple((x*x+y*y)%P for x,y in zip(vals[roots[0]],vals[roots[1]]))]
print('SUMMARY',json.dumps({'forms':len(forms),'stats':stats,'hits':len(found),'positive_control_live_before':len(graph(control_sum)),'positive_control_live_after':len(graph(root)),'prime':P,'samples':3,'seed':0x46BE,'script_sha256':hashlib.sha256(SCRIPT_PATH.read_bytes()).hexdigest()},sort_keys=True),flush=True)
if found:Path('/tmp/positive74-quadratic-candidates.json').write_text(json.dumps({'found':found,'nodes':N}))
