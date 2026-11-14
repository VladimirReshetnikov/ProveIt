from pathlib import Path
import json,sys,collections,itertools,time
sys.path.insert(0,str(Path(__file__).parent))
import compiler as c, symbolic_runtime as sr
ROOT=Path(__file__).parent
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
ns={k:tup(v) for k,v in json.loads((ROOT/'nodes.json').read_text()).items()}
c.raw_nodes=lambda:ns
grammar=c.read_grammar(ROOT/'pa194.grammar.json')
sites,ins,contracts=c.source(grammar)
def succ(pc,m):
 row=ins[pc]
 if row[0]=='inc':return [(row[2],m|(1<<row[1]))]
 if row[0]=='jump':return [(row[1],m)]
 if row[0]=='halt':return []
 _,r,z,n=row;bit=1<<r
 return [(n,m&~bit),(n,m)] if m&bit else [(z,m)]
seen={(25,1)};todo=list(seen)
for pc,m in todo:
 for x in succ(pc,m):
  if x not in seen:seen.add(x);todo.append(x)
positive=[0]*len(ins)
for pc,m in seen:positive[pc]|=m
print('positivity_pairs',len(seen),flush=True)
raw={}
for l in (ROOT/'unfolded202.native.tm').read_text().splitlines():
 if not l.strip():continue
 q,b,w,d,n=l.split();raw[int(q),int(b)]=(int(w),d=='R',int(n))
folds=json.loads((ROOT/'folds.json').read_text());aliases={a:b for a,b,acts in folds};acts={b:act for a,b,act in folds}
rows={(q,b):(w,bool(d),aliases.get(n,n)) for(q,b),a in raw.items() if q not in aliases for w,d,n in [acts[q][b] if q in acts else a]}
print('table',len(rows)//2,'validate',c.validate(rows,contracts),flush=True)
active_zero=set();orig_oracle=sr.oracle
def oracle(q,br,x):
 out=orig_oracle(q,br,x)
 if out is not None:return out
 if q==0 and x[1]=='mark' and x[2] in active_zero:return(97,sr.PLAIN,False)
sr.oracle=oracle
c.oracle=oracle
# Identify the rows immediately following the path prefix for break1 sites.
breaks=[i for i,(p,op,arg) in enumerate(sites) if op=='breakTo' and arg==1]
print('breaks',[(i,[r for r in range(9) if not positive[i]>>r&1]) for i in breaks],flush=True)
# Run affected sites and record each literal row used. The patches are tried at original jump rows0L40.
used=collections.defaultdict(set)
for idx in breaks:
 ct=next(x for x in contracts if x[0]==idx)
 st=ct[2]
 for k in range(5000):
  if k and sr.matches(st,ct[3]):break
  q,onl,l,r=st
  if not onl and r and r[0][0]=='b':used[q,r[0][1]].add(idx)
  out=sr.sstep(rows,None,st)
  assert out is not None,(idx,st)
  st,m=out
 else:raise Exception(idx)
keys=[key for key,pcs in used.items() if rows[key] in ((0,False,40),(0,False,302))]
print('jump_rows',[(key,sorted(used[key])) for key in keys],flush=True)
options={}
for key in keys:
 pcs=used[key];out=[]
 possible=[(w,d,n) for w in (0,1) for d in (False,True) for n in sorted({q for q,b in rows})]
 for act in possible:
  mod=dict(rows);mod[key]=act;ok=True
  for pc in pcs:
   active_zero={c.PHYSICAL[r] for r in range(9) if not positive[pc]>>r&1}
   ct=next(x for x in contracts if x[0]==pc)
   if c.run(mod,ct,3000) is None:ok=False;break
  if ok:out.append(act)
 options[str(key)]=out
 print('options',key,'sites',sorted(pcs),'acts',out,flush=True)
(ROOT/'jump_options.json').write_text(json.dumps({'positive':positive,'pairs':len(seen),'options':options,'rows':[[q,b,w,int(d),n]for(q,b),(w,d,n) in sorted(rows.items())]},indent=2))
