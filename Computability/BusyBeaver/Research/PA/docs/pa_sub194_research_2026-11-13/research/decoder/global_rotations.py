"""Search exact source-preserving rotations of fixed pure decoder readers.
All files emitted by this experiment are outside the pinned checkout.
"""
import sys, pathlib, json, collections, itertools, time
PK=pathlib.Path(__file__).resolve().parents[2]/'reference/haz'
sys.path.insert(0,str(PK/'vendor'))
import compiler as c, symbolic_runtime as s
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99
c.MACROS[((inc,inc),(inc,inc))]=190
NODES=c.raw_nodes(); ORIGINAL=c.raw_nodes
G=c.read_grammar(PK/'inputs/pa194.grammar.json')
raw,idx,shape=c.build(G)
# Native state hints from decoding the immutable source tree.
old,_=c.machine(); hint={}; todo=[('node172',84)]
while todo:
 name,q=todo.pop()
 if not isinstance(name,str) or name in hint: continue
 hint[name]=q
 for b,ch in enumerate(NODES[name]):
  w,d,n=old[q,b]
  if w==b and d:todo.append((ch,n))
qnames=collections.defaultdict(list)
for n,q in hint.items():qnames[q].append(n)
# Build actual source tree with reference leaves and frozen AX grammar.
base_sites,base_ins,base_contracts=c.source(G)
# Fixed q must be a pure reader and have an unambiguous logical meaning.
pure={q:(raw[q,0][2],raw[q,1][2]) for q,b in raw if b==0 and raw[q,0][:2]==(0,True) and raw[q,1][:2]==(1,True)}
provider=collections.defaultdict(list)
for q,pr in pure.items(): provider[pr].append(q)
# Fold assignments are synthesized below; no external fold list is used.

# Fold only disjoint candidates; universal symbolic validation determines whether
# use of the old context providers remains valid after changing the tree.
def foldall(rows, folds):
 aliases={a:b for a,b,acts in folds}; actions={b:acts for a,b,acts in folds}
 def alias(q):
  seen=set()
  while q in aliases:
   if q in seen:raise ValueError('alias cycle')
   seen.add(q);q=aliases[q]
  return q
 return {(q,b): (a[0],bool(a[1]),alias(a[2])) for (q,b),v in rows.items() if q not in aliases for a in [actions.get(q,[rows[q,0],rows[q,1]])[b]]}

def reachable(rows):
 live={74};todo=[74]
 for q in todo:
  for b in (0,1):
   n=rows[q,b][2]
   if n!=254 and n not in live:live.add(n);todo.append(n)
 return {(q,b):a for (q,b),a in rows.items() if q in live}

out=[];count=0;st=time.time()
for name,q in sorted(hint.items()):
 if q>=1300 or q not in pure or len(qnames[q])!=1:continue
 for side in (0,1):
  child=NODES[name][side]
  if not isinstance(child,str) or child not in hint:continue
  cq=hint[child]
  if cq not in pure or len(qnames[cq])!=1 or pure[q][side]!=cq:continue
  # Perform a single definition-level rotation, preserving all leaf order.
  if side==0:
   a,b=NODES[child];r=NODES[name][1]
   pair=(pure[cq][1],pure[q][1]);dirs=(pure[cq][0],4000)
   newdef=(a,(b,r))
  else:
   a=NODES[name][0];b,d=NODES[child]
   pair=(pure[q][0],pure[cq][0]);dirs=(4000,pure[cq][1])
   newdef=((a,b),d)
  ns=dict(NODES);ns[name]=newdef;c.raw_nodes=lambda:ns
  try: sites,ins,contracts=c.source(G)
  except (ValueError,AssertionError,KeyError):continue
  count+=1
  if ins!=base_ins:continue
  if max(map(lambda z:len(z[0]),sites))>48:continue
  rec={'node':name,'state':q,'side':side,'source_identity':True}
  for pq in (provider.get(pair,[]) or [4000]):
   if pq in (q,cq):continue
   rows=dict(raw);rows[q,0]=(0,True,pq if side else dirs[0]);rows[q,1]=(1,True,dirs[1] if side else pq)
   if pq==4000:
    rows[pq,0]=(0,True,pair[0]);rows[pq,1]=(1,True,pair[1])
   rows=reachable(rows)
   # Check best available one-bit-history matching over all non-box readers.
   candidates={a:None for a,b in rows if b==0 and a not in c.BOXSTATES|{74,84}}
   ops=c.opportunities_fast(rows,candidates)
   pairs=c.max_matching(ops); best=len(rows)//2-len(pairs)
   rec.update(raw_states=len(rows)//2,fold_count=len(pairs),nominal_states=best,provider=pq)
   print(json.dumps(rec),flush=True)
   if best<=194:
    opdict={(a,b):o for a,b,o in ops}
    folds=[[a,b,[o[0] for o in opdict[a,b]]] for a,b in pairs]
    folded=foldall(rows,folds)
    valid=c.validate(folded,contracts)
    rec['validation']=valid
    if valid['ok']:
     text=''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n' for(q,b),(w,d,n)in sorted(folded.items()))
     path=pathlib.Path(__file__).parent/f'rotation_{name}_{side}_{best}.tm';path.write_text(text)
     path.with_suffix('.json').write_text(json.dumps({'record':rec,'folds':folds,'sites':sites,'instructions':ins},indent=2))
     print('VERIFIED',path,flush=True)
   out.append(dict(rec))
c.raw_nodes=ORIGINAL
pathlib.Path(__file__).with_suffix('.json').write_text(json.dumps({'attempted':count,'exact_source_rotations':out,'elapsed':time.time()-st},indent=2))
print('END',count,len(out),time.time()-st,flush=True)
