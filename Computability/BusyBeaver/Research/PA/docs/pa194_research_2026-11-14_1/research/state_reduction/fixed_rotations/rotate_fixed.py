import sys,json,itertools,collections,ast,re,copy,time
from pathlib import Path
W=Path(__file__).parent
sys.path.insert(0,str(W/'base'))
import compiler as c
import symbolic_runtime as sr
P=W/'base'
R={}
for l in (P/'unfolded201.native.tm').read_text().splitlines():
 q,b,w,d,n=l.split();R[int(q),int(b)]=int(w),d=='R',int(n)
raw=W/'Program.lean'
nodes={}
for line in raw.read_text().splitlines():
 m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
 if not m:continue
 toks=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2]);ch=[]
 for op,arg,n in toks:ch.append(n if n else ('leaf',op,int(arg) if arg else None))
 nodes[m[1]]=tuple(ch)
grammar=c.read_grammar(W/'grammar.json')
nodes['x67']=grammar
inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
c.machine=lambda:(R,[]);c.raw_nodes=lambda:nodes
sites,ins,contracts=c.source(grammar)
assert len(sites)==3673
mapping=collections.defaultdict(set);leafmap=collections.defaultdict(set);seen=set()
def prop(q,t):
 if (q,t) in seen:return
 seen.add((q,t))
 if isinstance(t,str):mapping[q].add(t);return prop(q,nodes[t])
 if len(t)==3:leafmap[q].add(t);return
 for b,child in enumerate(t):
  w,d,n=R[q,b]
  if w==b and d and (n,0)in R:prop(n,child)
prop(84,'node172')
for t,q in c.MACROS.items():prop(q,t)
print('mapping',len(mapping),dict(mapping))
incoming=collections.defaultdict(list)
for k,(w,d,n)in R.items():incoming[n].append(k)
folds=json.loads((P/'pa194.folds.json').read_text())
foldcontrols={q for a,b,acts in folds for q in(a,b)}
tries=[]
for q,names in mapping.items():
 if q>=1300:continue
 for direction in [0,1]:
  # right association if child0 is internal, left association if child1
  a0,a1=R[q,0],R[q,1]
  if a0[:2]!=(0,True) or a1[:2]!=(1,True):continue
  r=(a0 if direction==0 else a1)[2]
  if r==q or incoming[r]!=[(q,direction)] or r not in mapping:continue
  r0,r1=R[r,0],R[r,1]
  if r0[:2]!=(0,True) or r1[:2]!=(1,True):continue
  if direction==1:
   na={0:(0,True,r),1:(1,True,r1[2])};nb={0:(0,True,a0[2]),1:(1,True,r0[2])}
  else:
   na={0:(0,True,r0[2]),1:(1,True,r)};nb={0:(0,True,r1[2]),1:(1,True,a1[2])}
  for victim,rows in [(q,na),(r,nb)]:
   for keeper in {s for s,b in R}-{q,r}:
    if all(R[keeper,b]==rows[b]for b in[0,1]):
     tries.append((q,r,direction,victim,keeper,sorted(names)))
print('potential one-state savings',tries)
(W/'fixed_rotation_candidates.json').write_text(json.dumps(tries,indent=2))
import build194 as bld
original_nodes=copy.deepcopy(nodes)
records=[]
for q,names in mapping.items():
 if q>=1300 or len(names)!=1:continue
 name=next(iter(names));orig_t=nodes[name]
 for direction in [0,1]:
  a0,a1=R[q,0],R[q,1]
  if a0[:2]!=(0,True) or a1[:2]!=(1,True):continue
  r=(a0 if direction==0 else a1)[2]
  if r==q or incoming[r]!=[(q,direction)] or r not in mapping:continue
  r0,r1=R[r,0],R[r,1]
  if r0[:2]!=(0,True) or r1[:2]!=(1,True):continue
  child=orig_t[direction]
  if isinstance(child,str):child=nodes[child]
  if len(child)!=2:continue
  if direction==1:
   new_t=((orig_t[0],child[0]),child[1]);na={0:(0,True,r),1:(1,True,r1[2])};nb={0:(0,True,a0[2]),1:(1,True,r0[2])}
  else:
   new_t=(child[0],(child[1],orig_t[1]));na={0:(0,True,r0[2]),1:(1,True,r)};nb={0:(0,True,r1[2]),1:(1,True,a1[2])}
  nodes=copy.deepcopy(original_nodes);nodes[name]=new_t
  try:news,newi,newc=c.source(grammar)
  except Exception as ex:records.append({'q':q,'r':r,'direction':direction,'source':'invalid'});continue
  rec={'q':q,'r':r,'name':name,'direction':direction,'source_equal':newi==ins,'modified_sites':sum(a!=b for a,b in zip(sites,news))}
  records.append(rec)
  if newi!=ins:continue
  RR=dict(R)
  for bit in[0,1]:RR[q,bit]=na[bit];RR[r,bit]=nb[bit]
  folded,aliases=bld.apply_folds(RR,folds)
  try:bld.check_local_folds(RR,folded,aliases,folds)
  except Exception:rec['old_folds_valid']=False;continue
  rec['old_folds_valid']=True
  sh={z:None for z,bit in folded if z not in c.BOXSTATES and z!=84}
  opportunities=c.opportunities_fast(folded,sh)
  survivors=[]
  for aa,bb,acts in opportunities:
   # exact predecessor context guard, then full simultaneous local trace
   incs={s:set()for s in[aa,bb]}
   for (s,bit),(w,d,n)in folded.items():
    if n in incs:incs[n].add((w,d))
   if incs[aa]!={(0,True)}or incs[bb]!={(1,True)}:continue
   for ac in itertools.product(*acts):
    f=[(aa,bb,ac)];out,al=bld.apply_folds(folded,f)
    try:local=bld.check_local_folds(folded,out,al,f)
    except Exception:continue
    valid=c.validate(out,newc)
    print('NEW FOLD',q,r,name,direction,aa,bb,ac,valid,flush=True)
    survivor={'pair':[aa,bb],'acts':ac,'validation':valid};survivors.append(survivor)
    if valid['ok']:
     folder=W/f'rotation193_{q}_{r}_{direction}_{aa}_{bb}';folder.mkdir(exist_ok=True)
     (folder/'machine.native.tm').write_text(bld.table_text(out));(folder/'nodes.json').write_text(json.dumps(nodes));(folder/'sites.json').write_text(json.dumps(news));(folder/'instructions.json').write_text(json.dumps(newi));(folder/'local.json').write_text(json.dumps(local));(folder/'receipt.json').write_text(json.dumps(rec))
  rec['extra_folds']=survivors
print('records',json.dumps(records,indent=2));(W/'fixed_rotation_results.json').write_text(json.dumps(records,indent=2))
