#!/usr/bin/env python3
from pathlib import Path
import sys,itertools,json,hashlib,random
if not __debug__:raise RuntimeError('Assertions required')
OUT=Path(__file__).resolve().parent;A=OUT.parent/'architectures';sys.path.insert(0,str(A))
import tag_edge as E
import native_edge_step as N

def parse(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));assert(q,b)not in t;t[q,b]=w,d,n
 return t
et,ee,er,ej,en=E.compile_edge();assert er==16 and parse(A/'tag_edge_16.tm')==et
mark=en.index('mark_child');dead=en.index('return_right');fold=lambda q:mark if q==dead else q
keep=[q for q in range(er)if q!=dead];ren={q:i for i,q in enumerate(keep)}|{er:er-1};f=lambda q:ren[fold(q)]
small={(f(q),b):(w,d,f(n))for(q,b),(w,d,n)in et.items()if q!=dead}
w,d,n=et[dead,0];small[f(mark),0]=w,d,f(n)
excluded={(mark,0),(dead,1)}
for(q,b),(w,d,n)in et.items():
 if(q,b)not in excluded:assert small[f(q),b]==(w,d,f(n))
assert len(small)==30
counts={'tag_cases':0,'native_edge_cases':0};seen=set()
for tag,left,right,branch,bit,origin in itertools.product(range(4),range(6),range(6),range(2),range(2),(-5,11)):
 tape={origin-1,origin-7};p=origin;starts=[]
 for v in(tag,left,right):starts.append(p);tape.update(range(p,p+v+1));p+=v+2
 tape|={p,p+3};tape.remove(origin);initial=set(tape);q=ee[branch,bit];h=origin
 while q not in(er,ej):
  b=int(h in tape);assert(q,b)not in excluded;seen.add(f(q));w,d,n=et[q,b]
  assert small[f(q),b]==(w,d,f(n))
  if w:tape.add(h)
  else:tape.discard(h)
  h+=1 if d=='R'else-1;q=n
 good=(tag>>branch)&1==bit;assert(q==er)==good
 want=initial|{origin}
 if good:want.discard(starts[branch+1]);assert h==starts[branch+1]
 assert tape==want;counts['tag_cases']+=1
# Export the independently verified 15-state quotient for the worker to inspect.
lines=[f'#! start {f(ee[0,0])}']+[f'{q} {b} {w} {d} {n}'for(q,b),(w,d,n)in sorted(small.items())]
smallpath=OUT/'tag_edge_15_verified_fold.tm';smallpath.write_text('\n'.join(lines)+'\n')
nt,ne,nr,nj,nn=N.compile_step();assert nr==67 and parse(A/'native_edge_step_67.tm')==nt
rng=random.Random(6715);maxsteps=0
for m in range(1,8):
 for trial in range(20):
  records=[(rng.randrange(4),rng.randrange(m),rng.randrange(m))for _ in range(m)]
  selected=rng.randrange(m)
  for branch,bit,origin in itertools.product(range(2),range(2),(-13,7)):
   child=records[selected][1+branch];gap=child+2;c=origin;anchor=c+gap+1;tape={c,anchor};p=anchor+2;starts=[]
   for record in records:
    starts.append(p)
    for v in record:tape.update(range(p,p+v+1));p+=v+2
   tape.remove(starts[selected]);tape|={c-2,c-6,p,p+5};initial=set(tape);q=ne[branch,bit];h=starts[selected];k=0
   while q not in(nr,nj):
    w,d,q=nt[q,int(h in tape)]
    if w:tape.add(h)
    else:tape.discard(h)
    h+=1 if d=='R'else-1;k+=1;assert k<1000000
   good=(records[selected][0]>>branch)&1==bit;assert(q==nr)==good
   want=initial|{starts[selected]}
   if good:want.discard(starts[child]);assert h==starts[child]
   assert tape==want;counts['native_edge_cases']+=1;maxsteps=max(maxsteps,k)
result={'status':'PASS_VALID_FRAME_CONTRACTS','counts':counts,'tag_original_states':16,'tag_fold_states':15,'tag_fold_rows':30,'tag_fold_excluded_original_pairs':2,
 'fold_entries':{str(k):f(v)for k,v in ee.items()},'fold_reject':f(ej),'fold_return':15,'native_edge_states':67,'maximum_edge_steps':maxsteps,
 'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in[A/'tag_edge.py',A/'tag_edge_16.tm',A/'native_edge_step.py',A/'native_edge_step_67.tm',smallpath]}}
(OUT/'tag_native_edge_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
