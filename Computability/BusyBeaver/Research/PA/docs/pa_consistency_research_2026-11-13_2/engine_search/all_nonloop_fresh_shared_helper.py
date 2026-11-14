"""Two contextual merges paid for by one fresh 2-row dispatch state."""
import symbolic_core as c
from collections import defaultdict,Counter
from pathlib import Path
import itertools,json,time
OUT=Path(__file__).resolve().parent
raw,labels=c.machine();inv={v:i for i,v in enumerate(labels)}
T={(inv[q],b):(w,1 if d else -1,inv[n])for(q,b),(w,d,n)in raw.items()}
data=json.loads((OUT/'all_nonloop_contexts.json').read_text());R=data['radius']
ctx={int(q):ws for q,ws in data['contexts'].items()}
tag={q:{(w>>(R-1))&1 for w,m in ws}for q,ws in ctx.items()}
# tags computed from full symbolic contracts + finite bootstrap, must be checked again for final candidate.
bytag=[[q for q in ctx if q!=75 and tag[q]=={b}]for b in(0,1)]
rowtargets={}
for b in(0,1):
 out=defaultdict(list)
 for q in range(196):
  w,d,z=T[q,b]
  out[w,d,z].append(q)
 rowtargets[b]=out
helpers=defaultdict(list)
folds=[]
for p,q in itertools.product(*bytag):
 for b in(0,1):
  if T[p,1-b]!=T[q,1-b]:continue
  tp,tq=T[p,b],T[q,b]
  if tp==tq:continue
  folds.append((p,q,b))
  for a0,a1 in itertools.product(rowtargets[b][tp],rowtargets[b][tq]):
   if {a0,a1}&{p,q}:continue
   helpers[a0,a1].append((p,q,b))
print('tag_sizes',list(map(len,bytag)),'folds',folds,'helperkeys',len(helpers),flush=True)
sol=[];cnt=Counter();cs=c.contracts();start=time.monotonic()
for helper,fs in helpers.items():
 if len(fs)<2:continue
 for combo in itertools.combinations(fs,2):
  p,q,b=combo[0];r,s,d=combo[1]
  if len({p,q,r,s})<4 or set(helper)&{p,q,r,s}:continue
  cnt['combinations']+=1
  # Dense q,s dropped; p,r survive. Helper is new sparse raw9999.
  proj={labels[q]:labels[p],labels[s]:labels[r]}
  image=lambda z:proj.get(z,z)
  rows={(x,v):(w,di,image(n))for(x,v),(w,di,n)in raw.items()if x not in proj}
  rows[labels[p],b]=(b,False,9999);rows[labels[r],d]=(d,False,9999)
  rows[9999,0]=(0,True,labels[helper[0]]);rows[9999,1]=(1,True,labels[helper[1]])
  result=c.validate(rows,cs)
  if result['ok']:
   item=dict(helper=helper,folds=combo,verification=result)
   print('SUCCESS',item,flush=True);sol.append(item)
   (OUT/f'nonloop-fresh-helper-{len(sol)}.native.tm').write_text(''.join(f'{x} {v} {w} {"R" if di else "L"} {n}\n'for(x,v),(w,di,n)in sorted(rows.items())))
  else:
   cnt['failed']+=1
   if cnt['failed']<10:print('failed',helper,combo,result,flush=True)
print('RESULT',dict(cnt),'solutions',sol,'seconds',time.monotonic()-start,flush=True)
(OUT/'all_nonloop_fresh_shared_helper_result.json').write_text(json.dumps({'counts':dict(cnt),'folds':folds,'solutions':sol,'seconds':time.monotonic()-start},indent=2)+'\n')
