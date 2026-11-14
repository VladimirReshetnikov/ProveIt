from pathlib import Path
import sys,json,time,collections,ctypes,importlib.util
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/'vendor'))
from rotation_search import read,encode,candidates,rotate,L,SRC
_spec=importlib.util.spec_from_file_location('finite_fast_wrapper',BASE/'vendor/finite_fast.py')
_fast=importlib.util.module_from_spec(_spec);_spec.loader.exec_module(_fast)
check,lib=_fast.check,_fast.lib
OUT=Path(__file__).resolve().parent
OUT.mkdir(exist_ok=True)
t=read(SRC/'machine/u208.native.tm')
rows=json.loads((SRC/'machine/sites.json').read_text());root=L.tree(rows)
for key in [(155,85,0),(52,154,0)]:
 cs=[c for c in candidates(t,root) if c[:3]==key]
 assert len(cs)==1,(key,[c[:3] for c in candidates(t,root)])
 t,root=rotate(t,root,cs[0])
assert (t[85,0],t[85,1])==(t[154,0],t[154,1])
t={k:(w,d,85 if z==154 else z) for k,(w,d,z) in t.items() if k[0]!=154}
rows=L.sites(root)
(OUT/'rejected207.native.tm').write_text(encode(t))
(OUT/'sites.json').write_text(json.dumps(rows))
result=check(t,rows,variants=1)
print('baseline',result,flush=True)
idx=result[0]-1 if result[0]<1000000 else result[0]-1000000
print('firstfailure',idx,rows[idx],flush=True)
protected=set();errors=[]
for p,op,arg in rows:
 q=84;h=0;tape={-1:1,**{i:int(b) for i,b in enumerate(p)}}
 for tick in range(2000):
  if h==len(p):break
  if h not in tape:errors.append((p,q,h,'outside'));break
  b=tape[h];w,d,z=t[q,b]
  if w!=b:errors.append((p,q,h,'write'));break
  protected.add((q,b));h+=d;q=z
 else:errors.append((p,q,h,'timeout'))
print('prefixrows',len(protected),'errors',len(errors),'runtimeonly',len(set(t)-protected),flush=True)
(OUT/'prefix_rows.json').write_text(json.dumps({'protected':sorted(protected),'errors':errors}))
# A write before the nominal leaf boundary is a valid fused primitive entry.
# The prefix set is advisory; full primitive replay is the preservation filter.

buf=(ctypes.c_int*6000)()
for (q,b),(w,d,z) in t.items():buf[6*q+3*b]=w;buf[6*q+3*b+1]=d;buf[6*q+3*b+2]=z
one='\n'.join(f'{p} {op} {arg or 0}' for p,op,arg in [rows[idx]]).encode()
alltext='\n'.join(f'{p} {op} {arg or 0}' for p,op,arg in rows).encode()
def test(src,limit=0,variants=1):
 steps=ctypes.c_longlong(0)
 return lib.check(buf,src,limit,variants,ctypes.byref(steps)),steps.value
targets=sorted({q for q,b in t}|{254})
priority=[(152,0),(159,1),(118,0),(155,0),(85,0),(98,0),(12,0)]
keys=[k for k in priority if k in t]+[k for k in sorted(t) if k not in priority and k not in protected]
stats=collections.Counter();best=[];start=time.time()
log=(OUT/'single_patch_hits.jsonl').open('w')
for k in keys:
 off=6*k[0]+3*k[1];old=t[k]
 for z in targets:
  for d in (-1,1):
   for w in (0,1):
    tr=(w,d,z)
    if tr==old:continue
    for j,v in enumerate(tr):buf[off+j]=v
    stats['tested']+=1
    err,steps=test(one,1)
    if err:continue
    stats['firstcase_pass']+=1
    err,steps=test(alltext)
    hit={'row':k,'old':old,'new':tr,'result':err,'steps':steps}
    log.write(json.dumps(hit)+'\n');log.flush()
    if not err:
     stats['all_pass']+=1
     print('CANDIDATE',hit,flush=True)
     tt=dict(t);tt[k]=tr
     (OUT/f'candidate_{k[0]}_{k[1]}_{w}_{d}_{z}.tm').write_text(encode(tt))
     err3,steps3=test(alltext,variants=3)
     print('variants3',err3,steps3,flush=True)
     if not err3:(OUT/'candidate_pass.json').write_text(json.dumps(hit))
    if len(best)<20 or (err if err<1000000 else err-1000000)>min(x[0] for x in best):
     best.append((err if err<1000000 else err-1000000,hit));best.sort(key=lambda x:x[0],reverse=True);best=best[:20]
 for j,v in enumerate(old):buf[off+j]=v
 print('finishedrow',k,dict(stats),'elapsed',round(time.time()-start,2),flush=True)
log.close()
(OUT/'single_patch_summary.json').write_text(json.dumps({'stats':dict(stats),'seconds':time.time()-start,'best':best},indent=2))
