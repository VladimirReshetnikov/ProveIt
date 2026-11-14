from pathlib import Path
import sys,json,ctypes,importlib.util,time,collections
BASE=Path(__file__).resolve().parent;OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/'vendor'))
from rotation_search import read,encode
spec=importlib.util.spec_from_file_location('finite_fast_wrapper',BASE/'vendor/finite_fast.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);lib=mod.lib
t=read(OUT/'rejected207.native.tm');rows=json.loads((OUT/'sites.json').read_text())
hits=[json.loads(l) for l in (OUT/'single_patch_hits.jsonl').read_text().splitlines()]
first=[x for x in hits if x['result']==71]
alltext='\n'.join(f'{p} {op} {arg or 0}' for p,op,arg in rows).encode()
singletext='\n'.join(f'{p} {op} {arg or 0}' for p,op,arg in [rows[70]]).encode()
buf=(ctypes.c_int*6000)()
for (q,b),(w,d,z) in t.items():buf[6*q+3*b]=w;buf[6*q+3*b+1]=d;buf[6*q+3*b+2]=z
def setrow(k,v):
 for i,x in enumerate(v):buf[6*k[0]+3*k[1]+i]=x
def test(src,limit=0,variants=1):
 s=ctypes.c_longlong(0);return lib.check(buf,src,limit,variants,ctypes.byref(s)),s.value
def trace(tab,p):
 tape=collections.defaultdict(int);tape[-1]=1;tape[56]=1
 for i,b in enumerate(p):tape[i]=int(b)
 for i in range(10):tape[58+2*i]=1
 q=84;h=0;used=[];last=[]
 for n in range(10000):
  if n and q==84:return list(dict.fromkeys(used)),{'steps':n,'head':h,'last':last[-20:]}
  if q==254:return list(dict.fromkeys(used)),{'steps':n,'halt':True,'last':last[-20:]}
  b=tape[h];w,d,z=tab[q,b];used.append((q,b));last.append([q,h,b,w,d,z]);tape[h]=w;q=z;h+=d
 return list(dict.fromkeys(used)),{'steps':10000,'head':h,'last':last[-20:]}
targets=sorted({q for q,b in t}|{254});stats=collections.Counter();log=(OUT/'two_patch_hits.jsonl').open('w');start=time.time()
for number,hit in enumerate(first):
 k1=tuple(hit['row']);v1=tuple(hit['new']);setrow(k1,v1);tt=dict(t);tt[k1]=v1
 keys,traceinfo=trace(tt,rows[70][0]);keys=[k for k in keys if k!=k1]
 print('firstpatch',number,k1,v1,'secondrows',len(keys),'trace',traceinfo,flush=True)
 for k in keys:
  for z in targets:
   for d in (-1,1):
    for w in (0,1):
     tr=(w,d,z)
     if tr==t[k]:continue
     setrow(k,tr);stats['tested']+=1
     err,steps=test(singletext,1)
     if err:continue
     stats['failure70_pass']+=1
     err,steps=test(alltext)
     result={'first':hit,'second_row':k,'second_new':tr,'result':err,'steps':steps};log.write(json.dumps(result)+'\n');log.flush()
     if not err:
      stats['all_pass']+=1;print('CANDIDATE',result,flush=True)
      good=dict(tt);good[k]=tr
      (OUT/f'two_candidate_{number}_{k[0]}_{k[1]}_{w}_{d}_{z}.tm').write_text(encode(good))
      err3,steps3=test(alltext,variants=3);print('variants3',err3,steps3,flush=True)
      if not err3:(OUT/'two_candidate_pass.json').write_text(json.dumps(result));sys.exit(0)
  setrow(k,t[k])
 setrow(k1,t[k1]);print('finished',number,dict(stats),'seconds',time.time()-start,flush=True)
(OUT/'two_patch_summary.json').write_text(json.dumps({'stats':dict(stats),'seconds':time.time()-start,'first_patches':first},indent=2))
