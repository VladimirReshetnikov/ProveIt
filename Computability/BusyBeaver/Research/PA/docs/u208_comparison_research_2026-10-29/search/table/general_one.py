import sys,json,itertools,time,hashlib,pathlib
sys.path.insert(0,'u209_reduction_20261029/table_search')
from core import read,contexts
OUT=pathlib.Path('u208_reduction_20261029/table_search')
def test(t,old,q,r,ctx,b,ed,limit=40):
 if ctx.get(0,b)!=b:return True
 init=dict(ctx);init[0]=b;w,d,z=t[old,b];z=r if z==q else z
 stack=[(r,0,dict(init),init,0)]
 while stack:
  s,h,tape,origin,n=stack.pop();dest=dict(origin);dest[0]=w
  if n and s==z and h==d and tape==dest:continue
  if n>=limit or s==254 or abs(h)>8:return False
  if h not in tape:
   for bit in (0,1):
    tt=dict(tape);tt[h]=bit;oo=dict(origin);oo[h]=bit;stack.append((s,h,tt,oo,n))
   continue
  bb=tape[h]
  if ed is None and (s,bb)==(r,1-b):return False # other row can change; require independent currentbranch
  ww,dd,rr=ed[1] if ed and (s,bb)==(r,ed[0]) else t[s,bb];rr=r if rr==q else rr
  tt=dict(tape);tt[h]=ww;stack.append((rr,h+dd,tt,origin,n+1))
 return True
results=[]
for pp in sys.argv[1:] or ['4564c487','89145587']:
 p=pathlib.Path('u209_reduction_20261029/table_search')/('candidate_'+pp)/'native.tm';t=read(p);states=sorted({q for q,b in t});cs={q:contexts(t,q,8) for q in states if q};hits=[];pairs=0;trials=0;start=time.time()
 for q in cs:
  for r in cs:
   if q==r:continue
   for b in (0,1):
    # unchanged branch need not match literally, unlike prior search
    if t[q,1-b]==t[r,1-b]:continue
    if not all(test(t,old,q,r,c,1-b,None) for old in (q,r) for c in cs[old]):continue
    pairs+=1
    for w,d,z in itertools.product((0,1),(-1,1),states):
     if z==q:continue
     ed=(b,(w,d,z));trials+=1
     if not all(test(t,old,q,r,c,b,ed) for old in (q,r) for c in cs[old]):continue
     if not all(test(t,old,q,r,c,1-b,ed) for old in (q,r) for c in cs[old]):continue
     hit=[q,r,b,w,d,z];hits.append(hit);print('HIT',pp,hit,flush=True)
  if q%20==0:print('progress',pp,q,pairs,trials,time.time()-start,flush=True)
 result={'parent':pp,'pairs':pairs,'trials':trials,'hits':hits,'seconds':time.time()-start};results.append(result);(OUT/'general_one_results.json').write_text(json.dumps(results,indent=2));print(result,flush=True)
