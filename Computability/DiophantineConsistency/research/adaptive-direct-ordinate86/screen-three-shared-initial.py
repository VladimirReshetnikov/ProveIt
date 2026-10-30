import json,random,itertools,hashlib
from pathlib import Path
p=2305843009213693951;r=random.Random(80281234);candidate=Path(__file__).resolve().parent/'candidate.json';raw=candidate.read_bytes();
if hashlib.sha256(raw).hexdigest()!='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f':raise RuntimeError('candidate hash mismatch')
j=json.loads(raw);rows=j['source'];base=j['witnesses']+j['fixed_numerals'];vals={n:tuple(r.randrange(2,p-1) for _ in range(3)) for n in base};vals.update({str(i):(i,i,i) for i in [0,1,2,3,4]});args=list(vals)
def op(o,a,b):
 if o=='+':return tuple((x+y)%p for x,y in zip(a,b))
 if o=='-':return tuple((x-y)%p for x,y in zip(a,b))
 return tuple(x*y%p for x,y in zip(a,b))
def count(rs):
 d={z[0]:z for z in rs};todo=['P13'];live=set()
 while todo:
  x=todo.pop()
  if x in live:continue
  live.add(x)
  if x in d:todo.extend(str(a) for a in d[x][2:])
 return len(set(d)&live)
tab={}
def add_arg(y,old):
 for x in old+[y]:
  for ot,aa,bb in [('+',x,y),('*',x,y),('-',x,y),('-',y,x)]:
   vv=op(ot,vals[aa],vals[bb]);tab.setdefault(vv,[]).append((ot,aa,bb))
for i,y in enumerate(args):add_arg(y,args[:i])
inv={}
def invmod(a):
 if a not in inv:inv[a]=pow(a,p-2,p)
 return inv[a]
def roots(aa,bb,target):
 # aa*x^2+bb*x=target over the prime field. None means an unconstrained sample.
 if aa==0:
  if bb==0:return None if target==0 else ()
  return ((target*invmod(bb))%p,)
 disc=(bb*bb+4*aa*target)%p;s=pow(disc,(p+1)//4,p)
 if s*s%p!=disc:return ()
 fac=invmod((2*aa)%p);x=((-bb+s)*fac)%p;y=((-bb-s)*fac)%p
 return (x,) if x==y else (x,y)
for idx,row in enumerate(rows):
 name,o,a,b=row;target=op(o,vals[str(a)],vals[str(b)]);rr=rows.copy();rr[idx]=[name,'+',0,0];potential=87-count(rr)
 if potential>=3:
  for z in args:
   zv=vals[z]
   # Middle gate is m*x+n, with m/n chosen per sample.
   for mid,reverse,m,n in [('+',False,(1,1,1),zv),('-',False,(1,1,1),tuple((-v)%p for v in zv)),('-',True,(p-1,p-1,p-1),zv),('*',False,zv,(0,0,0))]:
    for final,flip in [('+',False),('-',False),('-',True),('*',False)]:
     solutions=[]
     for x,z0,mm,nn in zip(target,zv,m,n):
      if final=='+':aa,bb,cc=0,(mm+1)%p,(x-nn)%p
      elif final=='-' and not flip:aa,bb,cc=0,(mm-1)%p,(x-nn)%p
      elif final=='-':aa,bb,cc=0,(1-mm)%p,(x+nn)%p
      else:aa,bb,cc=mm,nn,x
      rs=roots(aa,bb,cc)
      if rs is None or not rs:solutions=[];break
      solutions.append(rs)
     if len(solutions)!=3:continue
     for sig in itertools.product(*solutions):
      if sig not in tab:continue
      for first in tab[sig]:
       mk=lambda v:int(v) if v.isdigit() else v
       ma,mb=(z,'TMPA') if reverse else ('TMPA',z)
       fa,fb=('TMPA','TMPB') if flip else ('TMPB','TMPA')
       candidate=rows[:idx]+[['TMPA',first[0],mk(first[1]),mk(first[2])],['TMPB',mid,mk(ma),mk(mb)],[name,final,fa,fb]]+rows[idx+1:]
       c=count(candidate)
       if c<87:print('CANDIDATE',idx+1,row,'=>',candidate[idx:idx+3],'live',c,flush=True)
  print('checked target',idx+1,name,'potential',potential,flush=True)
 vals[name]=target;add_arg(name,args);args.append(name)
print('done; modular signature screening only')
