import json,random,itertools,hashlib
from pathlib import Path
p=2305843009213693951;r=random.Random(80281234);candidate=Path(__file__).resolve().parent/'candidate.json';raw=candidate.read_bytes();
if hashlib.sha256(raw).hexdigest()!='da6b88365da3ec9db6040373c25de20b30baf63edc9fdf742de2aa4b2c06e6e8':raise RuntimeError('candidate hash mismatch')
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
def div(a,b):
 if 0 in b:return None
 if b not in inv:inv[b]=tuple(pow(z,p-2,p) for z in b)
 return op('*',a,inv[b])
def prior_values(target,operand):
 return [('+',op('-',target,operand),False),('-',op('+',target,operand),False),('-',op('-',operand,target),True),('*',div(target,operand),False)]
def roots_square(t):
 sol=[]
 for n in t:
  s=pow(n,(p+1)//4,p)
  if s*s%p!=n:return []
  sol.append((s,) if s==0 else (s,p-s))
 return itertools.product(*sol)
for idx,row in enumerate(rows):
 name,o,a,b=row;target=op(o,vals[str(a)],vals[str(b)]);rr=rows.copy();rr[idx]=[name,'+',0,0];potential=87-count(rr)
 if potential>=3:
  by_sig={}
  for z in args:by_sig.setdefault(vals[z],[]).append(z)
  def check(first,mid,ma,mb,last,fa,fb):
   mk=lambda x:int(x) if x.isdigit() else x
   cand=rows[:idx]+[['TMPA',first[0],mk(first[1]),mk(first[2])],['TMPB',mid,mk(ma),mk(mb)],[name,last,mk(fa),mk(fb)]]+rows[idx+1:]
   c=count(cand)
   if c<87:print('CANDIDATE',idx+1,row,'=>',cand[idx:idx+3],'live',c,flush=True)
  # Gate 2 combines TMPA with itself; gate 3 combines TMPB with an earlier node.
  for xs,reps in tab.items():
   for mid in ['+','*']:
    ms=op(mid,xs,xs)
    # Last operation TMPB op z (or z-TMPB). Find z signatures.
    for final,need,flip in prior_values(target,ms):
     if need is None or need not in by_sig:continue
     for z in by_sig[need]:
      for first in reps:
       fa,fb=(z,'TMPB') if flip else ('TMPB',z)
       # prior_values solves unknown op ms, so subtraction orientation reverses.
       if final=='-':fa,fb=fb,fa
       check(first,mid,'TMPA','TMPA',final,fa,fb)
    # Gate 3 reuses TMPA as well as TMPB.
    for final,fa,fb in [('+','TMPB','TMPA'),('-','TMPB','TMPA'),('-','TMPA','TMPB'),('*','TMPB','TMPA')]:
     av=ms if fa=='TMPB' else xs;bv=ms if fb=='TMPB' else xs
     if op(final,av,bv)==target:
      for first in reps:check(first,mid,'TMPA','TMPA',final,fa,fb)
  # Gate 3 combines TMPB with itself. Invert doubling/square, then the middle operation.
  half=tuple((n*pow(2,p-2,p))%p for n in target)
  for final,ms in itertools.chain([('+',half)],(('*',s) for s in roots_square(target))):
   for z in args:
    for mid,need,flip in prior_values(ms,vals[z]):
     if need is None or need not in tab:continue
     for first in tab[need]:
      ma,mb=(z,'TMPA') if flip else ('TMPA',z)
      check(first,mid,ma,mb,final,'TMPB','TMPB')
  print('checked target',idx+1,name,'potential',potential,flush=True)
 vals[name]=target;add_arg(name,args);args.append(name)
print('done; modular signature screening only')
