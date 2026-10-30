import json,random,hashlib
from pathlib import Path
p=2305843009213693951;r=random.Random(80281234);candidate=Path(__file__).resolve().parent/'candidate.json';raw=candidate.read_bytes();
if hashlib.sha256(raw).hexdigest()!='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f':raise RuntimeError('candidate hash mismatch')
j=json.loads(raw);rows=j['source'];base=j['witnesses']+j['fixed_numerals']; vals={n:tuple(r.randrange(2,p-1) for _ in range(3)) for n in base};vals.update({str(i):(i,i,i) for i in [0,1,2,3,4]});args=list(vals)
def op(o,a,b):
 if o=='+':return tuple((x+y)%p for x,y in zip(a,b))
 if o=='-':return tuple((x-y)%p for x,y in zip(a,b))
 return tuple(x*y%p for x,y in zip(a,b))
def key(z):return str(z)
def count(rs):
 table={z[0]:z for z in rs};todo=['P13'];live=set()
 while todo:
  x=todo.pop()
  if x in live:continue
  live.add(x)
  if x in table:todo.extend(key(a) for a in table[x][2:])
 return len(set(table)&live)
inv={}
def div(a,b):
 if 0 in b:return None
 if b not in inv:inv[b]=tuple(pow(z,p-2,p) for z in b)
 return op('*',a,inv[b])
tab={}
def add_arg(y,old):
 for x in old+[y]:
  for ot,aa,bb in [('+',x,y),('*',x,y),('-',x,y),('-',y,x)]:
   vv=op(ot,vals[aa],vals[bb]);tab.setdefault(vv,[]).append((ot,aa,bb))
for i,y in enumerate(args):add_arg(y,args[:i])
for idx,row in enumerate(rows):
 name,o,a,b=row;target=op(o,vals[key(a)],vals[key(b)]);known=set(vals.values())
 for z in args:
  vz=vals[z]
  for f,need,orient in [('+',op('-',target,vz),0),('-',op('+',target,vz),0),('-',op('-',vz,target),1),('*',div(target,vz),0)]:
   if need is None or need in known or need not in tab:continue
   for first in tab[need]:
    tmp='SEARCH_TMP';aa,bb=(z,tmp) if orient else (tmp,z);mk=lambda x:int(x) if x.isdigit() else x
    rr=rows[:idx]+[[tmp,first[0],mk(first[1]),mk(first[2])],[name,f,mk(aa),mk(bb)]]+rows[idx+1:];c=count(rr)
    if c<len(rows):print('CANDIDATE',idx+1,row,'=>',rr[idx:idx+2],'live',c,flush=True)
 vals[name]=target;add_arg(name,args);args.append(name)
 if (idx+1)%10==0:print('checked',idx+1,flush=True)
print('done; modular signatures only, no minimality claim')
