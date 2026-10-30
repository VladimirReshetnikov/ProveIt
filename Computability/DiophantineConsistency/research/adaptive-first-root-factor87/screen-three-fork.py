import json,random,hashlib
from pathlib import Path
p=2305843009213693951;r=random.Random(80281234);candidate=Path(__file__).resolve().parent/'candidate.json';raw=candidate.read_bytes();
if hashlib.sha256(raw).hexdigest()!='da6b88365da3ec9db6040373c25de20b30baf63edc9fdf742de2aa4b2c06e6e8':raise RuntimeError('candidate hash mismatch')
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
 name,o,a,b=row;target=op(o,vals[key(a)],vals[key(b)]);rr=rows.copy();rr[idx]=[name,'+',0,0];potential=87-count(rr)
 if potential>=3:
  for value,representatives in list(tab.items()):
   for f,need,flip in [('+',op('-',target,value),False),('-',op('-',value,target),False),('-',op('+',target,value),True),('*',div(target,value),False)]:
    if need is None or need not in tab:continue
    for first in representatives:
     for second in tab[need]:
      if first==second:continue
      mk=lambda x:int(x) if x.isdigit() else x
      aa,bb=('TMPB','TMPA') if flip else ('TMPA','TMPB')
      candidate=rows[:idx]+[['TMPA',first[0],mk(first[1]),mk(first[2])],['TMPB',second[0],mk(second[1]),mk(second[2])],[name,f,aa,bb]]+rows[idx+1:]
      c=count(candidate)
      if c<87:print('CANDIDATE',idx+1,row,'=>',candidate[idx:idx+3],'live',c,flush=True)
  print('checked target',idx+1,name,'potential',potential,flush=True)
 vals[name]=target;add_arg(name,args);args.append(name)
print('done; modular signature screening only')
