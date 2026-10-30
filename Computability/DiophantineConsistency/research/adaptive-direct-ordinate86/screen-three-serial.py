import json,random,hashlib
from pathlib import Path
p=2305843009213693951;r=random.Random(80281234);candidate=Path(__file__).resolve().parent/'candidate.json';raw=candidate.read_bytes();
if hashlib.sha256(raw).hexdigest()!='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f':raise RuntimeError('candidate hash mismatch')
j=json.loads(raw);rows=j['source'];base=j['witnesses']+j['fixed_numerals']; vals={n:tuple(r.randrange(2,p-1) for _ in range(3)) for n in base};vals.update({str(i):(i,i,i) for i in [0,1,2,3,4]});args=list(vals)
def op(o,a,b):
 if o=='+':return tuple((x+y)%p for x,y in zip(a,b))
 if o=='-':return tuple((x-y)%p for x,y in zip(a,b))
 return tuple(x*y%p for x,y in zip(a,b))
def count(rs):
 table={z[0]:z for z in rs};todo=['P13'];live=set()
 while todo:
  x=todo.pop()
  if x in live:continue
  live.add(x)
  if x in table:todo.extend(str(a) for a in table[x][2:])
 return len(set(table)&live)
inv={}
def div(a,b):
 if 0 in b:return None
 if b not in inv:inv[b]=tuple(pow(z,p-2,p) for z in b)
 return op('*',a,inv[b])
def prior_values(target,operand):
 return [('+',op('-',target,operand),False),('-',op('+',target,operand),False),('-',op('-',operand,target),True),('*',div(target,operand),False)]
tab={}
def add_arg(y,old):
 for x in old+[y]:
  for ot,aa,bb in [('+',x,y),('*',x,y),('-',x,y),('-',y,x)]:
   vv=op(ot,vals[aa],vals[bb]);tab.setdefault(vv,[]).append((ot,aa,bb))
for i,y in enumerate(args):add_arg(y,args[:i])
for idx,row in enumerate(rows):
 name,o,a,b=row;target=op(o,vals[str(a)],vals[str(b)]);rr=rows.copy();rr[idx]=[name,'+',0,0];potential=len(rows)-count(rr)
 if potential>=3:
  for final_arg in args:
   for final_op,intermediate,flip in prior_values(target,vals[final_arg]):
    if intermediate is None:continue
    for middle_arg in args:
     for middle_op,need,midflip in prior_values(intermediate,vals[middle_arg]):
      if need is None or need not in tab:continue
      for first in tab[need]:
       mk=lambda x:int(x) if x.isdigit() else x
       ma,mb=(middle_arg,'TMPA') if midflip else ('TMPA',middle_arg)
       fa,fb=(final_arg,'TMPB') if flip else ('TMPB',final_arg)
       candidate=rows[:idx]+[['TMPA',first[0],mk(first[1]),mk(first[2])],['TMPB',middle_op,mk(ma),mk(mb)],[name,final_op,mk(fa),mk(fb)]]+rows[idx+1:]
       c=count(candidate)
       if c<len(rows):print('CANDIDATE',idx+1,row,'=>',candidate[idx:idx+3],'live',c,flush=True)
  print('checked target',idx+1,name,'potential',potential,flush=True)
 vals[name]=target;add_arg(name,args);args.append(name)
print('done; modular signature screening only')
