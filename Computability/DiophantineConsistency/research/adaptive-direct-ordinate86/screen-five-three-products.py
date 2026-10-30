"""Heuristically screen five-gate sums/differences of three two-factor products."""
import hashlib,json,random
from pathlib import Path
p=2305843009213693951;rng=random.Random(80281234);path=Path(__file__).resolve().parent/'candidate.json';raw=path.read_bytes();pin='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f'
if hashlib.sha256(raw).hexdigest()!=pin:raise RuntimeError('candidate hash mismatch')
j=json.loads(raw);rows=j['source'];base=j['witnesses']+j['fixed_numerals'];vals={n:tuple(rng.randrange(2,p-1) for _ in range(3)) for n in base};vals.update({str(i):(i,i,i) for i in range(5)});args=list(vals)
def op(o,a,b):
 if o=='+':return tuple((x+y)%p for x,y in zip(a,b))
 if o=='-':return tuple((x-y)%p for x,y in zip(a,b))
 return tuple(x*y%p for x,y in zip(a,b))
def key(x):return str(x)
def count(rs):
 table={z[0]:z for z in rs};todo=['P13'];live=set()
 while todo:
  x=todo.pop()
  if x in live:continue
  live.add(x)
  if x in table:todo.extend(key(a) for a in table[x][2:])
 return len(set(table)&live)
if count(rows)!=len(rows):raise RuntimeError('unexpected original liveness count')
products={}
def add_arg(y,old):
 for x in old+[y]:
  v=op('*',vals[x],vals[y]);products.setdefault(v,[]).append((x,y))
for i,y in enumerate(args):add_arg(y,args[:i])
hits=0;checked=0
for idx,row in enumerate(rows):
 name,o,a,b=row;target=op(o,vals[key(a)],vals[key(b)]);masked=rows.copy();masked[idx]=[name,'+',0,0];potential=len(rows)-count(masked)
 if potential>=5:
  checked+=1;existing=set(vals.values())
  allowed=[(v,ab) for v,ab in products.items() if v not in existing]
  for va,aa in allowed:
   for vb,bb in allowed:
    for first in ('+','-'):
     partial=op(first,va,vb)
     for second,vc in [('+',op('-',target,partial)),('-',op('-',partial,target))]:
      if vc in existing or vc not in products:continue
      for xa,ya in aa:
       for xb,yb in bb:
        for xc,yc in products[vc]:
         mk=lambda q:int(q) if q.isdigit() else q
         new=[['TMPA','*',mk(xa),mk(ya)],['TMPB','*',mk(xb),mk(yb)],['TMPC','*',mk(xc),mk(yc)],['TMPD',first,'TMPA','TMPB'],[name,second,'TMPD','TMPC']]
         candidate=rows[:idx]+new+rows[idx+1:];live=count(candidate)
         if live<len(rows):
          hits+=1;print('CANDIDATE',idx+1,name,'rows',new,'live',live,flush=True)
  print('checked target',idx+1,name,'potential',potential,flush=True)
 vals[name]=target;add_arg(name,args);args.append(name)
print('done; targets',checked,'candidates',hits,'modular signature screening only',flush=True)
