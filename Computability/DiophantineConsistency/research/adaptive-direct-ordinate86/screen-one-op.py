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
for idx,row in enumerate(rows):
 name,o,a,b=row; val=op(o,vals[key(a)],vals[key(b)])
 for i,x in enumerate(args):
  for y in args[i:]:
   for ot,aa,bb in [('+',x,y),('*',x,y),('-',x,y),('-',y,x)]:
    if op(ot,vals[aa],vals[bb])!=val or (ot,aa,bb)==(o,key(a),key(b)): continue
    rr=rows.copy();rr[idx]=[name,ot,int(aa) if aa.isdigit() else aa,int(bb) if bb.isdigit() else bb];c=count(rr)
    if c<len(rows):print('CANDIDATE',idx+1,row,'=>',rr[idx],'live',c,flush=True)
 vals[name]=val;args.append(name)
print('done')
