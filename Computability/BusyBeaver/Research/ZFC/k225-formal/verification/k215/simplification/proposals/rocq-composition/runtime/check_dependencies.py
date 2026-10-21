"""Owned access-logged dependency audit. Does not execute received code."""
if not __debug__:
 raise RuntimeError('Assertions must be enabled')
import json,hashlib,time
from pathlib import Path
import analyze_symbolic as A
D=Path(__file__).parent
class Logged(dict):
 def __init__(self,t):super().__init__(t);self.reads=set()
 def __getitem__(self,k):self.reads.add(k);return super().__getitem__(k)
def oracle_kind(s,br):
 q,on,l,r=s
 if on or not r or r[0][0]!='x':return None
 k,i=r[0][1:]
 if k=='none' and q in A.SK:return ('mark',A.SK.index(q))
 if k=='mark' and i<9:
  if q==64:return ('inc',i)
  if q==0 and br is not None and br[0]==i:return ('dec0' if br[1] else 'decp',i)
 return None
old=A.I.table(D/'inputs/ST215.tm');new=A.I.table(D/'inputs/DR215.tm')
s0=json.loads((D/'inputs/ST215.sites.json').read_text());s1=json.loads((D/'inputs/DR215.sites.json').read_text())
assert old.keys()==new.keys();patch={k for k in old if old[k]!=new[k]}
records=[];oracle_union=set();total=0
for i,site in enumerate(s0):
 if i%500==0:print(i,flush=True)
 for positive in ([False,True] if site[1]=='CD' else [False]):
  t=Logged(old);events,states,_,_=A.run(t,site,positive);reads=t.reads.copy();calls=set()
  for br,s in states:
   o=oracle_kind(s,br)
   if o:calls.add(o)
  oracle_union|=calls;affected=bool(reads&patch)
  if not affected:
   assert site==s1[i]
   # Strong exact check: every abstract step, including its progress flag, agrees.
   for br,s in states:assert A.step(old,br,s)==A.step(new,br,s)
  else:A.run(new,s1[i],positive)
  records.append(dict(index=i,positive=positive,steps=len(events),reads=sorted(reads),oracles=sorted(calls),affected=affected));total+=len(events)
out=dict(status='ACCESS_LOGGED_DEPENDENCY_PASS',guards=len(records),steps=total,affected=sum(r['affected'] for r in records),unaffected=sum(not r['affected'] for r in records),patch=sorted(patch),oracle_interfaces=sorted(oracle_union),records=records,scope='Exact owned symbolic transcription. Concrete BoxLemmas transport requires independently certified engine agreement; not discharged by symbolic accesses.')
(D/'DEPENDENCIES.json').write_text(json.dumps(out,separators=(',',':')))
print({k:v for k,v in out.items() if k!='records'})
