from itertools import combinations,permutations,product
from math import comb,factorial
from collections import defaultdict
from pathlib import Path
import sys,json,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]));from cover3 import mul,gap,weakcomps
OUT=Path(__file__).parent

def posets(n):
 if n==0:yield ();return
 for rows in posets(n-1):
  for mask in range(1<<(n-1)):
   # predecessor subset is an ideal: i<j and j selected implies i selected
   if any(rows[i]&mask and not(mask>>i&1)for i in range(n-1)):continue
   yield tuple(rows[i]|((1<<(n-1))if mask>>i&1 else 0)for i in range(n-1))+(0,)

def comps(n,k):
 if k==0:
  if n==0:yield ()
  return
 for i in range(1,n-k+2):
  for c in comps(n-i,k-1):yield(i,)+c

def cores(n):
 for k in range(1,n+1):
  for rr in posets(k):
   for cc in comps(n,k):
    labels=[i for i,c in enumerate(cc)for _ in range(c)]
    yield tuple(sum(1<<j for j,b in enumerate(labels)if i!=j and(a==b or rr[a]>>b&1))for i,a in enumerate(labels))

def transitive(rows):
 return all(not(rows[j]&~(rows[i]|(1<<i)))for i,row in enumerate(rows)for j in range(len(rows))if row>>j&1)

def types_for(rows,aa,ss):
 n=len(rows);types=[]
 for mask in (1,2,3):
  rr=list(rows)+[0]
  for i,a in enumerate(aa):
   if mask>>i&1:
    if ss[i]==-1:rr[a]|=1<<n
    else:rr[n]|=1<<a
  if transitive(rr):types.append(mask)
 return types

def canonical(rows,aa,ss,types):
 n=len(rows);rest=[i for i in range(n)if i not in aa];keys=[]
 for sw in(0,1):
  for pp in permutations(rest):
   order=(aa[sw],aa[1-sw])+pp
   for rev in(0,1):
    rr=tuple(sum(1<<j for j in range(n)if (rows[order[j]]>>order[i]&1 if rev else rows[order[i]]>>order[j]&1))for i in range(n))
    sign=tuple(((-1)**rev)*ss[i]for i in(sw,1-sw));tt=tuple(sorted(((t&1)<<1 | (t&2)>>1)if sw else t for t in types))
    keys.append((rr,sign,tt))
 return min(keys)

def polynomial(rows,ss,types):
 n=len(rows);d=len(types);g=[defaultdict(int)for _ in range(4)]
 for r in range(3):
  for quota in weakcomps(r,d):
   masks=[t for t,c in zip(types,quota)for _ in range(c)];rr=list(rows)+[0]*r
   for j,t in enumerate(masks):
    for a in range(2):
     if t>>a&1:
      if ss[a]==-1:rr[a]|=1<<(n+j)
      else:rr[n+j]|=1<<a
   from functools import lru_cache
   @lru_cache(None)
   def feasible(A,B):
    if not A:return True
    bit=A&-A;i=bit.bit_length()-1;choices=rr[i]&B
    while choices:
     b=choices&-choices;choices-=b
     if feasible(A-bit,B-b):return True
    return False
   for rc in product((0,1,2),repeat=n):
    ca=sum(1<<i for i,v in enumerate(rc)if v==1);cb=sum(1<<i for i,v in enumerate(rc)if v==2)
    for re in product((1,2),repeat=r):
     A=ca|sum(1<<(n+i)for i,v in enumerate(re)if v==1);B=cb|sum(1<<(n+i)for i,v in enumerate(re)if v==2);k=A.bit_count()
     if k>3 or k!=B.bit_count():continue
     if feasible(A,B):g[k][quota]+=1
 return [dict(a)for a in g]

def serialized(poly):return [[list(q),v]for q,v in sorted(poly.items())if v]

if __name__=='__main__':
 start=time.time();templates={};stats={}
 for n in range(2,6):
  count=0
  for rows in cores(n):
   count+=1
   for aa in combinations(range(n),2):
    for ss in product((-1,1),repeat=2):
     types=types_for(rows,aa,ss)
     if not types:continue
     key=canonical(rows,aa,ss,types);templates[key]=templates.get(key,0)+1
  stats[n]=count;print('n',n,'cores',count,'cumulative templates',len(templates),'sec',time.time()-start,flush=True)
 records=[];uniques={}
 for i,((rows,ss,types),mult)in enumerate(sorted(templates.items())):
  g=polynomial(rows,ss,types);D1=gap(g[0],g[1],g[2],3);D2=gap(g[1],g[2],g[3],3)
  key=str([serialized(a)for a in g]);gid=uniques.setdefault(key,len(uniques))
  records.append({'id':i,'gamma_id':gid,'core_rows':rows,'signs':ss,'types':types,'multiplicity':mult,'gamma':[serialized(a)for a in g],'gap1':serialized(D1),'gap2':serialized(D2),'positive1':all(v>=0 for v in D1.values()),'positive2':all(v>=0 for v in D2.values())})
  if i%100==0:print('polys',i,'distinct',len(uniques),'sec',time.time()-start,flush=True)
 (OUT/'templates.json').write_text(json.dumps({'core_counts':stats,'templates':records,'unique_gamma':len(uniques),'seconds':time.time()-start},indent=2)+'\n')
 print('FINAL',len(records),'gamma',len(uniques),'bad1',sum(not r['positive1']for r in records),'bad2',sum(not r['positive2']for r in records),'seconds',time.time()-start)
