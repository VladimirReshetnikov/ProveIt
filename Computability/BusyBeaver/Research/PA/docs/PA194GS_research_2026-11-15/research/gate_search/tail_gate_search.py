from pathlib import Path
import sys,json
from functools import lru_cache
PACKAGE=Path(__file__).resolve().parents[2];sys.path.insert(0,str(PACKAGE/'vendor/construction'));import engine_helpers as b
P=PACKAGE/'machine';O=Path(sys.argv[1])if len(sys.argv)>1 else Path('tail_templates');O.mkdir(exist_ok=True)
base={k:v for k,v in b.read_table(P/'raw.native.tm').items()if k[0]<1300};nodes={k:b.tup(v)for k,v in json.loads((P/'nodes.json').read_text()).items()};orig=b.tup(json.loads((P/'tree.json').read_text()))
INC=('leaf','inc',1)
macros={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,INC:61,'node60':99,'node61':190,'node54':114,'node57':20,'node69':30,'node146':196,'node149':217,(INC,INC):99,((INC,INC),(INC,INC)):190}
def pair(t):return isinstance(t,tuple)and len(t)==2
@lru_cache(None)
def count(t):return count(t[0])+count(t[1])if pair(t)else 1
@lru_cache(None)
def attr(t):
 if isinstance(t,str):return attr(nodes[t])
 if t[0]=='leaf':return 0,0,0,0,int(t[1]=='inc'),0
 a,d=attr(t[0]),attr(t[1]);bad=a[5]+d[5]+int(t[0]=='node142')+int(t[1]=='node72');return 1+max(a[0],d[0]),a[1]+1,max(a[1]+1,a[2],d[2]),max(a[3],d[3],a[1]+1 if a[4]else 0),a[4],bad
# attr recurses into native macro definitions and would flag internal node72 irrelevant; their bads are actually zero. all macro occurrences below are only top AX leaves.
@lru_cache(None)
def aa(t):
 if not pair(t):return attr(t)[:5]+(0,)
 a,d=aa(t[0]),aa(t[1]);bad=a[5]+d[5]+int(t[0]=='node142')+int(t[1]=='node72');return 1+max(a[0],d[0]),a[1]+1,max(a[1]+1,a[2],d[2]),max(a[3],d[3],a[1]+1 if a[4]else 0),a[4],bad

def split(t,k):
 if k==0:return None,t
 if k==count(t):return t,None
 a,d=t;m=count(a)
 if k<m:
  l,r=split(a,k);return l,(r,d)
 if k==m:return a,d
 l,r=split(d,k-m);return(a,l),r

def flat(t):return flat(t[0])+flat(t[1])if pair(t)else[t]
@lru_cache(None)
def shapes(seq):
 if len(seq)==1:return [seq[0]]
 out=[]
 for k in range(1,len(seq)):
  for a in shapes(seq[:k]):
   for d in shapes(seq[k:]):out.append((a,d))
 return out

def replace(t,p,x):
 if not p:return x
 bit=int(p[0]);l=list(t);l[bit]=replace(l[bit],p[1:],x);return tuple(l)
sub=orig[1][1][1];data=[];seen=set()
for K in range(5,11):
 pref,suff=split(sub,count(sub)-K)
 seq=tuple(flat(suff))
 for sh in shapes(seq):
  t=replace(orig,'111',(pref,sh))
  a=aa(t)
  if a[0]>38 or a[2]>6 or a[3]>5 or a[5]:continue
  if t not in seen:seen.add(t);data.append((K,t))
 print('K',K,'shapes',len(shapes(seq)),'valid total',len(data),flush=True)
pre=[]
for(q,bit),(w,d,n)in sorted(base.items()):
 if bit==0:pre.append([q,w,int(d),n])
 else:pre[-1].extend([w,int(d),n])
lines=[str(len(pre))]+[' '.join(map(str,r))for r in pre]+[str(len(data))]
for it,(K,t)in enumerate(data):
 records=[];memo={}
 def rec(t):
  if t in memo:return memo[t]
  if t in macros:x=[0,macros[t],-1,-1]
  else:x=[1,rec(t[0]),rec(t[1]),0]
  q=len(records);records.append(x);memo[t]=q;return q
 rt=rec(t);lines.append(f'{it} {len(records)} {rt}');lines.extend(' '.join(map(str,x))for x in records)
(O/'seeds.txt').write_text('\n'.join(lines)+'\n');(O/'metadata.json').write_text(json.dumps({'valid_templates':len(data),'suffix_range':[5,10]}))
