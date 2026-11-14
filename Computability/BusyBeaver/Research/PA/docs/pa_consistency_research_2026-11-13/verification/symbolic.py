"""Independent Python port of the finite path and symbolic execution checks.
Source conventions: jamesyc/BusyBeaver, MIT license, M6/Runtime.lean.
"""
from pathlib import Path
import re, ast
from collections import defaultdict
ROOT=Path(__file__).resolve().parents[1]/'reference/pa196'
labels=ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]*\])',(ROOT/'PA196/Conjugacy.lean').read_text())[1])
rows={}
for line in (ROOT/'data/pa196.tm').read_text().splitlines():
 q,b,w,d,n=line.split(); rows[labels[int(q)],int(b)]=(int(w),d,labels[int(n)])
NODES={}
def parse_tree(text):
 ts=re.findall(r'\.\w+|\w+|[()]',text); pos=0
 def sub():
  nonlocal pos
  t=ts[pos]; pos+=1
  if t=='(':
   out=sub(); assert ts[pos]==')';pos+=1;return out
  if t=='.node':return (sub(),sub())
  if t=='.leaf':return sub()
  if t=='.halt':return ('halt',0)
  if t in ['.inc','.dec','.breakTo','.continueTo']:
   v=int(ts[pos]);pos+=1;return (t[1:],v)
  return NODES[t]
 r=sub();assert pos==len(ts);return r
for line in (ROOT/'PA196/Program.lean').read_text().splitlines():
 m=re.match(r'def (\w+) : Tree := (.*)',line)
 if m:NODES[m[1]]=parse_tree(m[2])
TREE=NODES['trie']
def isleaf(t):return isinstance(t[0],str)
def flatten(t,p=()):
 if isleaf(t):return [(p,t)]
 return flatten(t[0],p+(0,))+flatten(t[1],p+(1,))
SITES=flatten(TREE)
SIZES={}
def size(t):
 if t not in SIZES:SIZES[t]=1 if isleaf(t) else size(t[0])+size(t[1])
 return SIZES[t]
def lookup(p,t=TREE):
 if isleaf(t):
  assert not any(p);return 0
 if not p:return 0
 if p[0]:return size(t[0])+lookup(p[1:],t[1])
 return lookup(p[1:],t[0])
def successor(p):
 r=list(p)
 for j in range(len(r)-1,-1,-1):
  if not r[j]:r[j]=1;return tuple(r)
  r[j]=0
 return None
def after(p):
 n=successor(p);return 0 if n is None else lookup(n)
def cut(p,b,k):
 for i in range(len(p)-1,-1,-1):
  if p[i]==b:
   k-=1
   if k==0:return p[:i]
 raise ValueError((p,b,k))
PHY=[6,2,0,4,3,7,8,5,1]
# Segments are ('b',bit), ('r',bit,a,c), or ('x',effect,register).
B=lambda b:('b',int(b))
R=lambda b,a,c:('r',int(b),a,c)
X=lambda e='none',r=0:('x',e,r)
def rootframe(p,extra=0,e='none',reg=0):return (84,False,[B(1)],[*map(B,p),R(0,1,48+extra-len(p)),B(1),X(e,reg)])
def norm(s,strip=False):
 out=[]
 for t in s:
  if t[0]=='b':t=R(t[1],0,1)
  if t[0]=='r' and t[2:]==(0,0):continue
  if out and t[0]=='r' and out[-1][0]=='r' and out[-1][1]==t[1]:
   out[-1]=R(t[1],out[-1][2]+t[2],out[-1][3]+t[3])
  else:out.append(t)
 if strip and out and out[-1][0]=='r' and not out[-1][1]:out.pop()
 return tuple(out)
def normconf(s):return (s[0],s[1],norm(s[2],True),norm(s[3]))
SK=[51,36,25,48,32,33,22,55,60]
def oracle(q,br,x):
 _,e,r=x
 if e=='none' and q in SK:
  r=SK.index(q);return (1 if r==0 else 3,X('mark',r),False)
 if e=='mark' and r<9:
  if q==64:return (40,X('inc',r),False)
  if q==0 and br is not None and br[0]==r:
   return (97,X(),False) if br[1] else (40,X('dec',r),True)
 return None

def sstep(M,br,s,visit=None):
 q,on,l,r=s
 if on:
  if not l:return (q,False,[],[B(0)]+r),False
  t,*tail=l
  if t[0]=='b':return (q,False,tail,[t]+r),False
  if t[0]=='r':
   _,b,a,c=t; row=M.get((q,b))
   if row is not None and row[1]=='L' and row[2]==q:return (q,True,tail,[R(row[0],a,c)]+r),False
   if c:return (q,True,[B(b),R(b,a,c-1)]+tail,r),False
   if not a:return (q,True,tail,r),False
  return None
 if not r:return None
 t,*tail=r
 if t[0]=='b':
  row=M.get((q,t[1]))
  if row is None:return None
  if visit is not None:visit(s)
  w,d,n=row
  return ((n,False,[B(w)]+l,tail) if d=='R' else (n,True,l,[B(w)]+tail)),True
 if t[0]=='r':
  _,b,a,c=t;row=M.get((q,b))
  if row is not None and row[1]=='R' and row[2]==q:return (q,False,[R(row[0],a,c)]+l,tail),False
  if c:return (q,False,l,[B(b),R(b,a,c-1)]+tail),False
  if not a:return (q,False,l,tail),False
  return None
 if t[0]=='x' and not tail:
  v=oracle(q,br,t)
  if v is not None:
   n,x,extra=v;return (n,True,([B(1)]+l if extra else l),[x]),False
  row=M.get((q,0))
  if row is not None and row[:2]==(0,'L'):return (row[2],True,l,r),True
 return None

def cases():
 for i,(p,(op,k)) in enumerate(SITES):
  if op=='halt':yield (i,None,rootframe(p),None);continue
  if op=='inc':
   yield (i,None,rootframe(p),rootframe(SITES[after(p)][0],0,'inc',PHY[k]))
  if op=='dec':
   yield (i,(PHY[k],True),rootframe(p),rootframe(SITES[after(cut(p,0,1))][0]))
   yield (i,(PHY[k],False),rootframe(p),rootframe(SITES[after(p)][0],1,'dec',PHY[k]))
  if op=='breakTo':yield (i,None,rootframe(p),rootframe(SITES[after(cut(p,0,k))][0]))
  if op=='continueTo':yield (i,None,rootframe(p),rootframe(SITES[lookup(cut(p,1,k))][0]))
CASES=list(cases())

def run_case(M,c,visit=None,limit=2048):
 i,br,s,tgt=c; goal=normconf(tgt) if tgt else None;moved=False
 for n in range(limit):
  if moved and ((s[0]==254) if tgt is None else (s[0]==tgt[0] and s[1]==tgt[1] and normconf(s)==goal)):
   return True,n,s
  v=sstep(M,br,s,visit)
  if v is None:return False,n,s
  s,m=v;moved=moved or m
 return False,limit,s

def validate(M,visit=None):
 worst=0
 for c in CASES:
  ok,n,s=run_case(M,c,visit)
  if not ok:return False,(c[0],c[1],n,s)
  worst=max(worst,n)
 return True,{'sites':len(SITES),'cases':len(CASES),'max_symbolic_steps':worst}
if __name__=='__main__':
 print(validate(rows))
