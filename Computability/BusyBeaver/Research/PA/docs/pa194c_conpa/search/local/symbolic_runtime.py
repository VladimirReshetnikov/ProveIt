# Adapted from the supplied PA194 executable verifier; original James Chang
# and ProveIt license notices are retained beside this file.
import re,json,itertools
from pathlib import Path
ROOT=Path(__file__).resolve().parent
BIT=(('b',0),('b',1));PLAIN=('x','none',-1)
SK=[51,36,25,48,32,33,22,55,60];SKMAP={q:r for r,q in enumerate(SK)}
PHYSICAL=[6,2,0,4,3,7,8,5,1]
BOXSTATES={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
def frame(p,extra=0,effect=PLAIN):
 return (84,False,(BIT[1],),tuple(BIT[b] for b in p)+(('r',0,1,48+extra-len(p)),BIT[1],effect))
def oracle(q,br,x):
 _,kind,r=x
 if kind=='none' and q in SKMAP:
  r=SKMAP[q];return (1 if r==0 else 3,('x','mark',r),False)
 if kind=='mark' and r<9:
  if q==64:return (40,('x','inc',r),False)
  if q==0 and br is not None and br[0]==r:return (97,PLAIN,False) if br[1] else (40,('x','dec',r),True)
def norm(s,left=False):
 out=[]
 for x in s:
  if x[0]=='b':x=('r',x[1],0,1)
  if x[0]=='r' and x[2]==0 and x[3]==0:continue
  if out and x[0]=='r' and out[-1][0]=='r' and x[1]==out[-1][1]:
   y=out[-1];out[-1]=('r',x[1],x[2]+y[2],x[3]+y[3])
  else:out.append(x)
 if left and out and out[-1][0]=='r' and out[-1][1]==0:out.pop()
 return tuple(out)
def canonical(s):
 q,onl,l,r=s;return q,onl,norm(l,True),norm(r)
def matches(s,t):return s[0]==t[0] and s[1]==t[1] and norm(s[2],True)==t[2] and norm(s[3])==t[3]
def sstep(rows,br,s):
 q,onl,l,r=s
 if onl:
  if not l:return (q,False,(),(BIT[0],)+r),False
  x=l[0];tail=l[1:]
  if x[0]=='b':return (q,False,tail,(x,)+r),False
  if x[0]=='r':
   _,b,a,c=x;act=rows.get((q,b))
   if act is not None and not act[1] and act[2]==q:return (q,True,tail,(('r',act[0],a,c),)+r),False
   if c>0:return (q,True,(BIT[b],('r',b,a,c-1))+tail,r),False
   if a==0:return (q,True,tail,r),False
  return None
 if not r:return None
 x=r[0];tail=r[1:]
 if x[0]=='b':
  act=rows.get((q,x[1]))
  if act is None:return None
  w,d,n=act
  return ((n,False,(BIT[w],)+l,tail) if d else (n,True,l,(BIT[w],)+tail)),True
 if x[0]=='r':
  _,b,a,c=x;act=rows.get((q,b))
  if act is not None and act[1] and act[2]==q:return (q,False,(('r',act[0],a,c),)+l,tail),False
  if c>0:return (q,False,l,(BIT[b],('r',b,a,c-1))+tail),False
  if a==0:return (q,False,l,tail),False
  return None
 if tail:return None
 oc=oracle(q,br,x)
 if oc is not None:
  n,x2,extra=oc;return (n,True,((BIT[1],)+l if extra else l),(x2,)),False
 act=rows.get((q,0))
 if act is not None and act[0]==0 and not act[1]:return (act[2],True,l,r),True
 return None
def run(rows,c,fuel=1024,observe=None):
 site,br,s,t=c;moved=False
 for k in range(fuel):
  if moved and (s[0]==254 if t is None else matches(s,t)):return k
  if observe is not None:observe(s)
  nxt=sstep(rows,br,s)
  if nxt is None:return None
  s,m=nxt;moved|=m
 return None
def validate(rows,cs,observe=None):
 lengths=[]
 for c in cs:
  v=run(rows,c,observe=observe)
  if v is None:return {'ok':False,'failed':(c[0],c[1]),'completed':len(lengths)}
  lengths.append(v)
 return {'ok':True,'contracts':len(cs),'max_steps':max(lengths),'total_steps':sum(lengths)}
def source():
 nodes={}
 for line in (ROOT/'Program.lean').read_text().splitlines():
  m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
  if not m:continue
  tokens=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2]);children=[]
  for op,arg,name in tokens:children.append(name if name else ('leaf',op,int(arg) if arg else None))
  assert len(children)==2;nodes[m[1]]=tuple(children)
 ax=json.loads((ROOT/'reconstructed_tree.json').read_text());sites=[]
 def walk(t,p):
  if isinstance(t,str):return walk(ax if t=='x67' else nodes[t],p)
  if t[0]=='leaf':sites.append((p,t[1],t[2]));return
  walk(t[0],p+(0,));walk(t[1],p+(1,))
 walk('node172',())
 by_path={p:i for i,(p,op,arg) in enumerate(sites)}
 def locate(p):
  if p in by_path:return by_path[p]
  for i,(q,_,_) in enumerate(sites):
   if q[:len(p)]==p or (p[:len(q)]==q and not any(p[len(q):])):return i
  raise ValueError(p)
 def after(p):
  p=list(p)
  for i in range(len(p)-1,-1,-1):
   if p[i]==0:p[i]=1;return locate(tuple(p[:i+1]))
  raise ValueError(('exit',p))
 def cut(p,b,k):
  for i in range(len(p)-1,-1,-1):
   if p[i]==b:
    k-=1
    if not k:return p[:i]
  raise ValueError((p,b,k))
 ins=[]
 for p,op,arg in sites:
  if op=='inc':code=('inc',arg,after(p))
  elif op=='dec':code=('dec',arg,after(cut(p,0,1)),after(p))
  elif op=='breakTo':code=('jump',after(cut(p,0,arg)))
  elif op=='continueTo':code=('jump',locate(cut(p,1,arg)))
  elif op=='halt':code=('halt',)
  else:raise ValueError(op)
  ins.append(code)
 cs=[]
 for i,code in enumerate(ins):
  st=frame(sites[i][0])
  if code[0]=='inc':
   _,r,n=code;cs.append((i,None,st,canonical(frame(sites[n][0],0,('x','inc',PHYSICAL[r])))))
  elif code[0]=='dec':
   _,r,z,p=code;cs.append((i,(PHYSICAL[r],True),st,canonical(frame(sites[z][0]))));cs.append((i,(PHYSICAL[r],False),st,canonical(frame(sites[p][0],1,('x','dec',PHYSICAL[r])))))
  elif code[0]=='jump':cs.append((i,None,st,canonical(frame(sites[code[1]][0]))))
  else:cs.append((i,None,st,None))
 return sites,ins,cs
def table():
 rows={}
 for line in (ROOT/'pa194.native.tm').read_text().splitlines():
  q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d=='R',int(n))
 return rows
if __name__=='__main__':
 sites,ins,cs=source();print(len(sites),len(cs),max(len(p) for p,op,a in sites));print(validate(table(),cs))
