import sys,json,itertools,collections,random,math,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'verification'))
from grammar import axword,raw_nodes
from layout import *
ONE='1'; INC=('leaf','inc',1)
def I(a,b):return ('I',a,b)
def M(a,b):return ('M',a,b)
def U(a,b):return ('U',a,b)
def E(a,b):return ('E',a,b)
def N(a):return I(a,ONE)
def And(a,b):return N(I(a,N(b)))
def Ex(a,b):return N(U(a,N(b)))
def heads(flags=0):
 d,h,a='DHA'
 hs=[I(Ex(d,U(d,h)),h),I(U(d,U(a,h)),U(a,U(d,h))),I(M(h,d),I(E(h,a),M(a,d))),I(E(h,d),I(M(a,h),M(a,d))),Ex(d,E(h,d)),I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
 for bit,j in enumerate((2,3,5)):
  if flags>>bit&1:
   _,x,(_,y,z)=hs[j];hs[j]=I(y,I(x,z))
 return hs
def gate(swap=0):
 a,b,c='HDA'
 delta=I(E(a,b),U(c,E(a,b)));v=I(M(a,b),U(c,M(a,b)));p=I(c,M(c,b));s=U(b,And(I(M(a,b),p),I(M(c,b),c)));q=U(c,I(s,N(p)))
 return N(I(v,I(delta,q)))if swap else N(I(delta,I(v,q)))
VARS={'D':'node55','H':'node58','A':'node70'}
def emit(f,tag_swap=0,mem_flip=0,eq_flip=0,u_flip=0):
 if isinstance(f,str):return ['node49',INC]if f==ONE else[VARS[f]]
 tag,a,b=f
 if tag=='U' and not u_flip or tag=='M' and mem_flip or tag=='E' and eq_flip:a,b=b,a
 res={'I':0,'M':1,'U':2+tag_swap,'E':3-tag_swap}[tag]
 return emit(a,tag_swap,mem_flip,eq_flip,u_flip)+emit(b,tag_swap,mem_flip,eq_flip,u_flip)+['node65']+[INC]*res
w=axword();ns=raw_nodes()
def expand(s):
 if isinstance(s,str)and s.startswith('x'):return tuple(map(expand,ns[s]))
 return s
initial=expand('x67')
prefix=w[:18];suffix=w[-3:]
assert prefix+sum((emit(h)for h in heads()),[])+emit(gate())+suffix==w

def word(meta):
 ts,mf,ef,uf,flags,sw,order=meta
 opts=(ts,mf,ef,uf)
 pref=emit(U('D','H'),*opts)+prefix[5:]
 return pref+sum((emit(heads(flags)[j],*opts)for j in order),[])+emit(gate(sw),*opts)+suffix

def repr_tree(word,seed=0):
 random.seed(seed);seq=word[:]
 while len(seq)>1:
  count=collections.Counter(zip(seq,seq[1:]))
  p=max(count,key=lambda p:count[p]+random.random())
  out=[];i=0
  while i<len(seq):
   if i+1<len(seq)and(seq[i],seq[i+1])==p:out.append(p);i+=2
   else:out.append(seq[i]);i+=1
  seq=out
 return seq[0]

def stats(t):
 ii={}
 def rec(t):
  if not isnode(t):return
  if t in ii:return
  rec(t[0]);rec(t[1]);ii[t]=len(ii)
 rec(t);return len(ii),list(ii)

def encode(t):
 rs={};ii={}
 def rec(t):
  if not isnode(t):return t
  if t in ii:return ii[t]
  a,b=map(rec,t);q='g'+str(len(rs));rs[q]=[a,b];ii[t]=q;return q
 rt=rec(t);return dict(root=rt,rules=rs)

def base_transformed(tag_swap):
 # Align every constructor's tag trailer by replacing each complete tag run.
 oldnew=[]
 def emitmap(f):
  if isinstance(f,str):return [(x,x)for x in emit(f)]
  tag,a,b=f
  if tag=='U':a,b=b,a
  rr={'I':0,'M':1,'U':2,'E':3}[tag];newrr=({'U':3,'E':2}.get(tag,rr)if tag_swap else rr)
  tail=[]
  for j in range(rr):tail.append((INC,None if j>=newrr else (INC,INC)if j==rr-1 and newrr>rr else INC))
  return emitmap(a)+emitmap(b)+[('node65','node65')]+tail
 oldnew=emitmap(U('D','H'))+[(x,x)for x in prefix[5:]]+sum((emitmap(h)for h in heads()),[])+emitmap(gate())+[(x,x)for x in suffix]
 assert [a for a,b in oldnew]==w
 it=iter(oldnew)
 def rec(t):
  if not isnode(t):
   old,new=next(it);assert old==t;return new
  a,b=rec(t[0]),rec(t[1]);return b if a is None else a if b is None else (a,b)
 return rec(initial)

if __name__=='__main__':
 print('base',stats(initial)[0],len(w),flush=True)
 t=base_transformed(1);print('swapinitial',stats(t)[0],len(word((1,0,0,0,0,0,tuple(range(6))))),flush=True)
 Path('tagswap_initial.json').write_text(json.dumps(encode(t),indent=2))
 best=999;records=[];start=time.time();rng=random.Random(31434)
 for i in range(20000):
  ts=1;mf=rng.randrange(2);ef=rng.randrange(2);uf=rng.randrange(2);flags=rng.randrange(8);sw=rng.randrange(2);order=list(range(6));rng.shuffle(order)
  meta=(ts,mf,ef,uf,flags,sw,tuple(order));ww=word(meta);t=repr_tree(ww,i);n,_=stats(t)
  if n<best:
   best=n;rec={'n':n,'meta':meta,'iteration':i,'tokens':len(ww),**encode(t)};records.append(rec);Path('tagswap_shortlist.json').write_text(json.dumps(records,indent=2));print('BEST',n,meta,'tokens',len(ww),'seconds',time.time()-start,flush=True)
  if i%1000==0:print('iter',i,'best',best,flush=True)
 print('DONE',best,flush=True)
