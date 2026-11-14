#!/usr/bin/env python3
"""Safe classical AX word variants on the inherited 201-leaf association."""
import sys,itertools,json,time,re,random,collections
from pathlib import Path
BASE=Path(__file__).resolve().parents[2]
OPT=BASE/'work/optimize196'
sys.path.insert(0,str(OPT))
from grammar import axword,raw_nodes
from layout import build,source,validate,opportunities_fast,max_matching,isnode
OUT=BASE/'work/logic/word_variants'
OUT.mkdir(exist_ok=True)

ONE='1'
def C(tag,a,b):return(tag,a,b)
def I(a,b):return C(0,a,b)
def M(a,b):return C(1,a,b)
def U(a,b):return C(2,b,a)
def E(a,b,flip=False):return C(3,b,a)if flip else C(3,a,b)
def N(a):return I(a,ONE)
def And(a,b):return N(I(a,N(b)))
def Ex(a,b):return N(U(a,N(b)))
TOK={'D':'node55','H':'node58','A':'node70',ONE:None}
INC=('leaf','inc',1)
def emit(f):
 if isinstance(f,str):return ['node49',INC]if f==ONE else[TOK[f]]
 tag,a,b=f
 return emit(a)+emit(b)+['node65']+[INC]*tag

def heads(flags,flip):
 d,h,a='DHA';eq=lambda x,y:E(x,y,flip)
 hs=[I(Ex(d,U(d,h)),h),I(U(d,U(a,h)),U(a,U(d,h))),
     I(M(h,d),I(eq(h,a),M(a,d))),I(eq(h,d),I(M(a,h),M(a,d))),
     Ex(d,eq(h,d)),I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
 for bit,j in enumerate((2,3,5)):
  if flags>>bit&1:
   _,x,(_,y,z)=hs[j];hs[j]=I(y,I(x,z))
 return hs
def gate(swap,flip):
 a,b,c='HDA'
 atom=E(a,b,flip);delta=I(atom,U(c,atom))
 atom=M(a,b);v=I(atom,U(c,atom))
 p=I(c,M(c,b));s=U(b,And(I(M(a,b),p),I(M(c,b),c)))
 q=U(c,I(s,N(p)))
 return N(I(v,I(delta,q)))if swap else N(I(delta,I(v,q)))

w=axword()
blocks=[(a,int(b),int(c)) for a,b,c in re.findall(r'\(\.(\w+), (\d+), (\d+)\)',(BASE/'sources/BusyBeaver/PA196/Source/AXProgram.lean').read_text().split('def program')[0])]
assert len(w)==len(blocks)==201
ih=next(i for i,b in enumerate(blocks)if b[1]==503)
ig=next(i for i,b in enumerate(blocks)if b[1]==2258)
prefix=w[:ih];suffix=w[-3:]
baseheads=sum((emit(h)for h in heads(0,False)),[])
basegate=emit(gate(False,False))
assert baseheads==w[ih:ig],(ih,ig,len(baseheads))
assert basegate==w[ig:-3],(ig,len(basegate))
print('word verified',len(w),'prefix',ih,'heads',list(map(lambda h:len(emit(h)),heads(0,False))),'gate',len(basegate),flush=True)

raw=raw_nodes()
def tree(s):
 if isinstance(s,str)and s.startswith('x'):
  a,b=raw[s];return(tree(a),tree(b))
 return s
initial=tree('x67')
leafnames=list(dict.fromkeys(w));leafid={x:i for i,x in enumerate(leafnames)}
post=[];counter=0
def skeleton(t):
 global counter
 if not isnode(t):
  i=counter;counter+=1;return i
 a,b=map(skeleton,t);i=201+len(post);post.append((a,b));return i
rt=skeleton(initial);assert counter==201
def instantiate(word,materialize=False):
 ids=[leafid[x]for x in word];intern={};rules=[]
 for a,b in post:
  k=ids[a],ids[b]
  if k not in intern:
   intern[k]=len(leafnames)+len(rules);rules.append(k)
  ids.append(intern[k])
 if not materialize:return len(rules)
 cache=list(leafnames)
 for a,b in rules:cache.append((cache[a],cache[b]))
 return len(rules),cache[ids[rt]]

def encode(t):
 rs={};idx={}
 def rec(t):
  if not isnode(t):return t
  if t in idx:return idx[t]
  l,r=map(rec,t);n=f'g{len(rs)}';rs[n]=[l,r];idx[t]=n;return n
 r=rec(t);return{'root':r,'rules':rs}

def variants():
 for flip,swap,flags in itertools.product((False,True),(False,True),range(8)):
  hs=list(map(emit,heads(flags,flip)));g=emit(gate(swap,flip))
  for perm in itertools.permutations(range(6)):
   ww=prefix+sum((hs[j]for j in perm),[])+g+suffix
   assert len(ww)==201
   yield {'equality_flip':flip,'gate_swap':swap,'antecedent_flags':flags,'head_order':perm},ww

start=time.monotonic();best=999;selected=[];hist=collections.Counter()
for meta,word in variants():
 n=instantiate(word);hist[n]+=1
 if n<best:
  best=n;print('new DAG best',best,meta,'seconds',time.monotonic()-start,flush=True)
 if n<=69:selected.append((n,meta,word))
print('screened',sum(hist.values()),'hist',sorted(hist.items()),'selected',len(selected),'seconds',time.monotonic()-start,flush=True)
(OUT/'screen.json').write_text(json.dumps({'histogram':hist,'best_DAG':best,'selected':len(selected)},indent=2))

best_eff=62;found=[]
for j,(n,meta,word)in enumerate(sorted(selected,key=lambda x:x[0])):
 _,t=instantiate(word,True);rows,index,shape=build(t)
 ops=opportunities_fast(rows,shape);match=max_matching(ops);eff=n-len(match)
 if eff<=best_eff:
  if eff<best_eff:best_eff=eff;print('new EFFECTIVE best',eff,'DAG',n,'folds',len(match),meta,'seconds',time.monotonic()-start,flush=True)
  if eff<62:
   name=f'candidate_{len(found):03}_{eff}'
   (OUT/(name+'.grammar.json')).write_text(json.dumps(encode(t),indent=2))
   rec={'name':name,'effective':eff,'DAG':n,'folds':match,'meta':meta}
   found.append(rec);(OUT/'candidates.json').write_text(json.dumps(found,indent=2))
 if j%100==0:print('fold check',j,'of',len(selected),'best',best_eff,'seconds',time.monotonic()-start,flush=True)
print('done effective',best_eff,'found',len(found),'seconds',time.monotonic()-start,flush=True)
