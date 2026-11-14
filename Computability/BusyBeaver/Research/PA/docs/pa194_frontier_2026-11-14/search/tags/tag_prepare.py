from pathlib import Path
import json,sys,collections,itertools,os,tempfile
ROOT=Path(__file__).resolve().parent
base=ROOT/'reference'
sys.path.insert(0,str(base/'construction'))
import compiler as c
INC=('leaf','inc',1)
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
raw={}
for ln in (base/'inputs/primary.raw.native.tm').read_text().splitlines():
 q,b,w,d,n=ln.split();raw[int(q),int(b)]=(int(w),d=='R',int(n))
ns={k:tup(v)for k,v in json.loads((base/'inputs/primary.nodes.json').read_text()).items()}
c.machine=lambda:(raw,[]);c.raw_nodes=lambda:ns
c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
g=c.read_grammar(base/'inputs/primary.grammar.json')
def flat(t):return flat(t[0])+flat(t[1]) if c.isnode(t)else([INC,INC]if t=='node60'else [t])
w=flat(g)
print('baseword',len(w),collections.Counter(w))
def dumpgrammar(t,p):
 rules={};idx={}
 def enc(t):
  if not c.isnode(t):return t
  if t in idx:return idx[t]
  name='g'+str(len(idx));idx[t]=name
  rules[name]=[enc(t[0]),enc(t[1])];return name
 p.write_text(json.dumps({'root':enc(t),'rules':rules}))
def mutate(t,edits):
 i=0
 def go(t):
  nonlocal i
  if c.isnode(t):
   l,r=go(t[0]),go(t[1]);return (l,r)if l and r else l or r
  if t=='node60':return go((INC,INC))
  z=edits.get(i,t);i+=1;return z
 ans=go(t);assert i==len(w);return ans

def variant(u,e):
 edits={};nblocks=collections.Counter()
 for i,t in enumerate(w):
  if t not in ('node65','node75'):continue
  j=i+1
  while j<len(w)and w[j]==INC:j+=1
  r=j-i-1
  if r in(2,3):
   new={2:u,3:e}[r];nblocks[r]+=1
   if new<r:
    for z in range(i+1+new,j):edits[z]=None
   elif new>r:
    ext=INC
    for _ in range(new-r):ext=(INC,ext)
    edits[j-1]=ext
 gg=mutate(g,edits);ww=flat(gg)
 return gg,ww,dict(nblocks)

def freecheck(ww,k,u,e,generalizer=False,q=False):
 ZERO=('zero',);ONE=('succ',ZERO)
 def S(x):return('succ',x)
 def rep(x,n):
  for _ in range(n):x=S(x)
  return x
 def I(a,b):return('I',k,a,b)
 def M(a,b):return S(I(a,b))
 def U(a,b):return rep(I(b,a),u)
 def E(a,b):return rep(I(a,b),e)
 def N(b):return I(b,ONE)
 def A(a,b):return N(I(a,N(b)))
 def X(a,b):return N(U(a,N(b)))
 oldt,a,d,h,y,x=(('atom',z)for z in('t','a','d','h','y','x'))
 T,D,H=oldt,d,h;stack=[];fields=[y,x]
 for op in ww[:-3]:
  if op=='node49':stack.append(T);T=ZERO
  elif op in('node55','node58','node70'):stack.append(T);T={'node55':D,'node58':H,'node70':a}[op]
  elif op=='node65':T=I(stack.pop(),T)
  elif op==INC:T=S(T)
  elif op=='node72':H=('add',H,fields.pop(0))
  elif op=='node75':D=('add',D,fields.pop(0));T=I(T,D)
  else:raise ValueError(op)
 heads=[I(X(D,U(D,H)),H),I(U(D,U(a,H)),U(a,U(D,H))),I(M(H,D),I(E(H,a),M(a,D))),I(E(H,D),I(M(a,H),M(a,D))),X(D,E(H,D)),I(U(D,a),I(U(D,I(a,H)),U(D,H)))]
 if q:heads[-1]=I(U(D,I(a,H)),I(U(D,a),U(D,H)))
 rho=I(I(I(H,d),D),I(I(D,H),I(a,H)));gamma=I(a,U(a,a));v=I(M(H,D),U(a,M(H,D)))
 point=I(a,M(a,D));sep=U(D,A(I(M(H,D),point),I(M(a,D),a)));Q=U(a,I(sep,N(point)))
 assert not fields;assert stack==[oldt,U(a if generalizer else d,h),rho]+heads+[gamma],(u,e,'stack');assert T==N(I(v,Q)),(u,e,'top')
 return True

out=Path(os.environ.get('PA_RESEARCH_OUTPUT') or tempfile.mkdtemp(prefix='pa-tags-'));out.mkdir(parents=True,exist_ok=True)
manifest=[]
for u,e in [(3,2),(2,4),(4,2),(4,3),(3,4)]:
 gg,ww,changes=variant(u,e)
 assert freecheck(ww,max(u,e)+1,u,e)
 p=out/f'u{u}e{e}';p.mkdir(exist_ok=True)
 dumpgrammar(gg,p/'grammar.json');(p/'word.json').write_text(json.dumps(ww))
 # baseline literal macro expansion only; k engine currently4 for screeninggrammar
 rr,index,shape=c.build(gg);ops=c.opportunities_fast(rr,shape);match=c.max_matching(ops)
 result={'u':u,'e':e,'tokens':len(ww),'retagged_blocks':changes,'raw_readers':len(shape),'AXfold_bound':len(match),'optimistic_total':134+len(shape)-len(match),'freecheck':True}
 manifest.append(result);print(result)
(out/'manifest.json').write_text(json.dumps(manifest,indent=2))
