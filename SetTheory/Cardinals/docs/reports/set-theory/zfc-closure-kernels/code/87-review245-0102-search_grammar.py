"""Independently authored SLP checker/search. Repository inputs are parsed only as data."""
import json,functools,collections,random,time,pathlib,sys,os
if not __debug__: raise RuntimeError("Assertions must remain enabled")
BASE=pathlib.Path(os.environ.get('B245_INPUTS',str(pathlib.Path(__file__).resolve().parent.parent/'inputs')))
OUT=pathlib.Path(os.environ.get('B245_OUTPUTS',str(pathlib.Path(__file__).resolve().parent)))
OUT.mkdir(parents=True,exist_ok=True)
G=json.loads((BASE/'candidate-routing245/grammar.json').read_text())
R={w:(a,b)for w,a,b in G['rules']}
lines=(BASE/'inputs__semantic.txt').read_text().splitlines();n,nr,na=map(int,lines[0].split());OLD={};names={}
for line in lines[1:n+1]:
 k,w,s=line.split();k=int(k);OLD[w]=(w[:k],w[k:]);names[int(s)]=w
ALLOWED={a:int(b)for a,b in map(str.split,lines[n+nr+1:])}
locks=[line.split() for line in (BASE/'inputs__state_reduction__bootstrap-lock54.txt').read_text().splitlines()[1:]]
ls=(BASE/'inputs__state_reduction__route-constraints.txt').read_text().splitlines();ng=int(ls[0]);p=1;CON=[]
for _ in range(ng):
 q,b,word,m=ls[p].split();p+=1
 for i in range(int(m)):
  bits,target=ls[p].split();p+=1;CON.append((int(q),int(b),bits,target))
nast,root,na=map(int,ls[p].split());p+=1
AST=[l.split() for l in ls[p:p+nast]];p+=nast
ATOM={a:int(b)for a,b in map(str.split,ls[p:])};assert len(ATOM)==na
ROOTS=set(G['roots'])|{r['word']for r in G['routes']}
ROUTES={(x['source'],x['read']):x['word']for x in G['routes']}

def props(R):
 @functools.lru_cache(None)
 def ast(i):
  z=AST[i]
  if z[0]=='L':return 0,0,0
  if z[0]=='W':return word(z[1])
  return join(ast(int(z[1])),ast(int(z[2])))
 @functools.lru_cache(None)
 def word(w):
  if len(w)==1:return ast(ATOM[w])
  a,b=R.get(w,OLD.get(w,(None,None)))
  assert a is not None,w
  return join(word(a),word(b))
 def join(a,b):return 1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2])
 return ast(root)

def reached(R):
 seen=set()
 def v(w):
  if len(w)==1 or w in seen:return
  assert w in R,w
  seen.add(w)
  for c in R[w]:v(c)
 for w in ROOTS:v(w)
 return seen

def validate(R):
 for w,ab in R.items():
  assert ''.join(ab)==w
  for bit,c in enumerate(ab):
   assert len(c)>0 and (c in R if len(c)>1 else ALLOWED[c]&(1<<bit)),(w,bit,c)
 for w,bit,target in locks:assert R[w][int(bit)]==target,(w,bit,target)
 for q,b,bits,target in CON:
  w=ROUTES[q,b]
  for bit in bits:w=R[w][int(bit)]
  assert w==target,(q,b,bits,w,target)
 return props(R)

def save(R,tag):
 x=dict(G);x['rules_count']=len(R);x['rules']=[[w,*ab]for w,ab in sorted(R.items())];x['properties']=list(props(R));x['status']='INDEPENDENT_GRAMMAR_SEARCH_NOT_RUNTIME_CERTIFIED'
 (OUT/(tag+'.json')).write_text(json.dumps(x,indent=2)+'\n')

if __name__=='__main__':
 print('baseline',len(R),validate(R))
 RR=dict(R);RR['eijkKCeijkfg']=('eijkKC','eijkfg');del RR['KCeijkfg']
 try: print('127 simple',len(RR),validate(RR));save(RR,'simple-127')
 except Exception as e: print('127 simple FAILED',repr(e))

def search(seconds=120,seed=1):
 random.seed(seed);cur=dict(R);best=len(cur);t0=time.monotonic();iters=accepted=0
 locked={w for w,_,_ in locks}
 while time.monotonic()-t0<seconds:
  iters+=1
  x=random.choice(tuple(cur));a,b=cur[x];di=random.randrange(2)
  if x in locked:continue
  if di==0:
   if a not in cur:continue
   u,v=cur[a];new=v+b;ab=(u,new);cd=(v,b)
  else:
   if b not in cur:continue
   u,v=cur[b];new=a+u;ab=(new,v);cd=(a,u)
  if ab==cur[x]:continue
  rr=dict(cur);rr[x]=ab
  if new not in rr:rr[new]=cd
  try:
   pp=validate(rr)
   if pp[1]>6 or pp[2]>64:continue
   live=reached(rr);rr={w:ab for w,ab in rr.items()if w in live}
  except (AssertionError,KeyError):continue
  delta=len(rr)-len(cur);temp=0.15
  if delta>0 and random.random()>__import__('math').exp(-delta/temp):continue
  cur=rr;accepted+=1
  if len(cur)<best:
   best=len(cur);save(cur,f'search-{seed}-{best}');print('BEST',best,pp,iters,accepted,round(time.monotonic()-t0,3),flush=True)
   if best<=127:return cur
  if iters%10000==0:print('PROGRESS',iters,accepted,len(cur),best,round(time.monotonic()-t0,3),flush=True)
 print('DONE',iters,accepted,len(cur),best,flush=True)
 return cur
if __name__=='__main__' and len(sys.argv)>1:search(float(sys.argv[1]),int(sys.argv[2])if len(sys.argv)>2 else 1)
