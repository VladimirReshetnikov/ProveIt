import sys,json,pathlib,functools,itertools
P=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(P/'vendor'))
import compiler as c
K=int(sys.argv[1]);out=pathlib.Path(sys.argv[2]);rows={}
for l in (P/'runtime193.native.tm').read_text().splitlines():
 q,b,w,d,t=l.split();rows[int(q),int(b)]=(int(w),d=='R',int(t))
sites,ins,cs=c.source(c.read_grammar(P/'pa194.grammar.json'))
@functools.lru_cache(None)
def prefixes(s,k):
 if k==0:return ((),)
 if not s:return ((0,)*k,)
 x,*tail=s;tail=tuple(tail)
 if x[0]=='b':return tuple((x[1],)+p for p in prefixes(tail,k-1))
 if x[0]=='x':
  if k>16:raise ValueError(('TOO MUCH FILE',s,k))
  return tuple(itertools.product((0,1),repeat=k))
 if x[0]=='r':
  _,b,a,d=x
  if a==0:
   if d>=k:return ((b,)*k,)
   return tuple((b,)*d+p for p in prefixes(tail,k-d))
  ret=set()
  for n in range(k+1):
   size=a*n+d
   if size>=k:ret.add((b,)*k);break
   for p in prefixes(tail,k-size):ret.add((b,)*size+p)
  return tuple(ret)
 raise ValueError(x)
seen=set();pat=set()
def obs(s):
 q,onl,l,r=s
 if q not in (122,137):return
 if c.headbit(l if onl else r)!=0:return
 if s in seen:return
 seen.add(s)
 lp=prefixes(l,K+1 if onl else K);rp=prefixes(r,K if onl else K+1)
 for a,b in itertools.product(lp,rp):
  tape=tuple(reversed(a[1:]))+(a[0],)+b if onl else tuple(reversed(a))+b
  assert len(tape)==2*K+1
  pat.add((q,sum(bit<<i for i,bit in enumerate(tape))))
result=c.validate(rows,cs,observe=obs)
out.write_text(''.join(f'{q} {p}\n' for q,p in sorted(pat)))
print(json.dumps(dict(validation=result,radius=K,symbolic_configs=len(seen),contexts=len(pat))))
