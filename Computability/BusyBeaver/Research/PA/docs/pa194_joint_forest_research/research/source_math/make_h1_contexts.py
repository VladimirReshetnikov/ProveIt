from make_dup_seeds import *
from functools import lru_cache
OUT=HERE/'global_search'
I=lambda a,b:('I',a,b)
U=lambda a,b:('U',a,b)
N=lambda a:('N',a)
def emit(t):
 if isinstance(t,str):return [{'D':'node55','H':'node58','A':'node70','Z':'node49'}[t]]
 if t[0]=='N':return emit(t[1])+['node49',INC,'node65']
 _,a,b=t
 if t[0]=='U':return emit(b)+emit(a)+['node65',INC,INC]
 return emit(a)+emit(b)+['node65']
def head(f):return I(N(U('D',N(U('D',f)))),f)
@lru_cache(None)
def forms(n):
 if n==1:return ('A','H')
 return tuple(I(a,b)for k in range(1,n)for a in forms(k)for b in forms(n-k))
def val(t,a,h):return {'A':a,'H':h}[t] if isinstance(t,str)else(not val(t[1],a,h))or val(t[2],a,h)
# Every context retained has a displayed substitution reducing classically toH.
contexts=[]
for n in range(2,6):
 for t in forms(n):
  if not val(t,False,False):contexts.append((t,'A=H'))
  elif not val(t,True,False):contexts.append((t,'A=0'))
print('contexts',len(contexts),flush=True)
seeds=[];info=[]
for sn,s in enumerate(shapes):
 w=word(s);assert w[18:35]==emit(head('H'))
 for f,subst in contexts:
  nw=w[:18]+emit(head(f))+w[35:];seeds.append(adapt(s,nw));info.append(dict(shape=sn,formula_context=f,recovery_substitution=subst,tokens=len(nw)))
# Inherit exact136fixedforest, change operand macro label.
f=(OUT/'original.templates.txt').open();nb=int(next(f));fixed=[str(nb)]+[next(f).rstrip()for _ in range(nb)]
MACROS['node75']=332
text=fixed+[str(len(seeds))]
for tid,t in enumerate(seeds):
 ns,root=tarray(t);text.append(f'{tid} {len(ns)} {root}');text.extend(' '.join(map(str,row))for row in ns)
(OUT/'h1_context.templates.txt').write_text('\n'.join(text)+'\n');(OUT/'h1_context.seeds.json').write_text(json.dumps(info,indent=2)+'\n');print('seeds',len(seeds))
