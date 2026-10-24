"""Exact sign inference for finite quadratic residual systems."""
from math import isqrt
from collections import Counter,defaultdict,deque

def square_root(poly):
 diag=sorted((m[0],c) for m,c in poly.items() if len(m)==2 and m[0]==m[1] and c>0)
 if not diag:return None
 v,c=diag[0];r=isqrt(c)
 if r*r!=c:return None
 out={(v,):r}
 for u in sorted({u for m in poly for u in m}-{v}):
  val=poly.get(tuple(sorted((u,v))),0)
  if val%(2*r):return None
  if val:out[(u,)]=val//(2*r)
 val=poly.get((v,),0)
 if val%(2*r):return None
 if val:out[()]=val//(2*r)
 sq=defaultdict(int)
 for m,a in out.items():
  for n,b in out.items():sq[tuple(sorted(m+n))]+=a*b
 return out if {m:c for m,c in sq.items() if c}==poly else None

def infer_nonnegativity(equation):
    vs=equation["variables"];rows=equation["residuals"]
    rules=[]
    for rid,row in enumerate(rows):
     p={tuple(m):c for c,m in row['terms']}
     for (v,),coef in [(m,c) for m,c in p.items() if len(m)==1]:
      rest={m:-c*(1 if coef>0 else -1) for m,c in p.items() if m!=(v,)}
      if any(v in m for m in rest):continue
      sqrt=None
      if all(c>=0 for c in rest.values()):
       deps={k for m in rest for k,e in Counter(m).items() if e%2};kind='positive_monomials'
      else:
       sqrt=square_root(rest)
       if sqrt is None:continue
       deps=set();kind='affine_square'
      rules.append((v,deps,rid,abs(coef),rest,kind,sqrt))
    rev=defaultdict(list)
    for k,(_,deps,*_) in enumerate(rules):
     for d in deps:rev[d].append(k)
    def closure(seed):
     known=set(seed);pending=[len(deps-known) for v,deps,*_ in rules];q=deque(i for i,n in enumerate(pending) if n==0);proof=[]
     while q:
      k=q.popleft();v,deps,rid,c,rest,kind,sqrt=rules[k]
      if v in known:continue
      known.add(v);step={'variable':v,'name':vs[v]['name'],'row':rid,'coefficient':c,'dependencies':sorted(deps),'rhs':[[a,list(m)] for m,a in sorted(rest.items())],'kind':kind}
      if sqrt is not None:step['square_root']=[[a,list(m)] for m,a in sorted(sqrt.items())]
      proof.append(step)
      for k2 in rev[v]:
       pending[k2]-=1
       if pending[k2]==0:q.append(k2)
     return known,proof
    seed={i for i,v in enumerate(vs) if v['kind'] not in ('gate','square_difference')};initial=len(seed)
    if len(closure(seed)[0])!=len(vs):raise ValueError('gate inference incomplete')
    for i in sorted(seed,reverse=True):
     if len(closure(seed-{i})[0])==len(vs):seed.remove(i)
    known,proof=closure(seed)
    return {'initial_guards':initial,'retained_guards':len(seed),
            'variables_proved_nonnegative':len(known),'guard_indices':sorted(seed),
            'removed_guard_indices':[i for i,v in enumerate(vs)
                if v['kind'] not in ('gate','square_difference') and i not in seed],
            'proof_steps':proof}
