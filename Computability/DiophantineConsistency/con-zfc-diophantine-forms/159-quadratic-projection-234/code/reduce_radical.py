"""Exact integral projection of quadratic systems along common Hessian radicals."""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction
from math import gcd,lcm
import json,sys,hashlib,copy,time

def norm(ts):
 d=defaultdict(int)
 for c,m in ts:d[tuple(sorted(m))]+=c
 return {m:c for m,c in d.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def scale(p,a):return {m:a*c for m,c in p.items() if a*c}
def mul(p,q):
 d=defaultdict(int)
 for a,c in p.items():
  for b,e in q.items():d[tuple(sorted(a+b))]+=c*e
 return {m:c for m,c in d.items() if c}
def V(i):return {(i,):1}
def subst(p,mapping):
 out={}
 for m,c in p.items():
  part={():c}
  for j in m:part=mul(part,mapping.get(j,V(j)))
  out=add(out,part)
 return out
def canonical(o):return (json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(o):return hashlib.sha256(canonical(o)).hexdigest()
def radicals(eq):
 n=len(eq['variables']);rows={}
 for row in eq['residuals']:
  h=defaultdict(lambda:defaultdict(int))
  for c,m in row['terms']:
   if len(m)==2:
    i,j=m;h[i][j]+=c;h[j][i]+=c
  for coeff in h.values():
   d={k:Fraction(v) for k,v in coeff.items() if v}
   while d:
    j=min(d)
    if j not in rows:
     c=d[j];rows[j]={k:v/c for k,v in d.items()};break
    c=d.pop(j)
    for k,v in rows[j].items():
     if k==j:continue
     a=d.get(k,Fraction(0))-c*v
     if a:d[k]=a
     else:d.pop(k,None)
 free=[j for j in range(n) if j not in rows];out=[]
 for j in free:
  v=[Fraction(0)]*n;v[j]=Fraction(1)
  for k,r in sorted(rows.items(),reverse=True):v[k]=-sum(c*v[i] for i,c in r.items() if i!=k)
  den=lcm(*(q.denominator for q in v));w=[int(x*den) for x in v];g=gcd(*w);out.append([x//g for x in w])
 return out

def project(eq,v,p,rid):
 n=len(v)
 if v[p]==-1:v=[-x for x in v]
 if v[p]!=1:raise ValueError('nonunit pivot')
 shear={i:add(V(i),{(p,):c}) for i,c in enumerate(v) if c and i!=p}
 rows=[subst(norm(r['terms']),shear) for r in eq['residuals']]
 if any(len(m)>1 and p in m for r in rows for m in r):raise ValueError('not radical')
 a=rows[rid].get((p,),0)
 if a not in (-1,1):raise ValueError('nonunit slope')
 solve=scale({m:c for m,c in rows[rid].items() if m!=(p,)},-a)
 keep=[i for i in range(n) if i!=p];ren={k:j for j,k in enumerate(keep)}
 new=copy.deepcopy(eq);new['variables']=[copy.deepcopy(eq['variables'][i]) for i in keep]
 for i in keep:
  if v[i]:new['variables'][ren[i]]['name']=f"radical{n}.{i}"
 newrows=[]
 for j,row in enumerate(rows):
  if j==rid:continue
  out=subst(row,{p:solve})
  if any(len(m)>2 for m in out):raise ValueError('degree increase')
  if any(p in m for m in out):raise ValueError('pivot remains')
  newrows.append(dict(eq['residuals'][j],terms=terms({tuple(ren[i] for i in m):c for m,c in out.items()})))
 new['residuals']=newrows;new.pop('metrics',None)
 new['variant']=eq.get('variant','')+':radical_projection'
 cert={'input_sha256':digest(eq),'direction':[[i,c] for i,c in enumerate(v) if c],
       'pivot':p,'pivot_name':eq['variables'][p]['name'],'deleted_row':rid,'slope':a,
       'sheared_pivot_solution':terms(solve),'retained_old_indices':keep,'output_sha256':digest(new)}
 return new,cert

def metric(eq,expand=False):
 ps=[norm(r['terms']) for r in eq['residuals']]
 d={'variables':len(eq['variables']),'rows':len(ps),'residual_terms':sum(map(len,ps)),
 'row_height':max(abs(c) for p in ps for c in p.values())}
 if expand:
  pp=add(*(mul(p,p) for p in ps));d.update(degree=max(map(len,pp)),monomials=len(pp),height=max(map(abs,pp.values())))
 return d

def reduce(eq):
 cs=[];log=[]
 while True:
  vs=radicals(eq);cand=[]
  for k,v in enumerate(vs):
   slopes=[sum(norm(r['terms']).get((i,),0)*x for i,x in enumerate(v) if x) for r in eq['residuals']]
   for p,x in enumerate(v):
    if abs(x)!=1:continue
    for rid,a in enumerate(slopes):
     if abs(a)!=1:continue
     new,c=project(eq,v,p,rid);m=metric(new)
     score=(m['row_height'],m['residual_terms'],len(c['sheared_pivot_solution']),p,rid)
     cand.append((score,new,c,k))
  log.append({'n':len(eq['variables']),'radical_dimension':len(vs),'candidates':len(cand)})
  if not cand:break
  _,new,c,k=min(cand,key=lambda z:z[0]);print(log[-1],c['pivot_name'],c['deleted_row'],metric(new),flush=True)
  cs.append(c);eq=new
 return eq,{'schema':'common_hessian_radical_projection_v1','steps':cs,'search_log':log}

if __name__=='__main__':
 inp=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
 eq=json.loads(inp.read_text());new,cert=reduce(eq)
 for name,o in [('equation.json',new),('projection_certificate.json',cert),('metrics.json',metric(new,True))]:
  (out/name).write_bytes(canonical(o))
 pp=add(*(mul(norm(r['terms']),norm(r['terms'])) for r in new['residuals']))
 (out/'expanded_polynomial.json').write_bytes(canonical({'schema':'sparse_integer_polynomial_v1','variables':len(new['variables']),'terms':terms(pp)}))
 print(metric(new,True))
