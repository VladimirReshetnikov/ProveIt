import json,math,time
from pathlib import Path
P=Path(__file__).parent
T=json.load(open(P.parent/'two-attachment/templates.json'))['templates']
def comps(n,d):
 if not d:
  if not n:yield ()
  return
 if d==1:yield(n,);return
 for i in range(n+1):
  for z in comps(n-i,d-1):yield(i,)+z

def disc(a,b,c):return a*a*b*b-4*b**3-4*a**3*c-27*c*c+18*a*b*c
report={};start=time.time()
for N in range(2,16):
 r=dict(tested=0,degree3=0,negative_discriminants=0,best=None)
 for t in T:
  n=len(t['core_rows'])
  if n>N:continue
  for pop in comps(N-n,len(t['types'])):
   r['tested']+=1
   g=[sum(v*math.prod(math.comb(a,b)if a>=b else 0 for a,b in zip(pop,q))for q,v in terms)for terms in t['gamma']]
   if not g[3]:continue
   r['degree3']+=1;d=disc(*g[1:])
   if d<0:
    r['negative_discriminants']+=1
    if r['best'] is None or d<r['best']['discriminant']:
     es=[(i,j)for i,row in enumerate(t['core_rows'])for j in range(n)if row>>j&1];v=n
     for mask,c in zip(t['types'],pop):
      for u in range(v,v+c):
       for i in range(2):
        if mask>>i&1:es.append((i,u)if t['signs'][i]==-1 else(u,i))
      v+=c
     r['best']=dict(n=N,template=t['id'],population=pop,gamma=g,discriminant=d,arcs=es)
 report[N]=r;print(N,r,flush=True)
 (P/'a2_minimum_scan.json').write_text(json.dumps(report,indent=2)+'\n')
print('seconds',time.time()-start)
