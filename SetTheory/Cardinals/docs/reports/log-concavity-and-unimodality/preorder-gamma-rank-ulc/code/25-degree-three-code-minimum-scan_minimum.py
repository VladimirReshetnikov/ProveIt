import json,csv,math,time
from pathlib import Path
P=Path(__file__).parent
D=Path(__file__).resolve().parent.parent
def compositions(n,d):
 if d==1:yield(n,);return
 for i in range(n+1):
  for z in compositions(n-i,d-1):yield(i,)+z

def discriminant(a,b,c):return a*a*b*b-4*b*b*b-4*a*a*a*c-27*c*c+18*a*b*c

def coeffs(t,pop):
 return [sum(v*math.prod(math.comb(n,r) if n>=r else 0 for n,r in zip(pop,q)) for q,v in terms) for terms in t['gamma_binomial']]

def arcs(t,pop):
 out=[tuple(e) for e in t['core_arcs']];next_v=3
 for mask,c in zip(t['types'],pop):
  for v in range(next_v,next_v+c):
   for i in range(3):
    if mask>>i&1:out.append((i,v) if t['signs'][i]==-1 else(v,i))
  next_v+=c
 return sorted(out)

T=json.load(open(D/'cover3_seventeen_templates.json'));report={'cover3':{},'a1':{}};start=time.time()
for n in range(3,16):
 tested=degree3=bad=0;best=None
 for t in T:
  for pop in compositions(n-3,len(t['types'])):
   tested+=1;g=coeffs(t,pop)
   if not g[3]:continue
   degree3+=1;disc=discriminant(*g[1:])
   if disc<0:
    bad+=1
    if best is None or disc<best['discriminant']:best=dict(n=n,template=t['id'],population=pop,gamma=g,discriminant=disc,arcs=arcs(t,pop))
 report['cover3'][n]=dict(tested=tested,degree3=degree3,negative_discriminants=bad,best=best)
 print('cover3',n,report['cover3'][n],flush=True)
 (P/'minimum_scan.json').write_text(json.dumps(report,indent=2)+'\n')
for row in csv.DictReader(open(P/'a1_min_size_pairs.csv')):
 p1,p2,p3,q1,q2,n,v=[int(row[k])for k in ['p1','p2','p3','q1','q2','n','v']]
 for m in range(16-n):
  N=n+m;g=[1,p1+m,p2+m*q1,p3+m*q2]
  r=report['a1'].setdefault(N,dict(tested=0,degree3=0,negative_discriminants=0,best=None));r['tested']+=1
  if not g[3]:continue
  r['degree3']+=1;disc=discriminant(*g[1:])
  if disc<0:
   r['negative_discriminants']+=1
   if r['best'] is None or disc<r['best']['discriminant']:
    rows=list(map(int,row['rowmasks'].split()));es=[(i,j)for i,a in enumerate(rows)for j in range(n)if a>>j&1]+[(v,j)for j in range(n,N)]
    r['best']=dict(n=N,core_n=n,mark=v,population=m,gamma=g,discriminant=disc,arcs=es)
report['seconds']=time.time()-start
(P/'minimum_scan.json').write_text(json.dumps(report,indent=2)+'\n')
for n,r in sorted(report['a1'].items()):print('a1',n,r,flush=True)
