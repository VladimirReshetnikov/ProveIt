import json,csv,math,itertools,hashlib
from pathlib import Path
P=Path(__file__).resolve().parents[1];D=P.parent;O=P/'independent-audit'
def populations(bound,d):
 if d==0:
  yield ()
 else:
  for x in range(bound+1):
   for tail in populations(bound-x,d-1):yield (x,)+tail

def discr(g):
 _,a,b,c=g
 # Resultant-form independent rearrangement of cubic discriminant
 return b*b*(a*a-4*b)+c*(18*a*b-4*a*a*a-27*c)
def evaluate(poly,pop):
 out=[]
 for coeffs in poly:
  s=0
  for ex,c in coeffs:
   for n,k in zip(pop,ex):c*=math.comb(n,k) if n>=k else 0
   s+=c
  out.append(s)
 return out

def scan(name,templates):
 counts={};bad=[]
 for ident,n,types,poly in templates:
  for pop in populations(15-n,len(types)):
   N=n+sum(pop);g=evaluate(poly,pop);r=counts.setdefault(N,[0,0,0]);r[0]+=1
   if g[3]:
    r[1]+=1
    if discr(g)<0:r[2]+=1;bad.append(dict(template=ident,n=N,population=pop,gamma=g,discriminant=discr(g)))
 return dict(counts=counts,totals=[sum(r[i]for r in counts.values())for i in range(3)],negative=bad)
T=json.load(open(D/'cover3_seventeen_templates.json'))
report={'cover3':scan('cover3',[(t['id'],3,t['types'],t['gamma_binomial'])for t in T])}
T2=json.load(open(D/'two-attachment/templates.json'))['templates']
report['a2']=scan('a2',[(t['id'],len(t['core_rows']),t['types'],t['gamma'])for t in T2])
counts={};bad=[]
for row in csv.DictReader(open(O/'a1_pairs.csv')):
 n=int(row['n']);p=list(map(lambda k:int(row[k]),['p1','p2','p3']));q=list(map(lambda k:int(row[k]),['q1','q2']))
 for m in range(16-n):
  N=n+m;g=[1,p[0]+m,p[1]+m*q[0],p[2]+m*q[1]];r=counts.setdefault(N,[0,0,0]);r[0]+=1
  if g[3]:
   r[1]+=1
   if discr(g)<0:r[2]+=1;bad.append((n,m,g))
report['a1']=dict(counts=counts,totals=[sum(r[i]for r in counts.values())for i in range(3)],negative=bad)
old={tuple(int(r[k])for k in ['p1','p2','p3','q1','q2']):int(r['n']) for r in csv.DictReader(open(D/'one-attachment/pairs.csv'))}
new={tuple(int(r[k])for k in ['p1','p2','p3','q1','q2']):int(r['n']) for r in csv.DictReader(open(O/'a1_pairs.csv'))}
assert old==new
report['a1_minimum_sizes']=dict(keys=len(new),all_stored_sizes_minimal=True)
for branch,fn in [('cover3','minimum_scan.json'),('a1','minimum_scan.json'),('a2','a2_minimum_scan.json')]:
 prior=json.load(open(P/fn)); prior=prior[branch]if branch!='a2'else prior
 for n,r in report[branch]['counts'].items():
  assert r==[prior[str(n)][k]for k in ['tested','degree3','negative_discriminants']],(branch,n)
report['agrees_with_original_scan']=True
(O/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:{a:b for a,b in v.items()if a!='counts'}if isinstance(v,dict)else v for k,v in report.items()},indent=2))
