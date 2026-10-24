import json, time, argparse
from collections import defaultdict, Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--source',type=Path,default=ROOT/'signed_quotients/candidate/equation.json')
parser.add_argument('--output',type=Path,default=Path(__file__).parent/'preliminary.json')
parser.add_argument('--seed-names',type=Path)
args=parser.parse_args()
P=json.loads(args.source.read_text())
V=P['variables'][:P['metrics']['core_variables']]
ROWS=P['residuals'][:P['metrics']['core_rows']]
N=len(V)
semantic={i for i,v in enumerate(V) if v['kind'] in ('outer','witness')}
signed={i for i,v in enumerate(V) if v['kind']=='signed_quotient'}
sym={i for i in semantic if V[i]['name'].endswith('.Z') or V[i]['name'].endswith('.pell.U')}

def canonical(p):
 d=defaultdict(int)
 for c,m in p:d[tuple(sorted(m))]+=c
 return [(c,m) for m,c in sorted(d.items()) if c]

rules=[]
by_dep=defaultdict(list)
for j,row in enumerate(ROWS):
 inds={x for c,m in row['terms'] for x in m}
 for x in sorted(inds-signed):
  if any(m.count(x)>1 for c,m in row['terms']):continue
  A=canonical([(c,[y for y in m if y!=x]) for c,m in row['terms'] if x in m])
  B=canonical([(-c,m) for c,m in row['terms'] if x not in m])
  if all(c<0 for c,m in A):A=[(-c,m) for c,m in A];B=[(-c,m) for c,m in B]
  if not A or any(c<0 for c,m in A):continue
  deps=set(y for p in (A,B) for c,m in p for y in m)
  idx=len(rules);rules.append((x,j,A,B,deps))
  for y in deps:by_dep[y].append(idx)

def translate(poly,lb):
 d=defaultdict(int)
 for c,m in poly:
  if len(m)==0:d[()]+=c
  elif len(m)==1:
   y=m[0];d[(y,)]+=c
   if lb[y]>0:d[()]+=c*lb[y]
  elif len(m)==2:
   y,z=m;d[(y,z)]+=c
   a=max(lb[y],0);b=max(lb[z],0)
   d[(y,)]+=c*b;d[(z,)]+=c*a;d[()]+=c*a*b
  else:raise ValueError('degree')
 return {m:c for m,c in d.items() if c}

def positive(poly,lb):
 d=translate(poly,lb)
 if any(c<0 for c in d.values()):return -1
 for m,c in d.items():
  odd=[y for y,z in Counter(m).items() if z%2]
  if any(lb[y]<0 for y in odd):return -1
 return 1 if d.get((),0)>0 else 0

def closure(seeds,record=False):
 lb=[-1]*N
 for i in seeds|sym:lb[i]=0
 queue=list(range(len(rules)));queued=set(queue);steps=[];q=0
 while q<len(queue):
  k=queue[q];q+=1;queued.discard(k)
  x,j,A,B,deps=rules[k]
  if lb[x]>=2:continue
  if positive(A,lb)!=1:continue
  b=positive(B,lb)
  if b<0:continue
  bound=b
  if b>=0 and positive(canonical(B+[(-c,m) for c,m in A]),lb)==1:bound=2
  if bound<=lb[x]:continue
  lb[x]=bound
  if record:steps.append({'variable':x,'lower_bound':bound,'row':j})
  for t in by_dep[x]:
   if t not in queued:queue.append(t);queued.add(t)
 return lb,steps

def run():
 seeds=semantic-sym
 if args.seed_names:
  names=json.loads(args.seed_names.read_text())
  lookup={v['name']:i for i,v in enumerate(V)}
  seeds={lookup[name] for name in names}
 lb,st=closure(seeds)
 print('initial closure',sum(x>=0 for x in lb),'rules',len(rules),'sym',len(sym),flush=True)
 t=time.time();removed=[]
 for count,i in enumerate([] if args.seed_names else sorted(seeds,reverse=True)):
  test=seeds-{i};lb,st=closure(test)
  if all(lb[x]>=0 for x in semantic):seeds=test;removed.append(i)
  if count%100==0:print('progress',count,'seeds',len(seeds),'sec',round(time.time()-t,2),flush=True)
 lb,st=closure(seeds,True)
 result={'seeds':sorted(seeds),'symmetry_coordinates':sorted(sym),'steps':st,'removed':removed,'bounds':lb}
 if not all(lb[x]>=0 for x in semantic):
  print('uncovered',[(x,V[x]['name']) for x in semantic if lb[x]<0])
  raise ValueError('mapped guards do not recover all semantic coordinates')
 args.output.write_text(json.dumps(result))
 print('final seeds',len(seeds),'removed',len(removed),'covered',sum(x>=0 for x in lb),'steps',len(st),'secs',time.time()-t,flush=True)
 print(Counter(V[x]['name'].rsplit('.',1)[-1] for x in removed))
if __name__=='__main__':run()
