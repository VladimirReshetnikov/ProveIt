import sys,json
from pathlib import Path
from functools import lru_cache
source=Path(sys.argv[1]);d=json.loads(source.read_text());target=int(sys.argv[2])if len(sys.argv)>2 else 6
B=Path(__file__).resolve().parent/'reference_data';s=json.loads((B/'reference/grammar/closed-sequence-grammar-next22.json').read_text());sym=json.loads((B/'reference/grammar/semantic-symbols.json').read_text());enc=json.load(open(Path(__file__).resolve().parent/'inputs/canonical-map.json'))['physical_atoms'];canon=lambda w:''.join(enc[c]for c in w)
ls=(B/'reference/grammar/semantic.txt').read_text().splitlines();n,nr,na=map(int,ls[0].split());old={canon(w):(canon(w[:int(k)]),canon(w[int(k):]))for k,w,q in map(str.split,ls[1:n+1])};names={int(q):canon(w)for k,w,q in map(str.split,ls[1:n+1])};mask={enc[c]:int(m)for c,m in map(str.split,ls[n+1+nr:])};term={enc[c]:s['atoms'][k]['ast']for c,k in sym.items()};byast={int(v):d.get('source_replacements',{}).get(names[int(q)],names[int(q)])for q,v in s['sequence_ast_roots'].items()}
locks=[w.split()for w in (Path(__file__).resolve().parent/'inputs/canonical-lock50.txt').read_text().splitlines()[1:]]
ls=(Path(__file__).resolve().parent/'inputs/canonical-constraints.txt').read_text().splitlines();ng=int(ls[0]);i=1;groups=[]
for _ in range(ng):
 src,read,w,n=ls[i].split();i+=1;cs=[]
 for _ in range(int(n)):
  p,t=ls[i].split();i+=1;cs.append((p,t))
 groups.append((int(src),int(read),cs))
def props(g):
 def join(a,b):return a[0]+1,max(a[0]+1,a[1],b[1]),1+max(a[2],b[2]),a[3]+b[3]+(a[0]+1>target)
 @lru_cache(None)
 def wp(w):return ep(term[w])if w in term else join(*(wp(x)for x in g.get(w,old.get(w))))
 @lru_cache(None)
 def ep(i):
  if i in byast:return wp(byast[i])
  r=s['ast_dag'][i];return (0,0,0,0)if r[0]=='L'else join(ep(r[1]),ep(r[2]))
 return ep(s['original_ast'])
def permitted(a,b):return(a not in term or mask[a]&1)and(b not in term or mask[b]&2)
def project(g,w,p):
 for b in p:
  if w not in g:return None
  w=g[w][int(b)]
 return w
def close(g,routes):
 if any(project(g,w,b)!=t for w,b,t in locks):return None
 newroutes=[]
 for src,read,cs in groups:
  current=next(r['word']for r in routes if (r['source'],r['read'])==(src,read))
  good=lambda w:all(project(g,w,p)==t for p,t in cs)
  if not good(current):current=next((w for w in g if good(w)),None)
  if current is None:return None
  newroutes.append(dict(source=src,read=read,word=current))
 seen=set()
 def visit(w):
  if w in term or w in seen:return
  if w not in g:raise ValueError(w)
  seen.add(w)
  for x in g[w]:visit(x)
 for w in d['roots']+[r['word']for r in newroutes]:visit(w)
 return {w:g[w]for w in seen},newroutes
current={w:(a,b)for w,a,b in d['rules']};routes=d['routes'];p=props(current);print('initial',len(current),p,flush=True)
for step in range(20):
 best=(len(current)+10*p[3],current,routes,p)
 for w,(a,b)in current.items():
  for side in (0,1):
   child=(a,b)[side]
   if child not in current:continue
   if side==0:x,y=current[a];z=b;part=y+z;rule=(x,part);pr=(y,z)
   else:x=a;y,z=current[b];part=x+y;rule=(part,z);pr=(x,y)
   if not permitted(*rule):continue
   g=dict(current)
   if part not in term and part not in g:
    if not permitted(*pr):continue
    g[part]=pr
   g[w]=rule
   answer=close(g,routes)
   if answer is None:continue
   g,rt=answer;q=props(g)
   if q[2]>64:continue
   score=len(g)+10*q[3]
   if score<best[0]-1e-8:best=score,g,rt,q
 if best[1]is current:break
 _,current,routes,p=best;print('step',step,len(current),p,flush=True)
 if p[3]==0:break
out=dict(d,rules_count=len(current),rules=[[w,*ab]for w,ab in sorted(current.items())],routes=routes,properties=list(p));Path(str(source).replace('.json','-repaired.json')).write_text(json.dumps(out,indent=2)+'\n')
