"""Create physically oriented source candidates from certified AX symmetries.
The output is a candidate grammar and a source-word substitution, not a table.
"""
import sys,json,random,time
from functools import lru_cache
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(Path(__file__).resolve().parent))
import source_model as sm
B=ROOT/'reference_data';s=json.loads((B/'reference/grammar/closed-sequence-grammar-next22.json').read_text());ast=s['ast_dag'];cm=json.load(open(ROOT/'inputs/canonical-map.json'));base=json.load(open(ROOT/'candidates/canonical-20262021.json'));g={w:(a,b)for w,a,b in base['rules']};ax=max(base['roots'],key=len)
@lru_cache(None)
def bounds(i):
 r=ast[i]
 if r[0]=='L':
  op,*arg=r[1]
  return (1,0) if op=='dec' else (arg[0],0) if op=='brk' else (0,arg[0]) if op=='cont' else (0,0)
 a,b=bounds(r[1]),bounds(r[2]);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
@lru_cache(None)
def normal(i):
 r=ast[i]
 if r[0]=='L':return tuple([dict(dec='D',inc='I',brk='B',cont='C',halt='H')[r[1][0]]]+r[1][1:])
 a,b=r[1:];aa,bb=normal(a),normal(b)
 if bounds(a)==bounds(b)==(0,0):return ('S',*(aa[1:]if aa[0]=='S'else(aa,)),*(bb[1:]if bb[0]=='S'else(bb,)))
 return ('A',aa,bb)
normatom={normal(v):k for k,v in cm['fine_ast_ids'].items()}
assert len(normatom)==30
macro={k:''.join(normatom[t]for t in w)for k,w in sm.MACROS.items()}
def emit(row):return ''.join(macro[k]for k in sm.emit(row))
rows=[emit(row)for row in sm.ROWS[1:]];prefix=''.join(macro[k]for k in [166,121,180,176]);pre=prefix+''.join(rows)
assert ax.startswith(pre)
tail=ax[len(pre):]
ls=(ROOT/'inputs/canonical-grammar.txt').read_text().splitlines();n,nr,na=map(int,ls[0].split());terms={w:int(m)for w,m in map(str.split,ls[n+1+nr:])}
roots=(set(base['roots'])|{r['word']for r in base['routes']})-{ax}
def closure(seed,graph):
 out=set()
 def visit(w):
  if w in terms or w in out:return
  out.add(w)
  for c in graph[w]:visit(c)
 for w in seed:visit(w)
 return out
core=closure(roots,g);deps={w:closure([w],g)-core for w in g};print('core',len(core),'private',len(g)-len(core),'prefix',len(prefix),'rows',list(map(len,rows)),'tail',len(tail),flush=True)
words={w:len(deps[w]) for w in g};words.update({w:0 for w in terms})
byfirst={}
for w,cost in words.items():byfirst.setdefault(w[0],[]).append(w)
for arr in byfirst.values():arr.sort(key=lambda w:-len(w))
def join_words(parts,graph):
 # Choose a short left spine and avoid illegal atomic orientations. Each
 # binary parent incurs one rule unless it already has a graph definition.
 @lru_cache(None)
 def join(a,b):
  w=''.join(parts[a:b])
  if b==a+1:return (0,w,0,None)
  if w in graph:return (0,w,0,None)
  opts=[]
  for k in range(a+1,b):
   l=join(a,k);r=join(k,b)
   if l[1]in terms and not terms[l[1]]&1:continue
   if r[1]in terms and not terms[r[1]]&2:continue
   opts.append((l[0]+r[0]+1,w,1+max(l[2],r[2]),(k,l,r)))
  return min(opts,key=lambda a:(a[0],a[2]))if opts else (10000,w,10000,None)
 ans=join(0,len(parts))
 def put(rec):
  if rec[3]is None:return
  k,l,r=rec[3];put(l);put(r);graph[rec[1]]=(l[1],r[1])
 put(ans);return ans[0]
def build(w):
 dp=[1e10]*(len(w)+1);prev=[None]*(len(w)+1);dp[0]=0
 for i in range(len(w)):
  if dp[i]>=1e9:continue
  for token in byfirst.get(w[i],()):
   j=i+len(token)
   if w.startswith(token,i):
    score=dp[i]+words[token]+1
    if score<dp[j]:dp[j]=score;prev[j]=(i,token)
 if prev[-1]is None:return None
 parts=[];j=len(w)
 while j:i,t=prev[j];parts.append(t);j=i
 parts.reverse();ng=dict(g)
 if join_words(parts,ng)>1000:return None
 live=closure(roots|{w},ng)
 return {x:ng[x]for x in live},parts

def rename(t,m):
 if isinstance(t,str):return m.get(t,t)
 if isinstance(t,tuple):return tuple(rename(x,m)for x in t)
 return t
maps=[dict(zip(('a','b','c'),p))for p in __import__('itertools').permutations(('a','b','c'))]
variants=[[emit(rename(row,m))for m in maps]for row in sm.ROWS[1:]]
best=10000;rng=random.Random(531205)
limit=int(sys.argv[1])if len(sys.argv)>1 else 1200
start=time.monotonic()
for trial in range(limit):
 if trial==0:order=list(range(8));roles=[2]+[0]*7
 elif trial%10==0:order=list(range(8));roles=[rng.randrange(6)for _ in range(8)]
 else:order=rng.sample(range(8),8);roles=[rng.randrange(6)for _ in range(8)]
 w=prefix+''.join(variants[i][roles[i]]for i in order)+tail
 ans=build(w)
 if ans is None:continue
 graph,parts=ans
 if len(graph)<best:
  best=len(graph);d=dict(base,status='AX_SYMMETRY_ABSTRACT_CANONICAL_CANDIDATE',rules_count=best,rules=[[w,*ab]for w,ab in sorted(graph.items())],roots=[w if x==ax else x for x in base['roots']],source_replacements={ax:w},axiom_order=order,axiom_roles=roles,role_maps=maps,trial=trial)
  Path('axiom-canonical-best.json').write_text(json.dumps(d,indent=2)+'\n');print('BEST',best,'trial',trial,'pieces',len(parts),'seconds',time.monotonic()-start,flush=True)
 if best<=127:break
print('DONE',best,'seconds',time.monotonic()-start)
