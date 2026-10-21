"""Parse inert pinned Lean Tree literals; independent, no repository code imported."""
import re,sys,json,collections,hashlib
from pathlib import Path
sys.setrecursionlimit(20000)
BASE=Path(__file__).resolve().parent
for pin in json.loads((BASE/'SOURCE_PINS.json').read_text())['sources']:
 data=(BASE/'upstream'/pin['name']).read_bytes()
 assert len(data)==pin['bytes']
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==pin['git_blob_sha']
s=(Path(__file__).resolve().parent/'upstream'/'KSource215Data.lean').read_text()
def parse(name):
 text=s.split('def '+name+' : Tree :=',1)[1].split('\n\n',1)[0]
 ts=re.findall(r'\.\w+|\d+|[()]',text);i=0
 def go():
  nonlocal i
  t=ts[i];i+=1
  if t=='(':
   a=go();assert ts[i]==')';i+=1;return a
  if t=='.node':return ('node',go(),go())
  if t=='.leaf':return ('leaf',go())
  if t=='.halt':return ('halt',)
  if t in ('.decnz','.inc','.brk','.cont'):
   n=int(ts[i]);i+=1;return (t[1:],n)
  raise ValueError(t)
 t=go();assert i==len(ts);return t
T=parse('t215');D=parse('tD')
def leaves(t,p=''):
 if t[0]=='leaf':return [(p,t[1])]
 return leaves(t[1],p+'0')+leaves(t[2],p+'1')
a=leaves(T);b=leaves(D)
print('leaves',len(a),len(b),'word_equal', [x[1] for x in a]==[x[1] for x in b])
print('opcodes',collections.Counter(x[1] for x in a)); print('other',collections.Counter(x[1] for x in b))
BASE.joinpath('trees.json').write_text(json.dumps({'source':T,'reference':D}))
BASE.joinpath('leaves.json').write_text(json.dumps({'source':a,'reference':b}))
def intervals(t):
 d={}
 def walk(t,n):
  if t[0]=='leaf': end=n+1
  else:
   m=walk(t[1],n);end=walk(t[2],m)
  d[n,end]=t
  return end
 walk(t,0);return d
I=intervals(T);J=intervals(D);common=set(I)&set(J)
# The intersection of two laminar interval families remains laminar.
stack=[];children=collections.defaultdict(list)
for x in sorted(common,key=lambda x:(x[0],-x[1])):
 while stack and not(stack[-1][0]<=x[0] and x[1]<=stack[-1][1]):stack.pop()
 if stack:children[stack[-1]].append(x)
 stack.append(x)
def skeleton(t,lo,holes):
 def go(t,n):
  if n in holes:
   interval,ix=holes[n]
   if I.get(interval)==t or J.get(interval)==t:return ('hole',ix),interval[1]
  if t[0]=='leaf':return t,n+1
  a,m=go(t[1],n);b,k=go(t[2],m);return ('node',a,b),k
 return go(t,lo)[0]
# children of size1 only abstract when opcodes agree; changed leaves stay literal.
motifs=collections.defaultdict(list)
for x in common:
 if I[x]==J[x]:continue
 cs=[c for c in children[x] if c[1]-c[0]>1 or I[c]==J[c]]
 holes={c[0]:(c,i) for i,c in enumerate(cs)}
 left=skeleton(I[x],x[0],holes);right=skeleton(J[x],x[0],holes)
 if left!=right:motifs[left,right].append(x)
print('common_intervals',len(common),'nontrivial_rewrite_motifs',len(motifs),'instances',sum(map(len,motifs.values())))
def sz(t):return 1+sum(sz(x) for x in t[1:] if isinstance(x,tuple))
records=[]
for (l,r),xs in sorted(motifs.items(),key=lambda x:-len(x[1])):
 records.append({'count':len(xs),'intervals':xs,'left':l,'right':r,'size':sz(l)+sz(r)})
 print(len(xs),'size',sz(l)+sz(r),'sample',xs[:2],str((l,r))[:450])
BASE.joinpath('motifs.json').write_text(json.dumps(records,indent=2))
