from pathlib import Path
import sys,json,itertools
BASE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(BASE/'construction'))
import compiler as c,baseline_tools as b
OUT=Path(__file__).resolve().parent
names={'H':'node58','D':'node55','A':'node70','C':'node65','P':'node49','readH':'node72','readDcons':'node75','guardcopy':'node142','guardcmp':'node150','+':('leaf','inc',1),'close':('leaf','breakTo',1)}
rev={v:k for k,v in names.items()}
old=b.expanded(c.read_grammar(BASE/'construction/inputs/pa194.grammar.json'))
w=b.word(old)

def I(a,b):return ('I',a,b)
def M(a,b):return ('M',a,b)
def E(a,b,flip=False):return ('E',b,a) if flip else ('E',a,b)
def U(a,b):return ('U',a,b)
def N(a):return ('N',a)
def Ex(a,b):return N(U(a,N(b)))
def emit(f):
 if isinstance(f,str):return [f]
 tag,*args=f
 if tag=='N':return emit(args[0])+['P','+','C']
 a,b=args
 if tag=='U':return emit(b)+emit(a)+['C','+','+']
 return emit(a)+emit(b)+['C']+['+']*{'I':0,'M':1,'E':3}[tag]

def words(flip,s3,s4,s6):
 h3=(M('H','D'),E('H','A',flip),M('A','D'))
 h4=(E('H','D',flip),M('A','H'),M('A','D'))
 h6=(U('D','A'),U('D',I('A','H')),U('D','H'))
 def curry(h,s):a,b,z=h;return I(b,I(a,z)) if s else I(a,I(b,z))
 return emit(curry(h3,s3)),emit(curry(h4,s4)),emit(Ex('D',E('H','D',flip))),emit(curry(h6,s6))
for part,(a,z) in zip(words(0,0,0,0),[(54,70),(70,86),(86,102),(102,121)]):
 assert [names[x]for x in part]==w[a:z],(part,w[a:z])

other=b.expanded(c.read_grammar(BASE/'search/inputs/second_grammar.json'))
assert b.word(other)==w

def reword(t,seq):
 it=iter(seq)
 def go(t):return (go(t[0]),go(t[1])) if c.isnode(t) else next(it)
 ans=go(t);assert next(it,None) is None;return ans

def save_tree(t,path):
 nodes={};memo={}
 def rec(t):
  if not c.isnode(t):return t
  if t in memo:return memo[t]
  l,r=map(rec,t);key='g'+str(len(nodes));nodes[key]=[l,r];memo[t]=key;return key
 root=rec(t);path.write_text(json.dumps({'root':root,'rules':nodes})+'\n')

def tarray(t):
 ts=[];memo={}
 def go(t):
  if t in memo:return memo[t]
  if c.isnode(t):l,r=map(go,t);v=(1,l,r,0)
  else:v=(0,c.MACROS[t] if t!=('leaf','breakTo',1) else -1,-1,-1)
  q=len(ts);ts.append(v);memo[t]=q;return q
 root=go(t);return ts,root

raw,_=c.machine()
cached=b.read_table(BASE/'construction/inputs/pa194C.native.tm')
fixed={k:a for k,a in cached.items() if k[0]<1300}
assert len(fixed)==268
texts=[str(len(fixed)//2)]
for q in sorted({q for q,b in fixed}):texts.append(' '.join(map(str,[q,*[int(x)for a in (fixed[q,0],fixed[q,1])for x in a]])))
variants=[];info=[]
for flags in itertools.product([0,1],repeat=4):
 if flags==(0,0,0,0):continue
 v=w[:]
 for part,(a,z) in zip(words(*flags),[(54,70),(70,86),(86,102),(102,121)]):
  assert len(part)==z-a;v[a:z]=[names[x]for x in part]
 for shape,t in enumerate([old,other]):
  tree=reword(t,v);tid=len(variants);variants.append(tree)
  info.append({'id':tid,'flip_equality':flags[0],'swap_head3':flags[1],'swap_head4':flags[2],'swap_head6':flags[3],'shape':shape,'tokens':[rev[x]for x in v]})
  save_tree(tree,OUT/f'variant{tid}.grammar.json')
texts.append(str(len(variants)))
for i,t in enumerate(variants):
 ts,r=tarray(t);texts.append(f'{i} {len(ts)} {r}')
 texts.extend(' '.join(map(str,x))for x in ts)
(OUT/'variants.txt').write_text('\n'.join(texts)+'\n')
(OUT/'variants.json').write_text(json.dumps(info,indent=2)+'\n')
print('wrote',len(variants),'safe logical variants')
