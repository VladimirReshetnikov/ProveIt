from pathlib import Path
import json,itertools,difflib,os
HERE=Path(__file__).resolve().parent
PRIMARY=HERE/'inputs/ax11h'
def corpus_docs():
 root=os.environ.get('PROVEIT_ROOT')
 if not root:raise RuntimeError('Corpus regeneration requires PROVEIT_ROOT pointing to ProveIt commit 7c0bb454cf73c29ca1c385f9fec856ddd236a7cb; captured search replays do not require it.')
 docs=Path(root)/'Computability/BusyBeaver/Research/PA/docs'
 if not docs.is_dir():raise FileNotFoundError(docs)
 return docs
INC=('leaf','inc',1)
MACROS={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,INC:61}
def isnode(x):return isinstance(x,tuple)and len(x)==2
def read(path):
 d=json.loads(path.read_text())
 def rec(x):
  if isinstance(x,list):return tuple(x)
  if x=='node60':return (INC,INC)
  if x=='node61':return ((INC,INC),(INC,INC))
  if x in d['rules']:return tuple(rec(y)for y in d['rules'][x])
  return x
 return rec(d['root'])
def word(x):return word(x[0])+word(x[1])if isnode(x)else[x]
def tarray(t):
 ns=[];seen={}
 def go(t):
  if t in seen:return seen[t]
  row=(1,go(t[0]),go(t[1]),0)if isnode(t)else(0,MACROS[t],-1,-1)
  k=len(ns);seen[t]=k;ns.append(row);return k
 root=go(t);return ns,root
def balanced(w):
 if not w:return None
 if len(w)==1:return w[0]
 m=len(w)//2
 return balanced(w[:m]),balanced(w[m:])
def adapt(old,w):
 ow=word(old);mapped={i:[] for i in range(len(ow))}
 for tag,i,j,a,b in difflib.SequenceMatcher(None,ow,w,autojunk=False).get_opcodes():
  if tag=='equal':
   for k in range(j-i):mapped[i+k]+=[w[a+k]]
  elif tag in ['replace','insert']:
   slot=i if i<len(ow) else i-1
   mapped[slot]+=w[a:b]
 it=iter(mapped.values())
 def go(t):
  if not isnode(t):
   z=next(it);return balanced(z) if z else None
  a,b=map(go,t)
  if a is None:return b
  if b is None:return a
  return a,b
 ans=go(old);assert word(ans)==w
 return ans
shapes=[read(PRIMARY/'inputs/primary.grammar.json'),read(PRIMARY/'inputs/q.grammar.json')]
shapes=[adapt(s,word(s)[:-1]+['node49']) for s in shapes]
bounds=[18,35,54,70,86,102,121,128]
seeds=[];info=[]
# Duplicate each standard head at every head boundary. This preserves side effects
# because every block emits one closed theorem and preserves D,A,H.
for shapeid,s in enumerate(shapes):
 base=word(s);assert len(base)==190
 for head,(a,z) in enumerate(zip(bounds,bounds[1:])):
  for b in bounds:
   for n in [1,2]:
    w=base[:b]+base[a:z]*n+base[b:]
    seeds.append(adapt(s,w));info.append(dict(shape=shapeid,head=head,insertion=b,copies=n,original_tokens=190,tokens=len(w)))
# Build full reader templates using AX11H fixed control.
tokens=(PRIMARY/'research/joint_grammar/joint_ax11/seeds_h.txt').read_text().splitlines()
nb=int(tokens[0]);text=tokens[:1+nb]+[str(len(seeds))]
for tid,t in enumerate(seeds):
 ns,root=tarray(t);text.append(f'{tid} {len(ns)} {root}')
 text.extend(' '.join(map(str,row))for row in ns)
(HERE/'duplicate.templates.txt').write_text('\n'.join(text)+'\n')
(HERE/'duplicate.seeds.json').write_text(json.dumps(info,indent=2)+'\n')
print('seeds',len(seeds),'sizes',min(map(lambda s:len(word(s)),seeds)),max(map(lambda s:len(word(s)),seeds)))
