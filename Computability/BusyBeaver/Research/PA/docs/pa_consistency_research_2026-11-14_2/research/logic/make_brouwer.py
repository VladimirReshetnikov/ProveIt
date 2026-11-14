#!/usr/bin/env python3
"""Prepare a diagnostic, uncalibrated Brouwer-only search domain.

The old first head cannot simply be replaced by this head: see the exact
countermodel in the main report. The repaired experiment is prepared by
make_brouwer_explosion.py. This file is retained to reproduce the failed lead.
"""
from pathlib import Path
import json,itertools,shutil
BASE=Path(__file__).resolve().parent/'upstream'
OUT=Path(__file__).resolve().parent
names={'H':'node58','D':'node55','A':'node70','C':'node65','P':'node49','readH':'node72','readDcons':'node75','guardcopy':'node142','guardcmp':'node150','+':('leaf','inc',1),'close':('leaf','breakTo',1)}
rev={v:k for k,v in names.items()}
phys={'H':12,'D':98,'A':166,'C':90,'P':19,'readH':69,'readDcons':213,'guardcopy':194,'guardcmp':221,'+':61,'close':-1}
def read(p):
 d=json.loads(p.read_text());rs=d['rules']
 def rec(t):
  if isinstance(t,list):return tuple(t)
  if t=='node60':return (names['+'],names['+'])
  if t=='node61':return ((names['+'],names['+']),(names['+'],names['+']))
  return tuple(rec(x)for x in rs[t])if t in rs else t
 return rec(d['root'])
def isnode(t):return isinstance(t,tuple)and len(t)==2
def word(t):return word(t[0])+word(t[1])if isnode(t)else[rev[t]]
old=read(BASE/'primary.grammar.json')
other=read(BASE/'q.grammar.json')
w=word(old);assert len(w)==190

def I(a,b):return ('I',a,b)
def M(a,b):return ('M',a,b)
def E(a,b,flip=False):return ('E',b,a) if flip else ('E',a,b)
def U(a,b):return ('U',a,b)
def N(a):return ('N',a)
def Ex(a,b):return N(U(a,N(b)))
def emit(f):
 if isinstance(f,str):return[f]
 tag,*a=f
 if tag=='N':return emit(a[0])+['P','+','C']
 a,b=a
 if tag=='U':return emit(b)+emit(a)+['C','+','+']
 return emit(a)+emit(b)+['C']+['+']*{'I':0,'M':1,'E':3}[tag]
assert emit(I(Ex('D',U('D','H')),'H'))==w[18:35]
B=emit(I('H',U('D',Ex('D','H'))));assert len(B)==17

def curry(h,s):a,b,z=h;return I(b,I(a,z))if s else I(a,I(b,z))
def words(flip,s3,s4,s6):
 h3=(M('H','D'),E('H','A',flip),M('A','D'))
 h4=(E('H','D',flip),M('A','H'),M('A','D'))
 h6=(U('D','A'),U('D',I('A','H')),U('D','H'))
 return emit(curry(h3,s3)),emit(curry(h4,s4)),emit(Ex('D',E('H','D',flip))),emit(curry(h6,s6))

def reword(t,seq):
 it=iter(seq)
 def go(t):return(go(t[0]),go(t[1]))if isnode(t)else names[next(it)]
 r=go(t);assert next(it,None)is None;return r

def tarray(t):
 ts=[];memo={}
 def go(t):
  if t in memo:return memo[t]
  if isnode(t):l,r=map(go,t);v=(1,l,r,0)
  else:v=(0,phys[rev[t]],-1,-1)
  q=len(ts);ts.append(v);memo[t]=q;return q
 root=go(t);return ts,root
fixed={}
for l in (BASE/'unfolded201.native.tm').read_text().splitlines():
 if not l or l.startswith('#'):continue
 q,b,wr,d,n=l.split();q,b,wr,n=map(int,(q,b,wr,n))
 if q<1300:fixed[q,b]=(wr,int(d=='R'),n)
texts=[str(len(fixed)//2)]
for q in sorted({q for q,b in fixed}):texts.append(' '.join(map(str,[q,*[x for a in (fixed[q,0],fixed[q,1])for x in a]])))
variants=[];info=[]
for flags in itertools.product([0,1],repeat=4):
 v=w[:];v[18:35]=B
 for part,(a,z) in zip(words(*flags),[(54,70),(70,86),(86,102),(102,121)]):assert len(part)==z-a;v[a:z]=part
 for shape,t in enumerate([old,other]):
  tree=reword(t,v);variants.append(tree);info.append({'id':len(info),'H1':'Brouwer','flags':flags,'shape':shape,'tokens':v})
texts.append(str(len(variants)))
for i,t in enumerate(variants):
 ts,r=tarray(t);texts.append(f'{i} {len(ts)} {r}');texts.extend(' '.join(map(str,x))for x in ts)
(OUT/'brouwer_inputs.txt').write_text('\n'.join(texts)+'\n');(OUT/'brouwer_variants.json').write_text(json.dumps(info,indent=2)+'\n')
for f in ['logic_anneal.cpp','screen.cpp','leaf_attrs.txt']:shutil.copy2(BASE/f,OUT/f)
print('Diagnostic Brouwer-only templates; not calibrated to PA consistency:',len(variants))
