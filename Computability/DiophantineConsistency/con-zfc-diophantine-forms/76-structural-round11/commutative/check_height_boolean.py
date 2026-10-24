#!/usr/bin/env python3
import json,hashlib,itertools,random,re
from pathlib import Path
R=Path(__file__).resolve().parent
j=json.loads((R/'height_boolean_step.json').read_text())
def require(x,m):
 if not x:raise AssertionError(m)
def prod(xs):
 a=1
 for x in xs:a*=x
 return a
g=j['selector_groups'];require(sorted(sum(g,[]))==list(range(12)),'partition')
d=[sum(j['horn_source']['branches'][k]['degree'] for k in v) for v in g]
require(d==[8,8,8,8,8,8,2,0] and max(d)+6==14,'degree')
require(j['witnesses'][-3:]==['b0','b1','b2'] and len(j['witnesses'])==23,'witnesses')
def value(h,b):return sum((x*(x-1))**2 for x in b)+sum(prod(h[k] for k in group)*prod(b[k] if (i>>k)&1 else 1-b[k] for k in range(3))**2 for i,group in enumerate(g))
n=0
for h in itertools.product((0,1),repeat=12):
 good=[]
 for b in itertools.product((0,1),repeat=3):
  i=sum(v<<k for k,v in enumerate(b));v=value(h,b)
  require((v==0)==(prod(h[k] for k in g[i])==0),'Boolean selector');good.append(v==0);n+=1
 require(any(good)==(prod(h)==0),'existential equivalence')
rng=random.Random(8913)
for _ in range(2000):
 h=[rng.randrange(20) for _ in range(12)];b=[rng.randrange(-4,6) for _ in range(3)];v=value(h,b)
 require(v>=0,'global nonnegative')
 if any(x not in (0,1) for x in b):require(v>0,'nonboolean excluded')
 n+=1
s=(R/'HeightBooleanCommutativeEquation.lean').read_text()
require(s.count('.boundedForall')==1 and 'Fin 5 ⊕ Fin 23' in s,'shape')
for i,group in enumerate(g):
 frag=('('+' * '.join('h'+str(k) for k in group)+f') * l{i} * l{i}') if group else f'l{i} * l{i}'
 require(frag in s,'literal group')
for name in ['HeightCommutativeEquation.lean','HeightSelectedCommutativeEquation.lean','HeightBooleanCommutativeEquation.lean']:
 text=(R/name).read_text();text=re.sub(r'/\-.*?\-/','',text,flags=re.S);text=re.sub(r'--[^\n]*','',text)
 stack=[];matching={')':'(',']':'[','}':'{'}
 for c in text:
  if c in '([{':stack.append(c)
  elif c in ')]}':require(bool(stack) and stack.pop()==matching[c],'balanced syntax')
 require(not stack,'balanced end')
 require(max(map(int,re.findall(r'\.var \(\.inr (\d+)\)',text)))<int(re.search(r'Fin 5 ⊕ Fin (\d+)',text).group(1)),'variable range')
out={'status':'PASS','selector_fixtures':n,'local_witnesses':23,'exact_local_degree':14,'group_degrees':d,'global_blocks':1,'constructors_balanced':3,'scope':'finite local checks; Lean not elaborated; global polynomial unmaterialized','literal_sha256':hashlib.sha256((R/'height_boolean_step.json').read_bytes()).hexdigest()}
(R/'BOOLEAN_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
