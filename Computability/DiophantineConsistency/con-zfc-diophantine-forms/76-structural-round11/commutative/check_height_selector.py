#!/usr/bin/env python3
import json,hashlib,itertools,random
from pathlib import Path
R=Path(__file__).resolve().parent
j=json.loads((R/'height_selector_step.json').read_text())
def require(x,m):
 if not x:raise AssertionError(m)
def product(xs):
 a=1
 for x in xs:a*=x
 return a
groups=j['selector_groups'];require(sorted(sum(groups,[]))==list(range(12)),'partition')
degrees=[sum(j['horn_source']['branches'][k]['degree'] for k in g) for g in groups]
require(degrees==[14,12,12,12],'group degrees')
require(max([8]+[d+6 for d in degrees]+[10,6])==20,'degree')
require(j['witnesses'][-1]=='selector' and len(j['witnesses'])==21,'witnesses')
def value(h,r):
 return product(r-i for i in range(4))**2+sum(product(h[k] for k in group)*product(r-i for i in range(4) if i!=a)**2 for a,group in enumerate(groups))
n=0
for h in itertools.product((0,1),repeat=12):
 good=[]
 for r in range(-3,8):
  v=value(h,r);require(v>=0,'nonnegative');expected=(r in range(4) and product(h[k] for k in groups[r])==0)
  require((v==0)==expected,'selector roots');good.append(v==0);n+=1
 require(any(good)==(product(h)==0),'existential equivalence')
rng=random.Random(74592)
for _ in range(500):
 h=[rng.randrange(50) for _ in range(12)]
 require(any(value(h,r)==0 for r in range(4))==(product(h)==0),'positive values');n+=1
s=(R/'HeightSelectedCommutativeEquation.lean').read_text()
require(s.count('.boundedForall')==1 and 'Fin 5 ⊕ Fin 21' in s,'global shape')
require('let g := r * (r - 1) * (r - 2) * (r - 3)' in s,'root guard')
for a,g in enumerate(groups):require('('+' * '.join('h'+str(k) for k in g)+f') * l{a} * l{a}' in s,'literal group')
out={'status':'PASS','selector_fixtures':n,'local_witnesses':21,'exact_local_degree':20,'group_degrees':degrees,'global_blocks':1,'global_status':'uncompiled, unmaterialized; no full equation count','literal_sha256':hashlib.sha256((R/'height_selector_step.json').read_bytes()).hexdigest()}
(R/'SELECTOR_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
