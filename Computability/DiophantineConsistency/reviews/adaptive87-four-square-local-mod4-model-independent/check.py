#!/usr/bin/env python3
"""Bounded source/finite arithmetic audit; not Lean or provider authentication."""
import collections,hashlib,itertools,json,re,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent;draft=r/'research/adaptive87-four-square-local-mod4-model-draft'
sha=lambda x:hashlib.sha256(x).hexdigest()
def require(b,m):
 if not b:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_bytes())
for f,h in pins.items():require(sha((r/f).read_bytes())==h,'pin '+f)
def read(f):return (r/f).read_text()
src=read('Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean');new=(draft/'FourUnitGeneric.lean.src').read_text();model=(draft/'FourSquare88Model.lean.src').read_text();original=read('research/adaptive87-four-square-current88-model-draft/FourUnitGeneric.lean.src');origmodel=read('research/adaptive87-four-square-current88-model-draft/FourSquare88Model.lean.src')
names=['first_bad','main_bad','strong_bad','aux_bad']
for name in names:
 pattern=r'(?m)^(?:private )?theorem '+name+r'\b.*? := by decide'
 a=re.findall(pattern,src,re.S);b=re.findall(pattern,new,re.S)
 require(len(a)==len(b)==1 and a[0]==b[0].replace('private theorem','theorem',1),'finite source '+name)
 require(f'{name} ' in new,'client fact '+name)
# Reconstruct both declared source deltas independently.
x=original.replace('import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011','import Mathlib.Data.ZMod.Basic\nimport Mathlib.Tactic.LinearCombination\nimport Mathlib.Tactic.Linarith',1)
insert='\n'.join(re.findall(r'(?m)^private theorem (?:first_bad|main_bad|strong_bad|aux_bad)\b.*? := by decide',new,re.S))
x=x.replace('open DiscreteOrderedRingFacts ArithmeticAdaptiveFactorUnits2011','open DiscreteOrderedRingFacts\n\n/- The next four finite residue facts are copied from\n   ArithmeticAdaptiveFactorUnits2011; only visibility is changed. -/\n'+insert,1).replace('Existing universal ZMod-4 exclusions','Local universal ZMod-4 exclusions',1)
require(x==new,'generic exact delta')
require('HAExpressionNoZeroEquiv.bridge _ _ ?_ hp' in model and "exact forall_congr' fun v => not_congr (sameZero V v)" in model,'nozero direction')
require('theorem bridge (hp : PolynomialBridge AdaptiveFirstRootFactor87Literal.naturalExpression87)' in model,'parent premise')
require('import DiophantineConsistency.HAExpressionSameZero' in origmodel and 'import DiophantineConsistency.HAExpressionNoZeroEquiv' in model,'bridge import')
candidate=origmodel.replace('import DiophantineConsistency.HAExpressionSameZero','import DiophantineConsistency.HAExpressionNoZeroEquiv',1).replace('open HAExpressionAssembly HAExpressionSameZero PRALanguage IPRANativeTheory','open HAExpressionAssembly HAExpressionNoZeroEquiv PRALanguage IPRANativeTheory',1)
local="""/-- Same valuation in each model; local to avoid the 86-specific provider. -/
def SameZero {n : ℕ} (e g : Expr (Fin n)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∀ v : Fin n → V, InternalZero e v ↔ InternalZero g v

theorem sameZero : SameZero naturalExpression"""
candidate=candidate.replace('theorem sameZero : HAExpressionSameZero.SameZero naturalExpression',local,1)
candidate=candidate.replace('    PolynomialBridge naturalExpression := HAExpressionSameZero.bridge _ _ sameZero hp',"""    PolynomialBridge naturalExpression := by
  apply HAExpressionNoZeroEquiv.bridge _ _ ?_ hp
  intro V _ _
  exact forall_congr' fun v => not_congr (sameZero V v)""",1)
require(candidate==model,'model exact delta')
counts=[0]*4
for q,z,n in itertools.product(range(4),repeat=3):require((1+z*z-(q**3*(q-1))**2*n)%4!=3,'first');counts[0]+=1
for u,a,c,z in itertools.product(range(4),repeat=4):require((1+z*z-u*u*(1+(a*a+4*a+3)*c*c))%4!=3,'main');counts[1]+=1
for a,f,i in itertools.product(range(4),repeat=3):require((1+i*i-(a*a+4*a+3)*(f*f-1))%4!=3,'strong');counts[2]+=1
for a,f,v,y in itertools.product(range(4),repeat=4):
 D=(a*a+4*a+3)*(f*f-1);require((D*v*v+(1-D)*y*y)%4!=3,'aux');counts[3]+=1
# Independent narrow header scanner, nesting block comments and stopping at first declaration.
def imports(path):
 s=path.read_text();out=[];i=depth=0;clean=[]
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2
  elif depth and s.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:clean.append(s[i]);i+=1
 require(depth==0,'unclosed comment '+str(path))
 for line in ''.join(clean).splitlines():
  line=line.strip()
  if not line:continue
  if line in ('prelude','module'):continue
  match=re.fullmatch(r'(?:public\s+)?import\s+([\w.]+(?:\s+[\w.]+)*)',line)
  if not match:break
  out.extend(match.group(1).split())
 return out
custom={'FourSquare88Model':draft/'FourSquare88Model.lean.src','FourUnitGeneric':draft/'FourUnitGeneric.lean.src','AdaptiveFourSquare88Graph':r/'research/adaptive87-four-square-current88-model-draft/AdaptiveFourSquare88Graph.lean.src'}
def closure(roots):
 todo=collections.deque((n,[n]) for n in roots);seen={};external=set();missing=set();route=None;target='DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011'
 while todo:
  n,path=todo.popleft()
  if n in seen or n in external or n in missing:continue
  if n==target:route=path
  f=custom.get(n)
  if f is None:
   if not n.startswith('DiophantineConsistency.'):external.add(n);continue
   f=r/'Lean'/Path(*n.split('.')).with_suffix('.lean')
  if not f.is_file():missing.add(n);continue
  edges=imports(f);seen[n]=edges;todo.extend((e,path+[e]) for e in edges)
 return seen,external,missing,route
conditional,_,missing,route=closure(['FourSquare88Model']);require(not missing and route is None,'conditional source cut')
whole,ext,missing,route=closure(['FourSquare88Model','DiophantineConsistency.HAAdaptiveFactor87']);require(not missing and route is not None,'instantiated source cut')
project=lambda d:{n for n in d if n.startswith('DiophantineConsistency.')}
require(len(project(conditional))==458 and len(project(whole))==658 and len(ext)==124,'closure count')
author=json.loads((draft/'result.json').read_bytes());require(route==author['instantiated_endpoint_factorunits_path'],'parent dependency chain')
recorded=author['instantiated_endpoint_sources'];require(set(whole)==set(recorded),'full source name set')
for n,edges in whole.items():
 require(edges==recorded[n]['imports'] and sha((r/recorded[n]['source']).read_bytes())==recorded[n]['sha256'],'closure source '+n)
roots=[Path('/tmp/ha87-full-transitive-p3xt6wra/lib'),Path('/tmp/current14-standard-fresh-build-20261104/lib')]
missing_both=sorted(n for n in project(whole) if not any((p/Path(*n.split('.')).with_suffix('.olean')).is_file() for p in roots))
require(missing_both==author['instantiated_endpoint_missing_from_both_roots'],'bounded object observations')
print(json.dumps({'scope':'bounded lexical source imports, finite arithmetic and object presence only; no Lean/provider authentication','pins_sha256':sha((d/'pins.json').read_bytes()),'mod4_cases':counts,'conditional_project_sources':len(project(conditional)),'instantiated_project_sources':len(project(whole)),'instantiated_external_imports':len(ext),'conditional_factorunits_path':None,'parent_factorunits_path':route,'missing_from_two_observed_roots':missing_both},indent=2,sort_keys=True))
