#!/usr/bin/env python3
"""Read-only direct-import source trace, no Lean or compiler-artifact claims."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('Use python3 -I -S -B')
def need(b,s):
 if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
roots=[Path('/tmp/current14-structured-endpoint-coherent-v3-20261104/src'),Path('/tmp/current14-printed-port-extension-v3-20261104/src'),Path('/tmp/current14-standard-fresh-source-20261104/src'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation'),Path('/home/codex/src/Proofs/.lake/packages/mathlib')]
chains=[
['Current14LiteralPorts','DiophantineConsistency.CurrentKernel2011','DiophantineConsistency.WangTiles942Core','Mathlib.Tactic','Mathlib.Tactic.NormNum.LegendreSymbol','Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol','Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity','Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum','Mathlib.NumberTheory.GaussSum','Mathlib.NumberTheory.LegendreSymbol.AddCharacter','Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots','Mathlib.RingTheory.Norm.Transitivity','Mathlib.FieldTheory.Galois.Basic','Mathlib.FieldTheory.Fixed','Mathlib.LinearAlgebra.Dual.Lemmas','Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber'],
['DiophantineConsistency.IPRAStandardCurrentEndpoint','DiophantineConsistency.IPRACurrentNativeZFC','DiophantineConsistency.IPRABoundedRhoZFC','DiophantineConsistency.IPRAWholeMatrixZFC','DiophantineConsistency.IPRAFoundationZFCMatrixComparison','DiophantineConsistency.IPRAExistentialComparison','Foundation.FirstOrder.NegationTranslation.GoedelGentzen','Foundation.Meta.IntProver','Foundation.Meta.Lit','Foundation.Logic.LogicSymbol','Foundation.Vorspiel.List.Basic','Foundation.Vorspiel.Matrix']]
def locate(name):
 rel=name.replace('.','/')+'.lean'
 for root in roots:
  p=root/rel
  if p.is_file():return p
 raise RuntimeError('missing source '+name)
def without_comments(t):
 out=[];i=0;level=0
 while i<len(t):
  if t[i:i+2]=='/-':level+=1;i+=2;continue
  if level and t[i:i+2]=='-/':level-=1;i+=2;continue
  if level:out.append('\n' if t[i]=='\n' else ' ');i+=1;continue
  if t[i:i+2]=='--':
   k=t.find('\n',i);i=len(t) if k<0 else k;continue
  out.append(t[i]);i+=1
 need(level==0,'unclosed comment')
 return ''.join(out)
pat=re.compile(r'^\s*(?:(?:public|private|meta)\s+)?import\s+([\w.]+)',re.M)
result=[]
for chain in chains:
 nodes=[]
 for j,name in enumerate(chain):
  p=locate(name);text=p.read_text();imports=pat.findall(without_comments(text))
  if j+1<len(chain):need(chain[j+1] in imports,'missing edge '+name+' -> '+chain[j+1])
  nodes.append({'module':name,'source':str(p),'sha256':sha(p)})
 result.append(nodes)
foundation=locate('Foundation.Vorspiel.Matrix');mathlib=locate('Mathlib.LinearAlgebra.Matrix.Defs')
need('def map (f : α → β) : (Fin k → α)' in foundation.read_text(),'Foundation map declaration')
need('def map (M : Matrix m n α) (f : α → β)' in mathlib.read_text(),'Mathlib map declaration')
out={'status':'PASS_SOURCE_DECLARED_EDGES','trace_sha256':sha(__file__),'chains':result,
 'colliding_source_definitions':[{'source':str(foundation),'sha256':sha(foundation),'declaration':'Matrix.map (finite vector map)'},
 {'source':str(mathlib),'sha256':sha(mathlib),'declaration':'Matrix.map (matrix entry map)'}],
 'scope':'Observed source import edges and declarations only; no full transitive source-to-object or dynamic provenance claim.'}
print(json.dumps(out,indent=2,sort_keys=True))
