#!/usr/bin/env python3
"""Reproduce inert generated source and inspect direct theorem interfaces."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent
PINS={
 'research/adaptive87-four-square-current88-model-draft/generate.py':'aeaabfaef3c270696633155fcea55045e193d69a68d8bf5b0b4ca93a4b6d8d71',
 'research/adaptive87-four-square-current88-model-draft/AdaptiveFourSquare88Graph.lean.src':'5908a3a7329135658af7f653a4cf81856016c7015006235a94992c3550c0894d',
 'research/adaptive87-four-square-current88-model-draft/FourUnitGeneric.lean.src':'50218ec01fc5e93bb78c31aaa9c8b21eae24a52c8ca524eaec36ef7219ee23d3',
 'research/adaptive87-four-square-current88-model-draft/FourSquare88Model.lean.src':'a0684adbf49c8e3edddfc7151619ed3b3981c72dbbe8870067fbeb4dcd9e6ba7',
 'research/adaptive87-four-square-current88-30/graph.json':'293dac5175d4924812177a1e73a316bf5cc16bf1b5cef636388d9e110eebb7ed',
 'research/adaptive87-four-square-current88-30/result.json':'be3cf8c4ca971f78326095cb126a39b2739989efd11bfa3619d3e916ac67d14d',
 'Lean/DiophantineConsistency/AdaptiveFirstRootFactor87Literal.lean':'c870a43ab38e37d0985c5a57a3fd090f2e64efed479d81b4665623802e8928e3',
 'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean':'9e80ae52f5dddd21d50684ebb6ca6556e95ac37905277bc476d251b7bf59f5a4',
 'Lean/DiophantineConsistency/ModelCarrierScaled.lean':'8fe67fb1c7840f1a915fc1d34bdc26953573a62bcceaef1622e478f41ae90134',
 'Lean/DiophantineConsistency/HAExpressionSameZero.lean':'6a17db77b715aedf0ed87c19952ac61792a131c069d30eb96adb586d3e58ab28',
 'Lean/DiophantineConsistency/HAAdaptiveFactor87.lean':'710768bbb3f75a9f700f8d5407d9ab9fdff5d50088c43779123d200975a2ffc2',
}
for name,h in PINS.items():
 if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=h: raise RuntimeError('pin changed: '+name)
run=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'generate.py')],check=True,capture_output=True)
if run.stdout!=(HERE/'AdaptiveFourSquare88Graph.lean.src').read_bytes(): raise RuntimeError('generated source differs')
g=json.loads((ROOT/'research/adaptive87-four-square-current88-30/graph.json').read_bytes())
parent=json.loads((ROOT/'research/adaptive-first-root-factor87/candidate.json').read_bytes())
def parsed_rows(text):
 rows=[]
 for line in text.splitlines():
  m=re.fullmatch(r'\s*let ([A-Za-z][A-Za-z0-9_]*) := ([A-Za-z0-9_]+) ([+*\-]) ([A-Za-z0-9_]+)',line)
  if m:
   name,left,op,right=m.groups()
   rows.append([name,op,int(left) if left.isdigit() else left,int(right) if right.isdigit() else right])
 return rows
source=(HERE/'AdaptiveFourSquare88Graph.lean.src').read_text(); parsed=parsed_rows(source)
selected=[r for r in parsed if r[0] in {x[0] for x in g['source']}]
if selected!=g['source'] or len(selected)!=88: raise RuntimeError('generated AST rows mismatch')
full=(ROOT/'Lean/DiophantineConsistency/AdaptiveFirstRootFactor87Literal.lean').read_text()
cut=full.split('def expressionAt87 (p : Fin 4 → ℤ) : Expr (Fin 13) :=',1)[1].split('\ntheorem maintained_as_context',1)[0]
if parsed_rows(cut)!=parent['source']: raise RuntimeError('parent Lean source rows differ from 87 JSON')
generic=(HERE/'FourUnitGeneric.lean.src').read_text();model=(HERE/'FourSquare88Model.lean.src').read_text()
for marker in ('theorem product_iff_squares','theorem factor_exclusions','first_bad','main_bad','aux_bad','strong_bad'):
 if marker not in generic: raise RuntimeError('generic interface missing: '+marker)
for marker in ('theorem unshifted_same_zero','theorem sameZero','theorem bridge (hp :','theorem native_equivalence (hp :','factor_exclusions (mod4 (V:=V))','parent_eq'):
 if marker not in model: raise RuntimeError('model interface missing: '+marker)
if 'let parent := (1+g72)*(Fa*((1+A0)*(1+A1)))-1' not in source or 'theorem parent_eq' not in source: raise RuntimeError('missing exact parent association')
print(json.dumps({'scope':'static direct source/row markers and generator replay; no Lean or provider authentication',
 'pinned_files':len(PINS),'parent_source_rows_compared':len(parent['source']),
 'new_source_rows_compared':len(selected),'negative_unit_exclusions':4,
 'ipra_parent_bridge_explicit':True},indent=2,sort_keys=True))
