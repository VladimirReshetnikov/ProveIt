#!/usr/bin/env python3
"""Prepare exact minimally adapted 13-variable sources; no Lean invocation."""
import hashlib,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent;S=D/'Lean/DiophantineConsistency';OUT=HERE/'src/DiophantineConsistency'
pins={'ModelThirteenRestoration':'8e1f80500e54ee71b40085a01cdb00c22e69e66426fc823950dd07ab69380bfc',
 'ModelThirteenCarrier':'57f3cf755891aa921e9d97877af373e9194c6aa709a259c47678e4a370fd0185',
 'ModelThirteenForms':'98d9dcc48895ffe026c029b2496a61a35b66bca2f7b2fd1b31b8acf43acbfb6f'}
def need(b,s):
 if not b:raise RuntimeError(s)
def once(s,a,b):need(s.count(a)==1,'replace count '+a);return s.replace(a,b,1)
def refs(s,count):
 s,n=re.subn(r'\ntheorem reference_equivalence\d+\s*:.*?(?=\n(?:/--|theorem |end DiophantineConsistency\.))','\n',s,flags=re.S)
 need(n==count,'unexpected reference theorem count');return s
need(not OUT.exists(),'refusing existing source snapshot');OUT.mkdir(parents=True)
for name,h in pins.items():
 raw=(S/(name+'.lean')).read_bytes();need(hashlib.sha256(raw).hexdigest()==h,'source drift '+name);s=raw.decode()
 if name=='ModelThirteenRestoration':
  s=once(s,'import DiophantineConsistency.ModelCarrierSpheres','import FrontierBridge')
  s=once(s,'open ModelCarrierSpheres DiscreteOrderedRingFacts','open FreshCarrierSpheres DiscreteOrderedRingFacts')
 elif name=='ModelThirteenCarrier':
  s=once(s,'import DiophantineConsistency.HAExpressionNoZeroEquiv','import FrontierBridge')
  s=once(s,'open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelCarrierSpheres','open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres')
  need(s.count('ModelCarrierCurrent.evalRing_expressionAt65')==2 and s.count('ModelCarrierCurrent.beta_pos')==2 and s.count('ModelCarrierCurrent.currentBridge')==1,'carrier helper count')
  s=s.replace('ModelCarrierCurrent.evalRing_expressionAt65','FreshModel106.evalRing_expressionAt65').replace('ModelCarrierCurrent.beta_pos','FreshModel106.beta_pos').replace('ModelCarrierCurrent.currentBridge','HACurrentEquation2011.polynomialBridge')
  s=refs(s,1)
  s=once(s,'standard and equality-only iPRA proofs of its no-zero sentence','standard iPRA proofs of its no-zero sentence')
 else:
  s=once(s,'open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelCarrierSpheres','open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres')
  need(s.count('ModelCarrierCurrent.beta_pos')==3,'forms beta count');s=s.replace('ModelCarrierCurrent.beta_pos','FreshModel106.beta_pos');s=refs(s,2)
 marker='namespace DiophantineConsistency.'+name+'\n'
 s=once(s,marker,marker+'attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta\n  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix\n')
 (OUT/(name+'.lean')).write_text(s)
 print(name,hashlib.sha256(s.encode()).hexdigest())
