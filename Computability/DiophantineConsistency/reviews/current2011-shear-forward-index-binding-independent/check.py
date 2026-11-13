#!/usr/bin/env python3
"""Bounded source-interface and natural/signed truncation review; no Lean."""
import hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear-forward-index-binding-draft/README.md':'1a8ec7f8461eefd92899dad0f56c72f218d2b19811d54e47c7c5787d9f7a6424',
'research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src':'fb39f3cb211700acd7e431da2f7a4e95a256a4a6f98087f8db0cb163beb9101a',
'research/current2011-shear-forward-index-binding-draft/check.py':'7de46f2325a0f607c315557b66fcd8452d98b94d51aa1146a4f3bfcea8a45ff2',
'research/current2011-shear-forward-index-binding-draft/result.json':'e164d256eed6b02fe89a7eae7bc2be6e8ddba986cb44ae397994ca14661d4410',
'research/current2011-ordinary71-60-model-join/OrdinarySphere7160Model.lean':'98eda3763aa05598820c567e52a4c89d51a3aaaeed2912a925a9c1560d20ef98',
'Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean':'afc99ad41536f55e0f467581e4fbdbd5308036f93b6e3e10b1a5d2f1c113de4a',
'Lean/DiophantineConsistency/ArithmeticCarrier94Extraction.lean':'5e7ef8c7983af9a713b30a02616f00f81c3654b75574fecae944fee369c862f6',
'Lean/DiophantineConsistency/ArithmeticCarrier94Soundness.lean':'a325d0e3eef25c4313f94b28ccceb913d7ab4c1b153a175057db202eff923650',
'Lean/DiophantineConsistency/ArithmeticPellFirstIndex.lean':'8cf79ed14f00f565accbfae0eb03ccacca597d06d12a509fecd6d3272e30f9ce',
'Lean/DiophantineConsistency/ArithmeticCarrierRadix2011.lean':'87f89c10bd5499a4c7586d36138ded09fdcdb6968b16b954d30c1e335950c074',
'Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean':'112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9',
'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean':'f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
def need(b,m):
 if not b:raise RuntimeError(m)
for path,sha in pins.items():need(hashlib.sha256((root/path).read_bytes()).hexdigest()==sha,'pin '+path)
def read(p):return (root/p).read_text()
draft=read('research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src')
current=read('Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean');adaptive=read('Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean')
for s in (current,adaptive):
 need('def positiveShift {σ : Type*} (e : Expr σ) : Expr σ :=\n  e.subst (fun i => Expr.var i + Expr.constant 1)' in s,'shift definition')
 need('theorem internalZero_positiveShift' in s,'shift theorem')
need('namespace DiophantineConsistency.ObjectCurrentEquation2011' in current and 'ObjectCurrentEquation2011.internalZero_positiveShift _ v' in draft,'qualified shift')
need('InternalZero Carrier94Syntax.naturalExpression94 v' in read('research/current2011-ordinary71-60-model-join/OrdinarySphere7160Model.lean'),'94 endpoint')
for s in ['(w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9)', '(w 10) (w 11) (w 12) (w 13)', 'hb0 hl hh', 'ht hn hm hstrong haux', 'hwindow.1,hhalf', '(hrank :', '(hc :', '(ι_lt_ι).2 hn']:
 need(s in draft,'client argument: '+s)
rad=read('Lean/DiophantineConsistency/ArithmeticCarrierRadix2011.lean')
need('((q v-1)*(q v-v 1)+v 2)*((q v)^2-1)' in rad and '((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)' in rad,'rank definition')
need('0<q-F-alpha ∧' in read('Lean/DiophantineConsistency/ArithmeticPellFirstIndex.lean'),'gap')
need('2*R<k*Y+eta' in read('Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean'),'half')
# Concrete signed-vs-truncated controls, not a proof of a model cast.
count=0
for q in range(1,12):
 for F in range(q+1):
  for alpha in range(1,5):
   for mc in range(3):
    for mf in range(3):
     for J in range(1,4):
      nat=lambda a,b:max(a-b,0)
      rn=(nat(q,1)*nat(q,F)+alpha)*nat(q*q,1)+(mc+q*mf)*J
      rs=((q-1)*(q-F)+alpha)*(q*q-1)+(mc+q*mf)*J
      need(rn==rs,'truncation');count+=1
need(max(3-5,0)!=3-5,'F≤q is essential')
print(json.dumps({'source_pins_verified':len(pins),'both_qualified_shift_declarations_checked':True,'same_valuation_argument_shapes_checked':True,'signed_truncated_rank_controls':count,'F_upper_bound_negative_control':True,'rank_and_c_casts_are_hypotheses':True,'scope':'source review and finite arithmetic controls, no Lean or provider resolution'},sort_keys=True,indent=2))
