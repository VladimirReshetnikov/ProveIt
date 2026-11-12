#!/usr/bin/env python3
"""Source-level audit of both AQ26 quotient witnesses and conditional maps."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
base='research/adaptive-aq26-quotient122-model-draft/'
l=pin(base+'AQ26Quotient122Literal.lean.src','a54df6e9150130e72dcdbdfb0e50431a6796323437a99d32b705e7f85afff746')
r=pin(base+'AQ26Quotient122Residuals.lean.src','b6e1155d0dd45eb4f65f39593168be48acca6cf0825ee24b303f882ff4a1058d')
z=pin(base+'AQ26Quotient122ResidualZeros.lean.src','4536c65020edf06669d53abf8f109e136a19cf3d68ecd6334d752fcf0f5ec3e9')
w=pin(base+'AQ26Quotient122Witness.lean.src','722970a165318f44b878af8b5e477bd9e9b1932aa86cf3340f3f433d3029d1fe')
t=pin(base+'AQ26Quotient122ConditionalTransfer.lean.src','df0fbd26eb39cd6de845c4438a93a80bb2013afabcfd847008332ae7e0caebec')
pin(base+'receipt.json','de161e93826254bf60eec4bfbfc4fad2c75e748fe804bd9277fb51ea09533241')
pin('reviews/adaptive-aq26-two-quotients122-independent/result.json','48216bbe262c6aaa9dc92a9d58a0b67a021a629f6222cf56060df4dc148d99ff')
g=json.loads(pin('research/adaptive-aq26-two-quotients122/candidate.json','14c9cac4f3af45c15ec5e6df623c83fcab7581ba042aff34c6614dad890154ae'))
p=json.loads(pin('research/adaptive-square-sums26-degree8/candidate.json','d8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5'))
pz=pin('Lean/DiophantineConsistency/AdaptiveAQ26Zeros.lean','dd49ed0bf68338354dd99498cb091176e21eed281dff0fe252ed8fc99932024c')
q=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884')
ep=pin('Lean/DiophantineConsistency/IPRAAQ26Native.lean','7be42c91618e357ea519fc21afa07fbfd646aa376571d85fd004584b711c37d1')
assert len(g['source'])==122
for s in (l,r):
 for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 26) := .var {i}' in s
 for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 26) := .constant (p {i})' in s
 for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in s,n
assert [p['witnesses'][i] for i in (9,10,13,14,17,18,19,20,22)]==['eta','zeta','scaleVariable','mainScaleVariable','ellVariable','cSquareVariable','zValueVariable','dValueVariable','deltaVariable']
assert [g['witnesses'][i] for i in (13,14,19,20)]==['scaleVariable','mainScaleVariable','firstQuotient','mainQuotient']
def vec(s):
 v=re.findall(r'^  !\[([^\n]+)\]$',s,re.M);assert len(v)==1;return v[0].split(',')
assert len(vec(r))==17 and vec(r)==vec(pz)
assert '∀ i : Fin 17' in z and 'Fin 16' in z and 'foldSquares_zero_iff' in z
for x in ['have h0 := h 0','have h1 := h 1','v 19*v 19 = v 13*v 13*(1+v 17*(v 17+(v 9+v 10)))','v 20*v 20 = v 14*v 14*(1+v 22*v 18)','(v 13) (v 19) (1+v 17*(v 17+(v 9+v 10))) (hv 13) h0','(v 14) (v 20) (1+v 22*v 18) (hv 14) h1','rw [←hu]; exact hv 19','rw [←ht]; exact hv 20']:assert x in w,x
assert w.count('ArithmeticAdaptiveQuotients2011.scaled_quotient')==2
assert '∃ t : V, z=m*t ∧ t*t=n' in q
for x in ['if i.val=19 then u else if i.val=20 then t else v i','if i.val=19 then v 13*v 19 else if i.val=20 then v 14*v 20 else v i','(hproject :','(hextend :','AQ26Quotient122WitnessDraft.parent_quotients','(h : GraphZeroObligations)','IPRAAQ26Native.bridge26','theorem native_equivalence','theorem standard_equivalence']:assert x in t,x
assert 'positiveShift\n  (AdaptiveAQ26Literal.literal CurrentWindowCarry2011.ports)' in ep and '∼mappedNativeRefutation embedding' in ep
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',l+r+z+w+t)
print(json.dumps({'scope':'source-only graph, quotient, maps and premise audit; no Lean elaboration','child_literal_and_residual_rows':122,'sum_residuals':17,'parent_quotient_norm_indices':[0,1],'replaced_slots':[19,20],'scale_slots':[13,14],'quotient_witnesses':2,'both_graph_zero_maps_remain_premises':True,'native_and_standard_targets_conditional':True},sort_keys=True,indent=2))
