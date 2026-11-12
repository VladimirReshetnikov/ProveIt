#!/usr/bin/env python3
"""Pin source, inspect assumptions, and check a rational nondiscrete counterexample.

This does not elaborate Lean or prove any universal arithmetic claim.
"""
from fractions import Fraction
from pathlib import Path
import hashlib, json
D = Path(__file__).resolve().parents[2]
inputs = {
 'pred':('research/ordinary14-natural-forced82-predecessor-draft/Predecessors82.lean','9b17307ba0245cf02d3f944510daab2560f34b1ba31f2b93323c279bf12d0d3e'),
 'partial':('research/ordinary14-natural-forced82-predecessor-draft/PartialShift82To74.lean','33b1d66bc3ab8010d83b91bff8604b015a3df000630a8d09fabbd77aa3e30a7e'),
 'model':('research/ordinary14-natural-forced82-ring-bridge-draft/Natural82Model.lean','e10b5e7dcc6169fd4730f3bf4e9058081efa1ac4e628de382dcbfc2dcf244854'),
 'diff':('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'),
 'bound':('research/ordinary14-natural-forced82-predecessor-draft/GraphPredecessors82.lean','7972ddb132643d0fd46bfd66e200bdf80a48e5d0df1b75f719b9c4ef5db5de54'),
 'g74':('research/ordinary14-positive-guard74/candidate.json','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'),
 'p74':('research/ordinary14-root74-slim-overlay/source/P74PositiveGuard.lean.src','5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b'),
 'units':('research/ordinary14-root74-slim-overlay/source/OwnZeroProduct74.lean.src','26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db'),
 'residues':('research/ordinary14-root74-slim-overlay/source/FactorResidues74.lean.src','368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60'),
}
s={}
for name,(path,h) in inputs.items():
 data=(D/path).read_bytes(); assert hashlib.sha256(data).hexdigest()==h, path
 s[name]=data.decode()
p=s['pred']; part=s['partial']
# Ensure the conditional helper visibly asks for all mathematical premises.
for token in (
 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]',
 '(ha : 0 ≤ a) (hell : 0 ≤ ellPart)',
 '(hfirst : ι (w 8)*ι (w 8) = ellPart + 1)',
 '(hstrong : 1 + I*I - (a*a + 4*a + 3)*(ι (w 3)*ι (w 3) - 1) = 1)',
 '(ι (w 11)*ι (w 11) - v*v) = 1) : HasThreePredecessors w',
 'ModelDifferenceRing.one_le_of_pos', 'exists_add_of_le',
): assert token in p, token
assert '∃ f r y : V, v 3 = f + 1 ∧ v 8 = r + 1 ∧ v 11 = y + 1' in s['model']
assert 'theorem one_le_of_pos (hd : ∀ a : V, 0 < a → 1 ≤ a)' in s['diff']
assert 'if j = 3 ∨ j = 8 ∨ j = 11 then v j else v j + 1' in part
assert 'theorem internalZero_iff_partial' in part
bound=s['bound']
for token in ('theorem strong_cut', 'theorem aux_cut', 'theorem a_nonnegative',
 'theorem predecessors_of_zero', '(hbeta : (p 0 : DiffRing V) = ι beta) (hb : 0 < beta)',
 'restricted_residues p u', 'factor_units_of_zero p beta u hbeta hb hJ hw hs',
 '(unit_iff_one (P74PositiveGuard.graph p).aux u).mp units.2.2.1',
 '(unit_iff_one (P74PositiveGuard.graph p).strong u).mp units.2.2.2.2',
 'predecessors_of_factor_equations w a I vroot ellPart', '(a_nonnegative p beta u hbeta) (ι_nonneg _)'):
 assert token in bound, token
assert '(hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)' in s['units']
assert 'theorem restricted_residues' in s['residues']

# Check the actual 74 Lean graph against JSON, then inspect all rows needed for
# the first, strong, auxiliary and embedded-a cuts. This is structural text
# evidence; Lean interpretation and the tactics are not checked.
g=json.loads(s['g74']); lean=s['p74']; rows=[]
for line in lean.split('  -- BEGIN LITERAL GRAPH\n')[1].split('  -- END LITERAL GRAPH\n')[0].splitlines():
 pieces=line.split(); assert len(pieces)==6 and pieces[0]=='let' and pieces[2]==':='
 def atom(x): return int(x) if x.isdecimal() else x
 rows.append([pieces[1],pieces[4],atom(pieces[3]),atom(pieces[5])])
assert rows==g['source'] and len(rows)==74
for i, name in enumerate(g['witnesses']):
 assert f'  let {name} : Expr (Fin 14) := .var {i}\n' in lean
assert '⟨F0, F1, Fa, Fs, guard, out, qm, q, X, Y, k, ell, a, c, U, Dstar, Q, I, V, C⟩' in lean
by={n:[op,x,y] for n,op,x,y in rows}
expected={
 'qm':['*','J','beta'], 'q':['+',1,'qm'], 'X':['*','q','w'],
 'q2':['*','q','q'], 'q3':['*','q','q2'], 'Y':['*','q3','s'],
 'E':['*','X','Y'], 'k':['+','eta','zeta'], 'kY':['*','Y','k'],
 'ell':['*','E','kY'], 'a':['+','E','Y'], 'g15':['*',4,'a'],
 'H':['+',3,'g15'], 'g17':['*','a','a'], 'Delta':['+','H','g17'],
 'f2':['*','f','f'], 'rho':['-','f2',1], 'Q':['*','Delta','rho'],
 'I':['*','c2','i'], 'g71':['*','I','I'], 'g72':['-','g71','Q'],
 'Fs':['+',1,'g72'], 'y2':['*','y','y'], 'V2':['*','V','V'],
 'g81':['-','y2','V2'], 'g82':['*','Q','g81'], 'Fa':['-','y2','g82'],
 'g30':['+','ell','k'], 'g38':['*','r','r'], 'g40':['*','ell','g30'],
 'F0':['-','g38','g40'],
}
for name,row in expected.items(): assert by[name]==row, name
# In Q, the displayed auxiliary equation permits y=0: this checks the
# logical need for discrete units and is not an IΣ₁ model counterexample.
a,f,r,y,I,v,ell=map(Fraction,(0,2,1,0,3,0,0))
v=Fraction(1,3)
delta=a*a+4*a+3
assert a>=0 and ell>=0 and delta>1
assert r*r==ell+1
assert 1+I*I-delta*(f*f-1)==1
assert y*y-delta*(f*f-1)*(y*y-v*v)==1
assert y==0 and Fraction(0)<(f*f-1)*v*v<1
# The two valuation prescriptions agree at all 14 coordinates in modular
# sample rings; this is a finite control, not the ring identity proof.
checks=0
for modulus in (2,4,7,11):
 for j in range(14):
  for x in range(modulus):
   down=(x-1)%modulus if j in (3,8,11) else x
   shifted=(down+1)%modulus
   partial=x if j in (3,8,11) else (x+1)%modulus
   assert shifted==partial
   checks+=1
print(json.dumps({'scope':'pinned source assumptions, structural factor checks and finite controls; no Lean or unbounded proof',
                  'source_files':len(inputs), 'selected_slots':[3,8,11],
                  'factor_graph_rows_checked':len(expected),
                  'partial_shift_modular_controls':checks,
                  'rational_nondiscrete_auxiliary_counterexample_checked':True},sort_keys=True,indent=2))
