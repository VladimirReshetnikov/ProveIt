#!/usr/bin/env python3
"""Independent source/interface/coordinate audit only; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
files={
 'parent_graph':('research/adaptive-square-sums40-quotient-quartic/candidate.json','fd49361551fde7c523c4494c2fbfd475f9f6c0b7660e3aef22c09228db82700d'),
 'child_graph':('research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56'),
 'child_review':('reviews/adaptive-square-sums38-independent/result.json','5173a65bc0dd0140de5995e014929ad00fb05c0446b3367222ce8b6e6743aaff'),
 'parent_source':('Lean/DiophantineConsistency/AdaptiveQM40Context.lean','be48ed96bcb082715c99cd697bfa25ff21bd55aa789e868970b74e621422dece'),
 'zero_source':('Lean/DiophantineConsistency/AdaptiveQM40Zeros.lean','b90faa5bace82f3352b94c5d5fade8cc3477cab3017de5ac9dc35dc8a73ce482'),
 'native_source':('Lean/DiophantineConsistency/IPRAQM40Native.lean','d261c83bf10cd406063b6622b477dac4aefe0a811f1e471ad5142e587864d40b'),
 'same_nozero':('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean','d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06'),
 'model_ring':('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'),
 'shift':('Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean','f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6'),
 'literal':('research/adaptive-qm38-conditional-model-draft/AdaptiveQM38Literal.lean.src','f033af128e5ca4c7a5a1473e6370fc385d0354b110067ae84e168eed6643a44d'),
 'transfer':('research/adaptive-qm38-conditional-model-draft/AdaptiveQM38ConditionalTransfer.lean.src','104e56bcbc2ef2c922864c443b607fdc69ea048a8546d7c1d69340c6e7c7b588'),
 'slots':('research/adaptive-qm38-conditional-model-draft/AdaptiveQM38ParentSlots.lean.src','9fa0f09927c327a6debf46dd894db4ce7f0ef746f07fd908aeb24b26cd3e5c42'),
 'cut':('research/adaptive-qm38-conditional-model-draft/AdaptiveQM38EvaluationCut.lean.src','08707aa597d45389ab038fcda534d342ec4487913da52832ea441241fa9fee0b'),
 'author_receipt':('research/adaptive-qm38-conditional-model-draft/result.json','98cee7dcad589c788ea180874a29ffd4ef58d89510cc533b54771ce1a473274d')}
s={}
for n,(p,h) in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,n;s[n]=b.decode()
parent=json.loads(s['parent_graph']);child=json.loads(s['child_graph']);assert len(parent['witnesses'])==40 and len(child['witnesses'])==38
assert parent['witnesses'][29]=='ellProductVariable' and parent['witnesses'][33]=='deltaProductVariable'
assert child['witnesses']==[n for n in parent['witnesses'] if n not in ('ellProductVariable','deltaProductVariable')]
# Check every generated child row and variable/port index exactly.
lit=s['literal'];expected=[f'  let {n} : Expr (Fin 38) := .var {i}' for i,n in enumerate(child['witnesses'])]
expected += [f'  let {n} : Expr (Fin 38) := .constant (p {i})' for i,n in enumerate(child['fixed_numerals'])]
expected += ['  -- BEGIN GENERATED ROWS']+[f'  let {n} := {x} {op} {y}' for n,op,x,y in child['source']]+['  -- END GENERATED ROWS','  '+child['output']]
part=lit.split('def literal (p : Fin 4 → ℤ) : Expr (Fin 38) :=\n',1)[1].split('\n\nend ',1)[0]
assert part.splitlines()==expected and len(child['source'])==160
# Independently enumerate inverse index maps on all 38/40 coordinates.
proji=lambda i:i if i<29 else i+1 if i<32 else i+2
exti=lambda i:None if i in (29,33) else i if i<29 else i-1 if i<33 else i-2
assert [parent['witnesses'][proji(i)] for i in range(38)]==child['witnesses']
assert all(exti(proji(i))==i for i in range(38))
assert all(proji(exti(i))==i for i in range(40) if i not in (29,33))
for i,name in [(9,'eta'),(10,'zeta'),(17,'ellVariable'),(22,'cSquareVariable'),(26,'deltaVariable')]:
 assert parent['witnesses'][i]==child['witnesses'][i]==name
res=s['parent_source'].split('def residuals (p : Fin 4 → ℤ) : Fin 31 → Expr (Fin 40) :=',1)[1].split('\ndef sum ',1)[0]
m=re.search(r'  !\[([^\n]+)\]',res);assert m;rs=m.group(1).split(',')
assert len(rs)==31 and rs[20]=='ellProductDifference' and rs[24]=='deltaProductDifference'
assert 'theorem new_all' in s['zero_source'] and '∀ i : Fin 31' in s['zero_source']
slots=s['slots'];cut=s['cut'];trans=s['transfer'];flat=lambda x:re.sub(r'\s+',' ',x)
for x in ['.mp hz 20','.mp hz 24','v 29 = v 17*(v 17+(v 9+v 10))','v 33 = v 26*v 22']:
 assert x in slots,x
for x in ['if h : i.val < 29 then v ⟨i.val, by omega⟩','else if h : i.val < 32 then v ⟨i.val+1, by omega⟩',
 'if i.val=29 then v 17*(v 17+(v 9+v 10))','else if i.val=33 then v 26*v 22',
 'else if h : i.val < 33 then v ⟨i.val-1, by omega⟩']:
 assert x in trans,x
assert 'def ZeroPreservationObligations : Prop :=' in trans and '∀ (V : Type) [ORingStructure V]' in trans
assert 'InternalZero child (project v)' in trans and 'InternalZero parent (extend v)' in trans
assert all(f'theorem {n} (h : ZeroPreservationObligations)' in trans for n in ('polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'))
assert 'def EvaluationCut : Prop :=' in cut and 'parent.evalRing (fun i => ι (extend v i)) =' in cut and 'child.evalRing (fun i => ι (v i))' in cut
assert 'theorem obligations_of_evaluation_cut (hcut : EvaluationCut)' in cut
assert all(x in cut for x in ('slot29_of_zero CurrentWindowCarry2011.ports','slot33_of_zero CurrentWindowCarry2011.ports','extend_project_of_slots v h29 h33','rw [← hcut V (project v)]','rw [hcut V v]'))
assert 'theorem internalZero_iff' in s['model_ring'] and 'theorem internalZero_positiveShift' in s['shift']
assert 'def SameNoZero' in s['same_nozero'] and 'theorem bridge' in s['same_nozero']
assert '(positiveShift (AdaptiveQM40Context.literal CurrentWindowCarry2011.ports))' in s['native_source']
for n in ('literal','transfer','slots','cut'):assert not re.search(r'^\s*(?:axiom|opaque)\b|\b(?:sorry|admit)\b',s[n],re.M)
print(json.dumps({'scope':'independent pinned source/interface and exhaustive coordinate-map checks; no Lean, model proof or provider validation',
 'inputs':{n:{'path':p,'sha256':h} for n,(p,h) in sorted(files.items())},
 'literal_rows':160,'child_variables':38,'parent_variables':40,
 'deleted_parent_slots':[29,33],'parent_residual_indices':[20,24],
 'coordinate_inverse_on_retained_slots':True,'zero_maps_remain_explicit_hypotheses':True,
 'evaluation_cut_is_hypothesis':True,'lean_elaboration':False},sort_keys=True,indent=2))
