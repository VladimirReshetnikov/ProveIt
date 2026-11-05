#!/usr/bin/env python3
"""Generate an uncompiled 29-slot residual/static-assignment proof draft."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1]
gpath=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';spath=D/'research/nine-sharing-quartic65-norm38-candidate/seed.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(gpath)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
assert sha(spath)=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23'
g=json.loads(gpath.read_text());s=json.loads(spath.read_text());indices={n:i for i,n in enumerate(g['witnesses'])};indices.update({n:14+i for i,n in enumerate(g['fixed_numerals'])});indices.update({1:18,3:19,4:20});nodes={}
for off,(row,record) in enumerate(zip(g['source'][:60],s['gate_records'])):
 name,op,left,right=row;assert (name,op,left,right)==(record['name'],record['op'],record['left'],record['right'])
 nodes[name]=(21+off,indices[left],indices[right],{'+':'add','-':'sub','*':'mul'}[op]);indices[name]=21+off
def rhs(r):
 name,kind=r['gate'],r['kind'];target,left,right,op=nodes[name]
 if kind in ('positive','negative'):
  return f'{kind}Residual ι GateOp.{op} (v {left}) (v {right}) (v {target})'
 assert kind=='norm';return f'pairValue ι (v {target}) - '+('pairValue ι (v 36)' if name=='scaled_Ns' else '1')
slots=[{'slot':i,'gate':r['gate'],'kind':r['kind'],'rhs':rhs(r)} for i,r in enumerate(s['residuals'])];assert len(slots)==29
header='''import DiophantineConsistency.SharingNormSquares
import DiophantineConsistency.NormAssignment38

/-! UNCOMPILED DRAFT. Exact slot-to-gate identities and conditional extraction.
Imports, tactic scripts and every theorem in this file are unverified. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def residuals (p : Fin 4 → ℤ) : List (Expr (Fin 39)) :=
  SharingSeed38.firstResidual p :: SharingSeed38.remainingResiduals p

def residualAt (p : Fin 4 → ℤ) (i : Fin 29) : Expr (Fin 39) :=
  (residuals p).get ⟨i.val, by simpa [residuals, SharingSeed38.remainingResiduals] using i.isLt⟩

'''
lines=[header]
for slot in slots:
 i=slot['slot'];lines.append(f'''/-- Slot {i}: {slot['gate']} / {slot['kind']}. -/
theorem slot{i:02d} (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p {i}).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; {slot['rhs']}) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

''')
lines.append('''/-- The sum-of-squares theorem supplies a zero at each indexed slot. -/
theorem each_slot_zero (p : Fin 4 → ℤ) (w : Fin 38 → V)
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w))
    (i : Fin 29) : (residualAt p i).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) = 0 := by
  have all := (SharingNormSquares.seed_zero_iff_residuals p (Fin.cons (1 : V) w)).mp hz
  have hm : residualAt p i ∈ residuals p := List.get_mem _ _
  exact (internalZero_iff.mp (all _ hm))

/-- Proposed extraction from the 29 literal equalities to the static graph
constraints. It is not a source-expression identification or model bridge. -/
theorem seed_zero_static (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    NormAssignment38.gatesHold ι ports w ∧ NormAssignment38.fiveNorms ι ports w := by
''')
for slot in slots:
 i=slot['slot'];lines.append(f'  have h{i:02d} := each_slot_zero p w hz {i}\n  rw [slot{i:02d} p ports w hp] at h{i:02d}\n')
norm={slot['gate']:slot['slot'] for slot in slots if slot['kind']=='norm'};assert set(norm)=={'N0','N1','Na','Nt','scaled_Ns'}
lines.append('''  constructor
  · unfold NormAssignment38.gatesHold
    simp only [NormAssignment38.gates, List.mem_cons, forall_eq_or_imp]
    repeat' constructor
    all_goals simp_all [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute]
  · unfold NormAssignment38.fiveNorms
''')
lines.append('    exact ⟨'+', '.join(f'sub_eq_zero.mp h{norm[name]:02d}' for name in ('N0','N1','Na','Nt','scaled_Ns'))+'⟩\n')
lines.append('''
-- Remaining: compile and repair these statements; prove the static-to-source
-- topological evaluation, fixed-port casts, forward witness construction,
-- Jones instantiation and consistency transfer.
end DiophantineConsistency.Norm38SlotExtraction
''')
target=P/'Norm38SlotExtraction.lean';mapfile=P/'slots.json';assert not target.exists() and not mapfile.exists()
target.write_text(''.join(lines));mapfile.write_text(json.dumps({'graph_sha256':sha(gpath),'seed_sha256':sha(spath),'slots':slots},indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'GENERATED_UNCOMPILED_DRAFT','slot_count':len(slots),'source_sha256':sha(target),'slots_sha256':sha(mapfile)},sort_keys=True,indent=2))
