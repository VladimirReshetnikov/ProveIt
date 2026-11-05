#!/usr/bin/env python3
"""Generate an uncompiled forward bridge using reviewed static slot maps."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];slotsfile=D/'research/nine-sharing-norm38-slot-extraction-draft/slots.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(slotsfile)=='f3b2a0ea47962596d8753533c363a6b3e0b4121cd3150722181581d9085326a4';slots=json.loads(slotsfile.read_text())['slots'];assert len(slots)==29
lines=['''import DiophantineConsistency.Norm38Reference
import DiophantineConsistency.ForwardWitness38
import FreshCarrierSpheres

/-! UNCOMPILED DRAFT. Forward construction, static-to-seed reconstruction,
and a conditional source-zero-to-seed-zero theorem. Imports and all proposed
proof scripts remain unchecked. No iPRA endpoint is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Forward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction

/-- The natural constructor preserves the first fourteen input coordinates. -/
theorem forward_prefix {S : Type*} [CommSemiring S]
    (ports : Fin 4 → S) (u : Fin 14 → S) (j : Fin 14) :
    SharingForward38.witnessCoordinates ports u
      (Fin.castLE (by decide : 14 ≤ 38) j) = u j := by
  fin_cases j <;> simp [SharingForward38.witnessCoordinates]

/-- Candidate direct verification of all 60 static gate equations for the
generated natural constructor. No source norm hypothesis is used here. -/
theorem forward_gatesHold {S R : Type*} [CommSemiring S] [CommRing R]
    (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    NormAssignment38.gatesHold embed ports
      (SharingForward38.witnessCoordinates ports u) := by
  unfold NormAssignment38.gatesHold
  simp only [NormAssignment38.gates, List.mem_cons, forall_eq_or_imp]
  repeat' constructor
  all_goals simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul]

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The five original unit norms imply the static graph's five targets for
the generated witness, using the separately drafted source-reference theorem. -/
theorem forward_fiveNorms (ports : Fin 4 → V) (u : Fin 14 → V)
    (hu : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j + 1))
      d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1) :
    NormAssignment38.fiveNorms ι ports
      (SharingForward38.witnessCoordinates ports u) := by
  let w := SharingForward38.witnessCoordinates ports u
  have hg : NormAssignment38.gatesHold ι ports w := forward_gatesHold ι ports u
  have ht := Norm38Reference.static_terminals_agree ports w hg
  simp only [w, forward_prefix] at ht
  have hc := Norm38Reference.reference_terminal_fields (fun j => ι (ports j))
    (fun j => ι (u j + 1))
  have hscale := Carrier65.strong_scale (fun j => ι (ports j)) (fun j => ι (u j + 1))
  rcases ht with ⟨ht0,ht1,hta,htt,hts,htd⟩
  rcases hc with ⟨hc0,hc1,hca,hct,hcs,hcd⟩
  rcases hu with ⟨hP,hQ,hU,hStrong,hW⟩
  have hZ : (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j + 1))).Z =
      (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j + 1))).delta := by
    rw [hscale,hStrong,mul_one]
  unfold NormAssignment38.fiveNorms
  exact ⟨ht0.trans (hc0.trans hP), ht1.trans (hc1.trans hQ),
    hta.trans (hca.trans hU), htt.trans (hct.trans hW),
    hts.trans (hcs.trans (hZ.trans (hcd.symm.trans htd.symm)))⟩

/-- Candidate reverse use of the literal slot identities: all static gate and
norm constraints make every squared residual zero. -/
theorem static_implies_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hg : NormAssignment38.gatesHold ι ports w)
    (hn : NormAssignment38.fiveNorms ι ports w) :
    InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w) := by
  unfold NormAssignment38.gatesHold at hg
  unfold NormAssignment38.fiveNorms at hn
  rcases hn with ⟨hn0,hn1,hna,hnt,hns⟩
''']
import re
seen={}
for s in slots:
 if s['kind']=='norm':continue
 m=re.fullmatch(r'(positive|negative)Residual ι GateOp\.(add|sub|mul) \(v (\d+)\) \(v (\d+)\) \(v (\d+)\)',s['rhs']);assert m,s
 kind,op,left,right,target=m.groups();entry=(op,int(left),int(right),int(target));assert s['gate'] not in seen or seen[s['gate']]==entry;seen[s['gate']]=entry
for name,(op,left,right,target) in seen.items():
 lines.append(f'  have gate_{target} := hg ⟨{target}, {left}, {right}, GateOp.{op}⟩ (by simp [NormAssignment38.gates])\n')
normnames={'N0':'hn0','N1':'hn1','Na':'hna','Nt':'hnt','scaled_Ns':'hns'}
for s in slots:
 i=s['slot'];kind=s['kind'];lines.append(f'  have hz{i:02d} : InternalZero (residualAt p {i}) (Fin.cons (1 : V) w) := by\n    rw [internalZero_iff, slot{i:02d} p ports w hp]\n')
 if kind=='norm':lines.append(f"    exact sub_eq_zero.mpr {normnames[s['gate']]}\n")
 else:
  target=seen[s['gate']][3];proj='1' if kind=='positive' else '2';lines.append(f'    exact gate_{target}.{proj}\n')
lines.append('''  have all (i : Fin 29) : InternalZero (residualAt p i) (Fin.cons (1 : V) w) := by
    fin_cases i <;> assumption
  apply (SharingNormSquares.seed_zero_iff_residuals p (Fin.cons (1 : V) w)).mpr
  intro e he
  obtain ⟨j,hj⟩ := List.get_of_mem he
  let i : Fin 29 := ⟨j.val, by simpa [residuals, SharingSeed38.remainingResiduals] using j.isLt⟩
  have hi := all i
  simpa [residualAt, residuals, hj] using hi

/-- Conditional forward bridge: actual source zero supplies the five norms,
and the generated natural witness gives a literal seed zero. -/
theorem source_zero_implies_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V)
    (u : Fin 14 → V) (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hb : (0 : DiffRing V) < ((p 0 : ℤ) : DiffRing V))
    (hs : InternalZero (ObjectCurrentEquation2011.expressionAt p) (fun j => u j+1)) :
    InternalZero (SharingSeed38.seed p)
      (Fin.cons (1 : V) (SharingForward38.witnessCoordinates ports u)) := by
  have hvalue : Carrier65.value (fun j => ι (ports j)) (fun j => ι (u j+1)) = 0 := by
    rw [internalZero_iff, FreshModel106.evalRing_expressionAt65] at hs
    simpa only [hp] using hs
  have hbeta : (0 : DiffRing V) < ι (ports 0) := by simpa only [hp] using hb
  have hpositive : ∀ j, (0 : DiffRing V) < ι (u j+1) := fun j =>
    ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  have hnorm := (FreshCarrierSpheres.value65_zero_iff_norms FreshCarrierSpheres.modelFacts
    (fun j => ι (ports j)) (fun j => ι (u j+1)) hbeta hpositive).mp hvalue
  exact static_implies_seed_zero p ports _ hp (forward_gatesHold ι ports u)
    (forward_fiveNorms ports u hnorm)
end Model
-- Still required: Lean checks, actual fixed-port cast proofs, reverse
-- combination, Jones instantiation and the iPRA consistency endpoint.
end DiophantineConsistency.Norm38Forward
''')
target=P/'Norm38Forward.lean';assert not target.exists();target.write_text(''.join(lines));print(json.dumps({'status':'GENERATED_UNCOMPILED_DRAFT','source_sha256':sha(target),'slot_count':len(slots),'materialized_gates':len(seen)},indent=2,sort_keys=True))
