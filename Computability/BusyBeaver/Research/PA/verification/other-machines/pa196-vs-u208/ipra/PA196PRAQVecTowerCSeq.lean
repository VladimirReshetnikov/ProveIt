import PA196PRAQVecTowerGraphStep

/-! Candidate-PRA semantics of arbitrary arithmetic tower computation
sequences. This does not assert uniqueness of an entire sequence. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PRAQVecTowerCSeq
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA196PAQVecSeqTrace PA196PRAQVecStepMonotone PA196PRAQVecTowerGraphStep
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero

theorem cseq_spec (s seed : M) : boundBlueprint.cseqDef.val.Evalb ![s,seed] ↔
    seqDef.val.Evalb ![s] ∧
    (∃ z < s, z = seed ∧ memRel.val.Evalb ![s,0,z]) ∧
    ∀ i < 2*s, (∃ l ≤ 2*s, lhDef.val.Evalb ![l,s] ∧ i+1 < l) →
      ∀ z < s, memRel.val.Evalb ![s,i,z] →
        ∃ u < s, u = majorant z ∧ memRel.val.Evalb ![s,i+1,u] := by
  have hstep (u z i : M) :
      boundSuccDef.val.Evalb (u :> z :> i :> fun _ => seed) ↔ u = majorant z := by
    have hv : (u :> z :> i :> fun _ => seed) = ![u,z,i,seed] := by
      funext j
      exact Fin.cases rfl (fun a => Fin.cases rfl (fun b =>
        Fin.cases rfl (fun c => Fin.cases rfl (fun d => Fin.elim0 d) c) b) a) j
    rw [hv]
    exact boundSucc_eval _ _ _ _
  simp [PR.Blueprint.cseqDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    Semiformula.ballLT, FirstOrder.bexs, FirstOrder.ball, Semiformula.Operator.val,
    memRelOpr, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le,
    Semiformula.Operator.Eq.sentence_eq, Matrix.comp_vecCons'',
    PRAHistoryTruncation.val_comp_bvar, boundBlueprint, zeroDef, hstep]

#print axioms cseq_spec
end PA196PRAQVecTowerCSeq
