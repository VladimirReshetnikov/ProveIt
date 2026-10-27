import DiophantineConsistency.FoundationHADeltaZeroGG

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHADeltaZeroGGChecks
open LO LO.FirstOrder HA FoundationPAHFSyntax HABoundedQuantifiers FoundationHADeltaZero
open FoundationHADeltaZeroGG
open scoped LO.FirstOrder

-- These are the literal existing source GG constructors, not a new translation.
example (bv : Fin 2 → PTerm) (fv : Nat → PTerm) :
    formulaAux bv fv (Semiformula.rel .eq ![#0,#1])ᴺ =
      doubleNeg (.eq (bv 0) (bv 1)) := rfl
example (bv : Fin 2 → PTerm) (fv : Nat → PTerm) :
    formulaAux bv fv (Semiformula.nrel .lt ![#0,#1])ᴺ =
      neg (ltFormula (bv 0) (bv 1)) := rfl
example (bv : Fin 0 → PTerm) (fv : Nat → PTerm)
    (p q : Semiformula ℒₒᵣ Nat 0) :
    formulaAux bv fv (p ⋎ q)ᴺ =
      neg (.and (neg (formulaAux bv fv pᴺ)) (neg (formulaAux bv fv qᴺ))) := rfl
example (bv : Fin 0 → PTerm) (fv : Nat → PTerm)
    (p : Semiformula ℒₒᵣ Nat 1) :
    formulaAux bv fv (∃⁰ p)ᴺ =
      neg (.all (neg (formulaAux (liftBound bv) (liftFree fv) pᴺ))) := rfl

private def sample : Semiformula ℒₒᵣ Nat 0 :=
  ∀⁰[“x. x < !!(Rew.bShift (&7 : Semiterm ℒₒᵣ Nat 0))”]
    (∃⁰[“y. y < !!(Rew.bShift (#0 : Semiterm ℒₒᵣ Nat 1))”]
      ((Semiformula.nrel .eq ![#0, &9]) ⋎ (Semiformula.rel .lt ![#0, #1])))

private theorem sample_bounded : LO.FirstOrder.Arithmetic.DeltaZero sample := by
  apply LO.FirstOrder.Arithmetic.Hierarchy.ball (Rew.bShift_positive _)
  apply LO.FirstOrder.Arithmetic.Hierarchy.bexs (Rew.bShift_positive _)
  exact .or (.nrel _ _ _ _) (.rel _ _ _ _)

example (fv : Nat → PTerm) : ProofEquiv (ordinaryAux Fin.elim0 fv sample)
    (formulaAux Fin.elim0 fv sampleᴺ) := ordinary_gg_equivalence sample_bounded _ _

example : ProofEquiv
    (ordinaryAux Fin.elim0 (fun i => .add (.var (3*i+2)) (.succ (.var 0))) sample)
    (formulaAux Fin.elim0 (fun i => .add (.var (3*i+2)) (.succ (.var 0))) sampleᴺ) :=
  ordinary_gg_equivalence sample_bounded _ _

example (fv : Nat → PTerm) (G : List F) :
    Relative SetTheory.PA.Formula.Ax_s (G.map (SetTheory.PA.Formula.rename Nat.succ))
      (.and (.imp (ordinaryAux Fin.elim0 (liftFree fv) sample)
          (formulaAux Fin.elim0 (liftFree fv) sampleᴺ))
        (.imp (formulaAux Fin.elim0 (liftFree fv) sampleᴺ)
          (ordinaryAux Fin.elim0 (liftFree fv) sample))) :=
  ordinary_gg_equivalence_relative sample_bounded _ _ _

-- Recovery explicitly requests decision of the whole existential.
example (a b : F) (h : ProofEquiv a b) (hd : Proves (dec (.ex a))) :
    Proves (.imp (neg (.all (neg b))) (.ex a)) :=
  (encoded_ex_equivalence h hd).and_right

#print axioms stable_of_decidable
#print axioms encoded_or_equivalence
#print axioms encoded_ex_forward
#print axioms not_ex_all_not
#print axioms encoded_ex_equivalence
#print axioms hierarchy_zero_equivalence
#print axioms ordinary_gg_equivalence
#print axioms ordinary_gg_equivalence_relative
#print axioms sample_bounded
end DiophantineConsistency.FoundationHADeltaZeroGGChecks
