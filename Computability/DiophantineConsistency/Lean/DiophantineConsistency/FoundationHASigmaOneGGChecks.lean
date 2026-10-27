import DiophantineConsistency.FoundationHASigmaOneGG

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHASigmaOneGGChecks
open LO LO.FirstOrder HA FoundationPAHFSyntax HABoundedQuantifiers FoundationHADeltaZero
open FoundationHADeltaZeroGG FoundationHASigmaOneGG
open scoped LO.FirstOrder

-- Literal source shapes: no new negative-translation definition is used.
example (bv : Fin 0 → PTerm) (fv : Nat → PTerm)
    (p : Semiformula ℒₒᵣ Nat 1) :
    formulaAux bv fv (∃⁰ p)ᴺ =
      neg (.all (neg (formulaAux (liftBound bv) (liftFree fv) pᴺ))) := rfl

example (bv : Fin 0 → PTerm) (fv : Nat → PTerm)
    (t : Semiterm ℒₒᵣ Nat 1) (p : Semiformula ℒₒᵣ Nat 1) :
    formulaAux bv fv (∀⁰[“x. x < !!t”] p)ᴺ =
      .all (neg (.and (doubleNeg (ltFormula (.var 0)
        (termAux (liftBound bv) (liftFree fv) t)))
        (neg (formulaAux (liftBound bv) (liftFree fv) pᴺ)))) := rfl

-- Arbitrary matrices stay double-negated; no existential decision is supplied.
example (a c : F) (h : ProofEquiv c (doubleNeg a)) :
    Proves (.imp (neg (.all (neg c))) (doubleNeg (.ex a))) :=
  (ex_doubleNeg_equiv h).and_left

example (l a c : F) (h : ProofEquiv c (doubleNeg a)) :
    ProofEquiv (neg (.and (doubleNeg l) (neg c))) (.imp l (doubleNeg a)) :=
  guard_doubleNeg_equiv h

private def sample : Semiformula ℒₒᵣ Nat 0 :=
  ∀⁰[“x. x < !!(Rew.bShift (&7 : Semiterm ℒₒᵣ Nat 0))”]
    (∃⁰ (∃⁰[“z. z < !!(Rew.bShift (#1 : Semiterm ℒₒᵣ Nat 2))”]
      ((Semiformula.nrel .eq ![#0, &9]) ⋎ (Semiformula.rel .lt ![#0, #1]))))

private theorem sample_sigma_one : Arithmetic.Hierarchy 𝚺 1 sample := by
  apply Arithmetic.Hierarchy.ball (Rew.bShift_positive _)
  apply Arithmetic.Hierarchy.exs
  apply Arithmetic.Hierarchy.bexs (Rew.bShift_positive _)
  exact .or (.nrel _ _ _ _) (.rel _ _ _ _)

private def fromPiZero : Semiformula ℒₒᵣ Nat 0 :=
  ∃⁰ ((Semiformula.rel .eq ![#0, &12]) ⋏ (Semiformula.nrel .lt ![#0, &10]))

private theorem fromPiZero_sigma_one : Arithmetic.Hierarchy 𝚺 1 fromPiZero :=
  .sigma (.and (.rel _ _ _ _) (.nrel _ _ _ _))

example (fv : Nat → PTerm) : ProofEquiv (formulaAux Fin.elim0 fv sampleᴺ)
    (doubleNeg (ordinaryAux Fin.elim0 fv sample)) := sigma_one_doubleNeg sample_sigma_one _ _

example : ProofEquiv
    (formulaAux Fin.elim0 (fun i => .add (.var (3*i+2)) (.succ (.var 0))) fromPiZeroᴺ)
    (doubleNeg (ordinaryAux Fin.elim0 (fun i => .add (.var (3*i+2)) (.succ (.var 0))) fromPiZero)) :=
  sigma_one_doubleNeg fromPiZero_sigma_one _ _

example (fv : Nat → PTerm) (G : List F) :
    Relative SetTheory.PA.Formula.Ax_s (G.map (SetTheory.PA.Formula.rename Nat.succ))
      (.and (.imp (formulaAux Fin.elim0 (liftFree fv) sampleᴺ)
          (doubleNeg (ordinaryAux Fin.elim0 (liftFree fv) sample)))
        (.imp (doubleNeg (ordinaryAux Fin.elim0 (liftFree fv) sample))
          (formulaAux Fin.elim0 (liftFree fv) sampleᴺ))) :=
  sigma_one_doubleNeg_relative sample_sigma_one _ _ _

example (p : Semiformula ℒₒᵣ Nat 1) (hp : Arithmetic.Hierarchy 𝚺 1 p)
    (fv : Nat → PTerm) :
    let q := ∀⁰[“x. x < !!(Rew.bShift (.func .zero Fin.elim0 : Semiterm ℒₒᵣ Nat 0))”] p
    ProofEquiv (formulaAux Fin.elim0 fv qᴺ) (doubleNeg (ordinaryAux Fin.elim0 fv q)) :=
  sigma_one_doubleNeg (.ball (Rew.bShift_positive _) hp) _ _

#print axioms negative_doubleNeg
#print axioms neg_of_doubleNeg_equiv
#print axioms and_doubleNeg_equiv
#print axioms or_doubleNeg_equiv
#print axioms ex_doubleNeg_equiv
#print axioms guard_doubleNeg_equiv
#print axioms hierarchy_sigma_one_doubleNeg
#print axioms sigma_one_doubleNeg
#print axioms sigma_one_doubleNeg_relative
#print axioms sample_sigma_one
#print axioms fromPiZero_sigma_one
end DiophantineConsistency.FoundationHASigmaOneGGChecks
