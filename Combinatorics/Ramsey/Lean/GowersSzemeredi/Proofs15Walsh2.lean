import GowersSzemeredi.Proofs15Walsh

/-!
# Proven companion for Gowers (2001), Corollary 15.2
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private theorem parityCharacter_eq_prod {N k : Nat}
    (e : Fin k → Bool) :
    parityCharacter (N := N) e =
      ∏ i : Fin k,
        if e i then (-1 : ZMod N) else 1 := by
  classical
  simp only [parityCharacter, boolWeight, countWhere]
  rw [← Finset.prod_const]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : e i = true <;> simp [h]

private theorem walshProduct_eq_parity {N k : Nat}
    (e : Fin k → Bool) :
    (∏ i : Fin k, walshSign (N := N) (e i)) =
      (-1 : ZMod N) ^ k * parityCharacter (N := N) e := by
  classical
  rw [parityCharacter_eq_prod]
  have hconst :
      (-1 : ZMod N) ^ k =
        ∏ _i : Fin k, (-1 : ZMod N) := by simp
  rw [hconst, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases e i <;> simp [walshSign]

/-- **Corollary 15.2.** Translate the Boolean cube to the sign cube and
apply Lemma 15.1 with half-sidelengths. -/
theorem corollary_15_2_holds : corollary_15_2 := by
  unfold corollary_15_2
  intro N k _ hprime hodd h eta hh heta hinvariant
  letI : Fact (Nat.Prime N) := ⟨hprime⟩
  have hNgt : 2 < N := by
    have hle := hprime.two_le
    have hne : N ≠ 2 := by
      intro hN
      subst N
      exact hodd.not_two_dvd_nat (dvd_refl 2)
    omega
  have htwo : (2 : ZMod N) ≠ 0 := by
    intro hz
    have hdvd : N ∣ 2 :=
      (CharP.cast_eq_zero_iff (ZMod N) N 2).mp hz
    exact (Nat.not_le_of_lt hNgt)
      (Nat.le_of_dvd (by omega) hdvd)
  let hhalf : Point N k :=
    fun i => h i / (2 : ZMod N)
  have hhalf_ne : ∀ i, hhalf i ≠ 0 := by
    intro i
    exact div_ne_zero (hh i) htwo
  have hcoord :
      ∀ (y : Point N k) (i : Fin k) (b : Bool),
        y i + walshSign (N := N) b * hhalf i =
          (y i - hhalf i) + if b then h i else 0 := by
    intro y i b
    dsimp only [hhalf]
    cases b <;> simp only [walshSign] <;> norm_num <;>
      field_simp [htwo] <;> ring
  have hmom :
      ∀ (A : Finset (Fin k)) (y : Point N k),
        signedWalshMoment eta hhalf y A =
          booleanWalshMoment eta h
            (fun i => y i - hhalf i) A := by
    intro A y
    unfold signedWalshMoment booleanWalshMoment
    apply Finset.sum_congr rfl
    intro e he
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact hcoord y i (e i)
  have hsigned :
      ∀ (A : Finset (Fin k)) (y z : Point N k),
        signedWalshMoment eta hhalf y A =
          signedWalshMoment eta hhalf z A := by
    intro A y z
    rw [hmom A y, hmom A z]
    exact hinvariant A _ _
  obtain ⟨c, hc⟩ :=
    lemma_15_1_holds N k hprime hodd hhalf eta
      hhalf_ne heta hsigned
  refine ⟨c * (-1 : ZMod N) ^ k, ?_⟩
  intro e
  rw [hc e]
  change
    c * (∏ i : Fin k, walshSign (N := N) (e i)) =
      c * (-1 : ZMod N) ^ k *
        parityCharacter (N := N) e
  rw [walshProduct_eq_parity]
  ring

end LeanProofs.GowersSzemeredi
