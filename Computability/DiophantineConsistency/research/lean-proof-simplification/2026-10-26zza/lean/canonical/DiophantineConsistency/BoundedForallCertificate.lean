import Diophantine.Common.MRDPCore

/-!
# A polynomial-parameter CRT certificate for bounded quantification

This exports the local certificate proved in `MRDP.boundedForall_dioph`.
The input polynomials are supplied directly: no representation is chosen
from a proposition. This interface will support the executable compiler.
The proof is the existing MRDP argument, with only its parameters exposed.
-/

namespace DiophantineConsistency

open Dioph Finset List MvPolynomial Nat MRDP
open scoped Vector3

local notation:max "evalRow" x:max k:max w:max =>
  MvPolynomial.eval (Sum.elim (Option.elim' k x) w)

/-- A fixed finite arithmetic certificate replaces all rows below N. -/
theorem boundedForallCertificate {σ : Type} {m : ℕ}
    (e f : MvPolynomial (Option σ ⊕ Fin m) ℕ) (N : ℕ) (x : σ → ℕ) :
    let bound k u := evalRow x k u (e + f) + N
    (∃ u : Fin m → ℕ, let T := (bound N u)!
      ∃ a : Fin m → ℕ, ∃ v : Vector3 ℕ 1,
      (∀ i, encodedModuliProduct N T ∣ ∏ t ∈ range (u i + 1), (a i - t)) ∧
      crtModulus T v.head ≡ 0 [MOD encodedModuliProduct N T] ∧
      evalRow x v.head a e ≡ evalRow x v.head a f [MOD encodedModuliProduct N T]) ↔
    ∀ k < N, ∃ w : Fin m → ℕ, evalRow x k w e = evalRow x k w f := by
  intro bound
  constructor
  · -- Decode one row of a certificate.
    rintro ⟨u, a, v, hWitness_product, hIndex, hEvaluation⟩ k hk
    let T := (bound N u)!
    have hScale_pos := factorial_pos <| bound N u
    have ⟨p, hp, hpk⟩ := @exists_prime_and_dvd (crtModulus T k) <| by lia
    have hPrime_product := hpk.trans <|
      encodedModuliProduct_eq_prod hScale_pos ▸ dvd_prod_of_mem _ <| Finset.mem_range.mpr hk
    -- Decode every witness coordinate by the same canonical residue operation.
    let j := fun i => a i % p
    have hWitness_bound i : j i ≤ u i :=
      (prime_dvd_descendingProduct_iff hp).mp (hPrime_product.trans (hWitness_product i))
    have hWitness_congruence i : a i ≡ j i [MOD p] := (mod_modEq _ _).symm
    have hCoprime : p.Coprime T := Nat.Coprime.of_dvd_left hpk (by simp)
    -- A prime coprime to (bound N u)! exceeds both decoded polynomial values.
    have hRow_bound : bound k j < p :=
      lt_of_le_of_lt (by
        unfold bound
        polynomial_congr) <|
        not_le.mp <| hp.dvd_factorial.not.mp <|
          hp.coprime_iff_not_dvd.mp hCoprime
    -- Cancel the common factorial scale to recover the row-index congruence.
    have hIndex_congruence :=
      ModEq.cancel_right_of_coprime hCoprime <|
        ModEq.add_right_cancel' _ <| (hIndex.of_dvd hPrime_product).trans hpk.zero_modEq_nat
    have hPolynomial_congruence g : evalRow x v.head a g ≡ evalRow x k j g [MOD p] := by
      polynomial_congr
    existsi j
    -- Both evaluations are below p, so congruence is actual equality.
    grind [eval_add, ModEq, = Nat.mod_eq_of_lt, hEvaluation.of_dvd hPrime_product]
  · -- Encode a family of row witnesses using the Chinese remainder theorem.
    choose! w hRows
    -- Take the coordinatewise maximum of the witnesses over the finite range.
    let u := sup (range N) w
    existsi u
    intro T
    have hPairwise_coprime : (List.range N).Pairwise (Coprime.onFun <| crtModulus T) :=
      List.pairwise_lt_range.imp_of_mem <| by
        intros
        apply coprime_mul_succ
        apply dvd_factorial <;> grind
    -- Encode the row indices once, then encode each witness coordinate separately.
    have ⟨c, hIndex_residue⟩ := chineseRemainderOfList id _ _ hPairwise_coprime
    have ⟨a, hWitness_residue⟩ :=
      Equiv.subtypePiEquivPi.symm <|
        (chineseRemainderOfList · _ _ hPairwise_coprime) ∘' Function.swap w
    existsi a, [c], fun i => modEq_zero_iff_dvd.mp ?_, ?_ <;>
      erw [encodedModuliProduct_eq_prod (factorial_pos _)] <;>
      apply modEq_list_map_prod_iff hPairwise_coprime |>.2 <;>
      intro k hk
    · exact
        Dvd.dvd.modEq_zero_nat <|
          (dvd_of_mod_eq_zero <| sub_mod_eq_zero_of_mod_eq <| hWitness_residue i _ hk).trans <|
            dvd_prod_of_mem _ <| mem_range_succ_iff.mpr <| Pi.le_def.mp (le_sup hk) i
    · apply ModEq.trans _ dvd_rfl.modEq_zero_nat
      unfold crtModulus
      gcongr
      exact?
    · have hPolynomial_congruence g :
          evalRow x c a g ≡ evalRow x k (w k) g [MOD crtModulus T k] := by
        polynomial_congr
      dsimp [Vector3.head]
      grind [ModEq]

end DiophantineConsistency
