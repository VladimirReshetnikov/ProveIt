import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic

/-!
Focused check of the complete forward decoding argument. The sole abstract input
is the existing encoded-moduli product identity. The original reverse encoding
and the Diophantine syntax proof are outside this check.
-/
namespace CanonicalResidueCheck

open Finset List MvPolynomial Nat

abbrev crtModulus (scale index : ℕ) := (index + 1) * scale + 1

local notation:max "evalRow" x:max k:max w:max =>
  MvPolynomial.eval (Sum.elim (Option.elim' k x) w)

macro "polynomial_congr" : tactic =>
  `(tactic| focus
    simp [eval_eq]
    gcongr <;> exact by
      cases_type* _root_.Sum Option <;> exact?)

/-- A prime divides a truncated descending product exactly when the least residue lies in its interval. -/
theorem prime_dvd_descendingProduct_iff {p a u : ℕ} (hp : p.Prime) :
    p ∣ ∏ t ∈ range (u + 1), (a - t) ↔ a % p ≤ u := by
  constructor
  · intro h
    obtain ⟨t, ht, hpt⟩ := hp.prime.exists_mem_finset_dvd h
    have heq : a % p = min a t % p :=
      (modEq_sub (min_le_left ..)).of_dvd (Nat.sub_eq_sub_min .. ▸ hpt)
    calc
      a % p = min a t % p := heq
      _ ≤ min a t := Nat.mod_le _ _
      _ ≤ t := min_le_right _ _
      _ ≤ u := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
  · intro h
    exact (Nat.dvd_sub_mod a).trans
      (dvd_prod_of_mem _ (mem_range_succ_iff.mpr h))

/-- The modified forward decoder, with the unchanged moduli-product identity supplied. -/
theorem decodeCanonicalRow {σ : Type} {m : ℕ}
    (e f : MvPolynomial (Option σ ⊕ Fin m) ℕ) (N M : ℕ) (x : σ → ℕ)
    (u a : Fin m → ℕ) (c : ℕ) :
    let bound k u := evalRow x k u (e + f) + N
    let T := (bound N u)!
    M = ∏ t ∈ range N, crtModulus T t →
    (∀ i, M ∣ ∏ t ∈ range (u i + 1), (a i - t)) →
    crtModulus T c ≡ 0 [MOD M] →
    evalRow x c a e ≡ evalRow x c a f [MOD M] →
    ∀ k < N, ∃ w : Fin m → ℕ, evalRow x k w e = evalRow x k w f := by
  intro bound T hProduct hWitness_product hIndex hEvaluation k hk
  have hScale_pos := factorial_pos <| bound N u
  have ⟨p, hp, hpk⟩ := @exists_prime_and_dvd (crtModulus T k) <| by lia
  have hPrime_product := hpk.trans <|
    hProduct ▸ dvd_prod_of_mem _ <| Finset.mem_range.mpr hk
  -- This is exactly the replacement block in both complete candidate sources.
  let j := fun i => a i % p
  have hWitness_bound i : j i ≤ u i :=
    (prime_dvd_descendingProduct_iff hp).mp (hPrime_product.trans (hWitness_product i))
  have hWitness_congruence i : a i ≡ j i [MOD p] := (mod_modEq _ _).symm
  have hCoprime : p.Coprime T := Nat.Coprime.of_dvd_left hpk (by simp)
  have hRow_bound : bound k j < p :=
    lt_of_le_of_lt (by
      unfold bound
      polynomial_congr) <|
      not_le.mp <| hp.dvd_factorial.not.mp <|
        hp.coprime_iff_not_dvd.mp hCoprime
  have hIndex_congruence :=
    ModEq.cancel_right_of_coprime hCoprime <|
      ModEq.add_right_cancel' _ <| (hIndex.of_dvd hPrime_product).trans hpk.zero_modEq_nat
  have hPolynomial_congruence g : evalRow x c a g ≡ evalRow x k j g [MOD p] := by
    polynomial_congr
  existsi j
  grind [eval_add, ModEq, = Nat.mod_eq_of_lt, hEvaluation.of_dvd hPrime_product]

#print axioms prime_dvd_descendingProduct_iff
#print axioms decodeCanonicalRow

end CanonicalResidueCheck
