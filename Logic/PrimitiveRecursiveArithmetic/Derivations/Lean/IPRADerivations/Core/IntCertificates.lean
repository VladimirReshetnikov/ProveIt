import IPRADerivations.Core.IntOrder
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearAlgebra

/-!
# Certificates for inequalities between integer terms

`Core/OrderCertificates` derives a natural inequality `a ≤ b` from a certificate: a `Nonneg` element `z` of the
ring of differences `Groth (Q Γ)` with `ι b − ι a = z`. This module does the same for integer terms
(`ZT`, pairs read as differences) and their order `zle`, so that signed rational estimates, cleared of
denominators, become iPRA derivations:

* `zsl h` is the slack `toZ v − toZ u` of a derived `h : Γ ⊢ zle u v`, and it is `Nonneg` (`nn_zsl`);
* `zle_of_comb`: `toZ v − toZ u = z` with `z` `Nonneg` gives `Γ ⊢ zle u v`;
* `zle_of_comb_two`: the same from `2 (toZ v − toZ u) = z`, for certificates with a factor `1/2` such as
  `2(AB − ab) = (A − a)(B + b) + (A + a)(B − b)` (via `le_of_two_mul`, halving natural inequalities);
* `nn_sum` (finite sums), `nn_zle0` (`0 ≤ u` makes `toZ u` `Nonneg`), `nn_zsq` (`toZ u ^ 2` is `Nonneg`, being
  `|u|^2`);
* `pair_sq` and `cauchy_nat`: the finite Cauchy inequality `(∑ aᵢ)² ≤ d ∑ aᵢ²` for natural terms, from
  `∑ᵢ ∑ⱼ (aᵢ − aⱼ)² = 2 (d ∑ aᵢ² − (∑ aᵢ)²)`;
* `false_of_comb`: a `Nonneg` certificate equal to `−1` derives every formula;
* `zabs_mul`: two-sided bounds `−A ≤ a ≤ A`, `−B ≤ b ≤ B` give `−AB ≤ ab ≤ AB`, from
  `2(AB ∓ ab) = (A ∓ a)(B + b) + (A ± a)(B − b)`;
* the tactics `zsimp` (push `toZ` through a goal), `znn` (prove `Nonneg` from slacks `zsl`/`sl`, squares
  `toZ u ^ 2`, values of terms and numerals) and `ipra_zle z` (derive `zle u v` from the certificate `z`).
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open PTm (pred monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The slack `v − u` of a derived `zle u v`. -/
def zsl {u v : ZT n} (_ : Γ ⊢[PRAAx] zle u v) : Groth (Q Γ) := ZT.toZ Γ v - ZT.toZ Γ u

theorem zsl_def {u v : ZT n} (h : Γ ⊢[PRAAx] zle u v) : zsl h = ZT.toZ Γ v - ZT.toZ Γ u := rfl

theorem nn_zsl {u v : ZT n} (h : Γ ⊢[PRAAx] zle u v) : Nonneg Γ (zsl h) := by
  have e := zle_toZ h
  exact ⟨monus (v.pos + u.neg) (u.pos + v.neg), by rw [zsl_def]; linear_combination -e⟩

/-- An integer inequality from a certificate. -/
theorem zle_of_comb {u v : ZT n} (z : Groth (Q Γ)) (hz : ZT.toZ Γ v - ZT.toZ Γ u = z) (h : Nonneg Γ z) :
    Γ ⊢[PRAAx] zle u v := by
  obtain ⟨d, hd⟩ := h
  exact zle_of_toZ d (by linear_combination -(hz.trans hd))

theorem nn_sum {ι : Type*} (s : Finset ι) (f : ι → Groth (Q Γ)) (h : ∀ i ∈ s, Nonneg Γ (f i)) :
    Nonneg Γ (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Nonneg Γ) (fun _ _ => nn_add) nn_zero h

theorem nn_zle0 {u : ZT n} (h : Γ ⊢[PRAAx] zle (ZT.natLit 0) u) : Nonneg Γ (ZT.toZ Γ u) := by
  have := nn_zsl h
  rwa [zsl_def, ZT.toZ_natLit, Nat.cast_zero, sub_zero] at this

theorem nn_zsq (u : ZT n) : Nonneg Γ (ZT.toZ Γ u ^ 2) := by
  rw [← ZT.toZ_sq, sq_nat]
  exact nn_term _

/-- Halving: `2a ≤ 2b` gives `a ≤ b`. -/
theorem le_of_two_mul {a b : PTm n} (h : Γ ⊢[PRAAx] le (num 2 * a) (num 2 * b)) : Γ ⊢[PRAAx] le a b := by
  refine .orE (lt_or_le b a) ?_ Prf.hyp0
  have h' := h.wk (ψ := lt b a)
  have hl : (lt b a :: Γ) ⊢[PRAAx] le (succ b) a := Prf.hyp0
  have bad : (lt b a :: Γ) ⊢[PRAAx] le (succ (num 2 * b)) (num 2 * b) := by
    ipra_le sl h' + 2 * sl hl + 1
  exact not_succ_le_self _ _ bad

/-- An integer inequality from a certificate for twice the slack. -/
theorem zle_of_comb_two {u v : ZT n} (z : Groth (Q Γ)) (hz : 2 * (ZT.toZ Γ v - ZT.toZ Γ u) = z)
    (h : Nonneg Γ z) : Γ ⊢[PRAAx] zle u v := by
  apply le_of_two_mul
  refine le_of_comb z ?_ h
  rw [← hz, toZ_def, toZ_def]
  ipra_simps
  ring

/-- A `Nonneg` certificate equal to `−1` is contradictory. -/
theorem false_of_comb (z : Groth (Q Γ)) (hz : z = -1) (h : Nonneg Γ z) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  have bad : Γ ⊢[PRAAx] le (succ zero) zero := by
    refine le_of_comb z ?_ h
    rw [hz]
    ipra_simps
    ring
  exact not_succ_le_self _ _ bad

/-- `∑ᵢ ∑ⱼ (xᵢ − xⱼ)² = 2 (d ∑ xᵢ² − (∑ xᵢ)²)` in every commutative ring. -/
theorem pair_sq {R : Type*} [CommRing R] {d : ℕ} (x : Fin d → R) :
    ∑ i, ∑ j, (x i - x j) ^ 2 = 2 * ((d : R) * ∑ i, x i ^ 2 - (∑ i, x i) ^ 2) := by
  have e : ∀ i j, (x i - x j) ^ 2 = x i ^ 2 + x j ^ 2 - 2 * (x i * x j) := fun i j => by ring
  simp only [e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The finite Cauchy inequality for integer terms: `(∑ uᵢ)² ≤ d ∑ uᵢ²`. -/
theorem cauchy_int {d : ℕ} (u : Fin d → ZT n) :
    Γ ⊢[PRAAx] zle (ZT.sq (ZT.sumFin u)) (ZT.natLit d * ZT.sumFin fun i => ZT.sq (u i)) := by
  refine zle_of_comb_two (∑ i, ∑ j, ZT.toZ Γ (u i - u j) ^ 2) ?_
    (nn_sum _ _ fun i _ => nn_sum _ _ fun j _ => nn_zsq _)
  simp only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sq, ZT.toZ_natLit, ZT.toZ_sumFin]
  rw [pair_sq (fun i => ZT.toZ Γ (u i))]

/-- `−A ≤ a ≤ A` and `−B ≤ b ≤ B` give `−AB ≤ ab ≤ AB`. -/
theorem zabs_mul {a A b B : ZT n} (ha₁ : Γ ⊢[PRAAx] zle (-A) a) (ha₂ : Γ ⊢[PRAAx] zle a A)
    (hb₁ : Γ ⊢[PRAAx] zle (-B) b) (hb₂ : Γ ⊢[PRAAx] zle b B) :
    (Γ ⊢[PRAAx] zle (-(A * B)) (a * b)) ∧ (Γ ⊢[PRAAx] zle (a * b) (A * B)) := by
  refine ⟨zle_of_comb_two (zsl ha₁ * zsl hb₁ + zsl ha₂ * zsl hb₂) ?_
      (nn_add (nn_mul (nn_zsl _) (nn_zsl _)) (nn_mul (nn_zsl _) (nn_zsl _))),
    zle_of_comb_two (zsl ha₂ * zsl hb₁ + zsl ha₁ * zsl hb₂) ?_
      (nn_add (nn_mul (nn_zsl _) (nn_zsl _)) (nn_mul (nn_zsl _) (nn_zsl _)))⟩ <;>
  · simp only [zsl_def, ZT.toZ_neg, ZT.toZ_mul]
    ring

end LeanProofs.IPRA

/-- Push `ZT.toZ` through sums, products, squares and numerals, and unfold integer slacks. -/
macro "zsimp" : tactic =>
  `(tactic| simp only [LeanProofs.IPRA.zsl_def, LeanProofs.IPRA.sl_def, LeanProofs.IPRA.ZT.toZ_add,
    LeanProofs.IPRA.ZT.toZ_sub, LeanProofs.IPRA.ZT.toZ_mul, LeanProofs.IPRA.ZT.toZ_neg,
    LeanProofs.IPRA.ZT.toZ_sq, LeanProofs.IPRA.ZT.toZ_natLit, LeanProofs.IPRA.ZT.toZ_ofNat,
    LeanProofs.IPRA.ZT.toZ_sumFin, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one])

/-- Prove `Nonneg Γ z` for `z` built from integer and natural slacks, squares of integer values, values of
terms and numerals (and `Nonneg` hypotheses) by `+`, `*` and powers. -/
macro "znn" : tactic =>
  `(tactic| repeat (with_reducible first
      | exact LeanProofs.IPRA.nn_zsl _
      | exact LeanProofs.IPRA.nn_sl _
      | exact LeanProofs.IPRA.nn_zsq _
      | exact LeanProofs.IPRA.nn_term _
      | exact LeanProofs.IPRA.nn_one
      | exact LeanProofs.IPRA.nn_zero
      | exact LeanProofs.IPRA.nn_ofNat _
      | exact LeanProofs.IPRA.nn_natCast _
      | assumption
      | apply LeanProofs.IPRA.nn_add
      | apply LeanProofs.IPRA.nn_mul
      | apply LeanProofs.IPRA.nn_pow))

/-- `ipra_zle z` derives `Γ ⊢ zle u v` from the certificate `z` (`toZ v − toZ u = z` by `ring`). -/
macro "ipra_zle " z:term : tactic =>
  `(tactic| (
      refine LeanProofs.IPRA.zle_of_comb $z ?_ ?_
      · zsimp; ring
      · znn))
