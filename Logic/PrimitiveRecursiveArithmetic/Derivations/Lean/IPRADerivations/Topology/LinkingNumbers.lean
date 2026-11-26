import IPRADerivations.Core.CertificateTactics

/-!
# Linking numbers: crossing bounds and crossing changes

Packet: `topology/knot_theory_ipra`, `surface.tex`, the paragraph after the Theorem "Three crossing formulas for
linking" and the Corollary "Even two-strand torus links". The crossings between two components `i, j` are
indexed by `Fin k`, with signs `ε_p` that are integer terms of square one, and `2 ℓ = ∑_p ε_p`. As iPRA
derivations:

* `sign_le_one`, `neg_one_le_sign`: a term with `ε² = 1` has `−1 ≤ ε ≤ 1`;
* `linking_upper`, `linking_lower`: "the number of crossings between `i, j` is at least `2 |ℓ_{ij}|`":
  `2 ℓ ≤ k` and `−k ≤ 2 ℓ`;
* `crossing_change`: "A change of such a crossing changes `ℓ_{ij}` by exactly one in absolute value": if `ε′`
  agrees with `ε` except at `q`, where `ε′_q = −ε_q`, then `∑ ε′ = ∑ ε − 2 ε_q`;
* `writhe_two`: `w = w₁ + w₂ + 2 ℓ` for two components, from the sum over all crossings;
* `torus_link_linking`: the closure of `σ₁^{2r}` has `2r` crossings of sign one between its two components,
  so `2 r = ∑_p 1`: its linking number is `r`.

Not derived: the invariance of `ℓ` along movies of coded diagrams, and the resulting lower bound for the number
of crossing changes of a movie.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.LinkingNumbers

open_ipra

variable {n k : ℕ} {Γ : List (Fm PTm n)}

local macro "lsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_sq, ZT.toZ_natLit,
    ZT.toZ_sumFin, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

/-- A sign is at most one. -/
theorem sign_le_one {ε : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (ε * ε) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle ε (ZT.natLit 1) := by
  ipra_zle2 (ZT.toZ Γ (ZT.natLit 1 - ε) ^ 2) with -ZT.toZ_eq h

/-- A sign is at least minus one. -/
theorem neg_one_le_sign {ε : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (ε * ε) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (-(ZT.natLit 1)) ε := by
  ipra_zle2 (ZT.toZ Γ (ZT.natLit 1 + ε) ^ 2) with -ZT.toZ_eq h

/-- `∑_p (1 − x_p)² = 2k − 2 ∑_p x_p` for signs `x_p`. -/
theorem sum_one_sub_sq {R : Type*} [CommRing R] (x : Fin k → R) (h : ∀ p, x p * x p = 1) :
    ∑ p, (1 - x p) ^ 2 = 2 * (k : R) - 2 * ∑ p, x p := by
  have e : ∀ p, (1 - x p) ^ 2 = 2 - 2 * x p := fun p => by linear_combination h p
  rw [Finset.sum_congr rfl fun p _ => e p, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `∑_p (1 + x_p)² = 2k + 2 ∑_p x_p` for signs `x_p`. -/
theorem sum_one_add_sq {R : Type*} [CommRing R] (x : Fin k → R) (h : ∀ p, x p * x p = 1) :
    ∑ p, (1 + x p) ^ 2 = 2 * (k : R) + 2 * ∑ p, x p := by
  have e : ∀ p, (1 + x p) ^ 2 = 2 + 2 * x p := fun p => by linear_combination h p
  rw [Finset.sum_congr rfl fun p _ => e p, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `2 ℓ ≤ k`: at least `2 ℓ` crossings. -/
theorem linking_upper (ε : Fin k → ZT n) {l : ZT n}
    (h : ∀ p, Γ ⊢[PRAAx] ZT.eq (ε p * ε p) (ZT.natLit 1))
    (hl : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * l) (ZT.sumFin ε)) :
    Γ ⊢[PRAAx] zle (ZT.natLit 2 * l) (ZT.natLit k) := by
  have hsq : ∀ p, ZT.toZ Γ (ε p) * ZT.toZ Γ (ε p) = 1 := fun p => by
    have e := ZT.toZ_eq (h p)
    lsimp at e
    exact e
  have el := ZT.toZ_eq hl
  have S := sum_one_sub_sq (fun p => ZT.toZ Γ (ε p)) hsq
  beta_reduce at S
  refine zle_of_comb_two (∑ p, ZT.toZ Γ (ZT.natLit 1 - ε p) ^ 2) ?_ (nn_sum _ _ fun p _ => nn_zsq _)
  lsimp at el ⊢
  rw [S]
  linear_combination (-2 : Groth (Q Γ)) * el

/-- `−k ≤ 2 ℓ`: at least `−2 ℓ` crossings. -/
theorem linking_lower (ε : Fin k → ZT n) {l : ZT n}
    (h : ∀ p, Γ ⊢[PRAAx] ZT.eq (ε p * ε p) (ZT.natLit 1))
    (hl : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * l) (ZT.sumFin ε)) :
    Γ ⊢[PRAAx] zle (-(ZT.natLit k)) (ZT.natLit 2 * l) := by
  have hsq : ∀ p, ZT.toZ Γ (ε p) * ZT.toZ Γ (ε p) = 1 := fun p => by
    have e := ZT.toZ_eq (h p)
    lsimp at e
    exact e
  have el := ZT.toZ_eq hl
  have S := sum_one_add_sq (fun p => ZT.toZ Γ (ε p)) hsq
  beta_reduce at S
  refine zle_of_comb_two (∑ p, ZT.toZ Γ (ZT.natLit 1 + ε p) ^ 2) ?_ (nn_sum _ _ fun p _ => nn_zsq _)
  lsimp at el ⊢
  rw [S]
  linear_combination (2 : Groth (Q Γ)) * el

/-- A crossing change at `q`: `∑ ε′ = ∑ ε − 2 ε_q`. -/
theorem crossing_change (ε ε' : Fin k → ZT n) (q : Fin k)
    (hoff : ∀ p, p ≠ q → (Γ ⊢[PRAAx] ZT.eq (ε' p) (ε p)))
    (hq : Γ ⊢[PRAAx] ZT.eq (ε' q) (-(ε q))) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin ε') (ZT.sumFin ε - ZT.natLit 2 * ε q) := by
  have D : ∑ p, (ZT.toZ Γ (ε' p) - ZT.toZ Γ (ε p)) = ZT.toZ Γ (ε' q) - ZT.toZ Γ (ε q) :=
    Finset.sum_eq_single q (fun p _ hp => by rw [ZT.toZ_eq (hoff p hp), sub_self])
      (fun hn => absurd (Finset.mem_univ q) hn)
  rw [Finset.sum_sub_distrib] at D
  ipra_lc D + ZT.toZ_eq hq

/-- `w = w₁ + w₂ + 2 ℓ` for two components. -/
theorem writhe_two {w w₁ w₂ l s : ZT n}
    (hw : Γ ⊢[PRAAx] ZT.eq w (w₁ + w₂ + s)) (hl : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * l) s) :
    Γ ⊢[PRAAx] ZT.eq w (w₁ + w₂ + ZT.natLit 2 * l) := by
  ipra_lc ZT.toZ_eq hw - ZT.toZ_eq hl

/-- The closure of `σ₁^{2r}`: `2 r` is the sum of its `2r` crossing signs, all equal to one. -/
theorem torus_link_linking (r : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * ZT.natLit r) (ZT.sumFin fun _ : Fin (2 * r) => (ZT.natLit 1 : ZT n)) := by
  apply ZT.derive
  lsimp
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end LeanProofs.IPRA.Topology.LinkingNumbers
