import IPRADerivations.Core.IntCertificates

/-!
# Approximate Brouwer fixed points: the certificate-to-error steps

Packet: `topology/approximate_brouwer_ipra`, `brouwer.tex` and `parity.tex`, the finite arithmetic that turns a
fully coloured cell into a residual bound, as iPRA derivations about integer terms (`ZT`, rational data cleared
by a common multiple `J`) and natural terms:

* `gap_mesh` (`eq:sperner-gap-mesh`): "the coordinates of `v^t − v^s` belong to `{0,1}`", so every gap
  `a_i = u_{i+1} − u_i` changes by at most one;
* `label_nonneg`, `label_max` (Lemma `lem:finite`, the tie rule): "Outside [the support], `r_j = −q_j ≤ 0`.
  The residuals on the support sum to `∑_{X_j = 0} q_j ≥ 0`, so their maximum is nonnegative. The chosen index
  is therefore a global maximizer";
* `transport`: `|R_j − (X_j(w) − q_j(w))| ≤ E` for `E = N^{-1} + ω`, from the gap mesh and the sample bound;
* `pair_gap`: "At `w_i` the largest residual is the `i`th. Comparing there and at the anchor gives
  `R_j − R_i ≤ 2E`";
* `avg_upper`, `avg_lower`: "Since `∑ R_i = 0`, `(d+1) R_j = ∑_i (R_j − R_i) ≤ 2dE` … In each sum the `i = j`
  term vanishes": the sum over the other `d` colours;
* `main_bound` (`eq:main`): `(2d/(d+1)) (N^{-1} + 2^{-m}) ≤ (d/(d+1)) 2^{-k}` for `m = k + 2`, `2^m ≤ N`;
* `transfer_residual` ("How to transfer the witness"): a `2^b`-Lipschitz retraction turns residual `δ` into
  `2^b δ`;
* `cube_anchor` ("A direct cube proof"): the two sign inequalities, transported to the initial vertex, give
  `|u_j − y_j| ≤ N^{-1} + ω`;
* `ball_outer`, `ball_mixed` (Corollary `cor:ball`): for `R(z) = z / max(1, ∑ z_j²)` the rational identities
  `‖R(z) − R(w)‖² = ‖z − w‖²/(st)` (cleared: `‖t z − s w‖² = s t ‖z − w‖²`) and
  `‖z − w‖² − ‖R(z) − w‖² = (1 − 1/s)(‖z − w‖² + 1 − t) ≥ 0` (cleared: `‖z − s w‖² ≤ s² ‖z − w‖²`);
* `sq_sum_le`: "`‖v‖_2² ≤ d ‖v‖²`" in the maximum norm.

The dimension-uniform Sperner parity (`parity.tex`) is not derived here; the cubical parity in every fixed
dimension is `Topology/SpernerCube`.
-/

namespace LeanProofs.IPRA.Topology.ApproximateBrouwer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem ztrans {a b c : ZT n} (h₁ : Γ ⊢[PRAAx] zle a b) (h₂ : Γ ⊢[PRAAx] zle b c) : Γ ⊢[PRAAx] zle a c := by
  ipra_zle zsl h₁ + zsl h₂

/-! ## The gap mesh -/

/-- `eq:sperner-gap-mesh`: increments `δ_i, δ_{i+1} ∈ [0, 1]` change the gap `u_{i+1} − u_i` by at most one. -/
theorem gap_mesh {δ₀ δ₁ : ZT n} (h₀ : Γ ⊢[PRAAx] zle (ZT.natLit 0) δ₀) (h₀' : Γ ⊢[PRAAx] zle δ₀ (ZT.natLit 1))
    (h₁ : Γ ⊢[PRAAx] zle (ZT.natLit 0) δ₁) (h₁' : Γ ⊢[PRAAx] zle δ₁ (ZT.natLit 1)) :
    (Γ ⊢[PRAAx] zle (-(ZT.natLit 1)) (δ₁ - δ₀)) ∧ (Γ ⊢[PRAAx] zle (δ₁ - δ₀) (ZT.natLit 1)) := by
  refine ⟨?_, ?_⟩
  · ipra_zle zsl h₁ + zsl h₀'
  · ipra_zle zsl h₁' + zsl h₀

/-! ## The label is a global maximizer -/

theorem nonpos_of {r ri : ZT n} (hi : Γ ⊢[PRAAx] zle ri (ZT.natLit 0))
    (h : Γ ⊢[PRAAx] zle r ri ⋎ zle r (ZT.natLit 0)) : Γ ⊢[PRAAx] zle r (ZT.natLit 0) := by
  refine .orE h ?_ ?_
  · have h' : (zle r ri :: Γ) ⊢[PRAAx] zle r ri := Prf.hyp0
    exact ztrans h' (hi.wk (ψ := zle r ri))
  · exact Prf.hyp0

/-- The residual at the label is nonnegative: every coordinate is dominated by the label (support) or is
nonpositive (off the support), and the residuals sum to a nonnegative number. -/
theorem label_nonneg (r : Fin (d + 1) → ZT n) (i : Fin (d + 1))
    (hsum : Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.sumFin r))
    (hsupp : ∀ j, Γ ⊢[PRAAx] zle (r j) (r i) ⋎ zle (r j) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0) (r i) := by
  refine .orE (le_total ((ZT.natLit 0 : ZT n).pos + (r i).neg) ((r i).pos + (ZT.natLit 0 : ZT n).neg)) ?_ ?_
  · exact Prf.hyp0
  · show (zle (r i) (ZT.natLit 0) :: Γ) ⊢[PRAAx] zle (ZT.natLit 0) (r i)
    have hi : (zle (r i) (ZT.natLit 0) :: Γ) ⊢[PRAAx] zle (r i) (ZT.natLit 0) := Prf.hyp0
    have h0 : ∀ j, (zle (r i) (ZT.natLit 0) :: Γ) ⊢[PRAAx] zle (r j) (ZT.natLit 0) := fun j =>
      nonpos_of hi ((hsupp j).wk (ψ := zle (r i) (ZT.natLit 0)))
    have hs := hsum.wk (ψ := zle (r i) (ZT.natLit 0))
    refine zle_of_comb (zsl hs + ∑ j ∈ Finset.univ.erase i, zsl (h0 j)) ?_
      (nn_add (nn_zsl _) (nn_sum _ _ fun j _ => nn_zsl _))
    simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero, Finset.sum_sub_distrib,
      Finset.sum_const_zero, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    ring

/-- "The chosen index is therefore a global maximizer." -/
theorem label_max (r : Fin (d + 1) → ZT n) (i : Fin (d + 1))
    (hsum : Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.sumFin r))
    (hsupp : ∀ j, Γ ⊢[PRAAx] zle (r j) (r i) ⋎ zle (r j) (ZT.natLit 0)) (j : Fin (d + 1)) :
    Γ ⊢[PRAAx] zle (r j) (r i) := by
  have hi := label_nonneg r i hsum hsupp
  refine .orE (hsupp j) ?_ ?_
  · exact Prf.hyp0
  · have h : (zle (r j) (ZT.natLit 0) :: Γ) ⊢[PRAAx] zle (r j) (ZT.natLit 0) := Prf.hyp0
    exact ztrans h (hi.wk (ψ := zle (r j) (ZT.natLit 0)))

/-! ## From a fully coloured cell to the residual bound -/

/-- The residual at a vertex `w` of the cell is within `E = h + ω` of the residual `R = x − y` at the
anchor: `|x − X(w)| ≤ h` and `|y − q(w)| ≤ ω`. -/
theorem transport {x y X q h ω : ZT n} (hx₁ : Γ ⊢[PRAAx] zle (-h) (x - X)) (hx₂ : Γ ⊢[PRAAx] zle (x - X) h)
    (hy₁ : Γ ⊢[PRAAx] zle (-ω) (y - q)) (hy₂ : Γ ⊢[PRAAx] zle (y - q) ω) :
    (Γ ⊢[PRAAx] zle (-(h + ω)) (x - y - (X - q))) ∧ (Γ ⊢[PRAAx] zle (x - y - (X - q)) (h + ω)) := by
  refine ⟨?_, ?_⟩
  · ipra_zle zsl hx₁ + zsl hy₂
  · ipra_zle zsl hx₂ + zsl hy₁

/-- "Comparing there and at the anchor gives `R_j − R_i ≤ 2E`": at the vertex `w_i` of colour `i` the
largest residual is the `i`th. -/
theorem pair_gap {Rj Ri rj ri E : ZT n} (hj : Γ ⊢[PRAAx] zle (Rj - rj) E) (hi : Γ ⊢[PRAAx] zle (-E) (Ri - ri))
    (hmax : Γ ⊢[PRAAx] zle rj ri) : Γ ⊢[PRAAx] zle (Rj - Ri) (ZT.natLit 2 * E) := by
  ipra_zle zsl hj + zsl hi + zsl hmax

/-- `2dE − (d+1) R_j = ∑_{i ≠ j} (2E − (R_j − R_i))` when `∑ R_i = 0`, in every commutative ring. -/
theorem avg_identity {A : Type*} [CommRing A] (R : Fin (d + 1) → A) (E : A) (j : Fin (d + 1))
    (hs : ∑ i, R i = 0) :
    ((2 * d : ℕ) : A) * E - ((d + 1 : ℕ) : A) * R j = ∑ i ∈ Finset.univ.erase j, (2 * E - (R j - R i)) := by
  have h1 : ∑ i ∈ Finset.univ.erase j, (2 * E - (R j - R i)) =
      ∑ _i ∈ Finset.univ.erase j, (2 * E - R j) + ∑ i ∈ Finset.univ.erase j, R i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, Finset.sum_const, Finset.sum_erase_eq_sub (Finset.mem_univ j), hs,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel,
    nsmul_eq_mul]
  push_cast
  ring

/-- `2dE + (d+1) R_j = ∑_{i ≠ j} (2E − (R_i − R_j))` when `∑ R_i = 0`. -/
theorem avg_identity_neg {A : Type*} [CommRing A] (R : Fin (d + 1) → A) (E : A) (j : Fin (d + 1))
    (hs : ∑ i, R i = 0) :
    ((d + 1 : ℕ) : A) * R j - -(((2 * d : ℕ) : A) * E) = ∑ i ∈ Finset.univ.erase j, (2 * E - (R i - R j)) := by
  have h1 : ∑ i ∈ Finset.univ.erase j, (2 * E - (R i - R j)) =
      ∑ _i ∈ Finset.univ.erase j, (2 * E + R j) - ∑ i ∈ Finset.univ.erase j, R i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, Finset.sum_const, Finset.sum_erase_eq_sub (Finset.mem_univ j), hs,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel,
    nsmul_eq_mul]
  push_cast
  ring

/-- `(d+1) R_j ≤ 2dE`: sum `R_j − R_i ≤ 2E` over the other `d` colours and use `∑ R_i = 0`. -/
theorem avg_upper (R : Fin (d + 1) → ZT n) (E : ZT n)
    (hsum : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin R) (ZT.natLit 0))
    (hpair : ∀ i j, Γ ⊢[PRAAx] zle (R j - R i) (ZT.natLit 2 * E)) (j : Fin (d + 1)) :
    Γ ⊢[PRAAx] zle (ZT.natLit (d + 1) * R j) (ZT.natLit (2 * d) * E) := by
  have hs := ZT.toZ_eq hsum
  simp only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] at hs
  refine zle_of_comb (∑ i ∈ Finset.univ.erase j, zsl (hpair i j)) ?_ (nn_sum _ _ fun i _ => nn_zsl _)
  simp only [zsl_def, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat]
  exact avg_identity (fun i => ZT.toZ Γ (R i)) (ZT.toZ Γ E) j hs

/-- `−2dE ≤ (d+1) R_j`. -/
theorem avg_lower (R : Fin (d + 1) → ZT n) (E : ZT n)
    (hsum : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin R) (ZT.natLit 0))
    (hpair : ∀ i j, Γ ⊢[PRAAx] zle (R j - R i) (ZT.natLit 2 * E)) (j : Fin (d + 1)) :
    Γ ⊢[PRAAx] zle (-(ZT.natLit (2 * d) * E)) (ZT.natLit (d + 1) * R j) := by
  have hs := ZT.toZ_eq hsum
  simp only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] at hs
  refine zle_of_comb (∑ i ∈ Finset.univ.erase j, zsl (hpair j i)) ?_ (nn_sum _ _ fun i _ => nn_zsl _)
  simp only [zsl_def, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit, Nat.cast_ofNat]
  exact avg_identity_neg (fun i => ZT.toZ Γ (R i)) (ZT.toZ Γ E) j hs

/-- Lemma `lem:finite` (finite table certificate) on a fully coloured cell: `X i`, `q i` are the grid point and
the sample at the vertex `w_i` of colour `i` (so its `i`th residual is the largest), `x` is the anchor and `y`
any point with the same total mass; `|x_j − X_j(w_i)| ≤ h` and `|y_j − q_j(w_i)| ≤ ω` give
`(d+1) |x_j − y_j| ≤ 2d (h + ω)`. -/
theorem finite_certificate (x y : Fin (d + 1) → ZT n) (X q : Fin (d + 1) → Fin (d + 1) → ZT n) (h ω : ZT n)
    (hmass : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => x j - y j) (ZT.natLit 0))
    (hmesh₁ : ∀ i j, Γ ⊢[PRAAx] zle (-h) (x j - X i j)) (hmesh₂ : ∀ i j, Γ ⊢[PRAAx] zle (x j - X i j) h)
    (hω₁ : ∀ i j, Γ ⊢[PRAAx] zle (-ω) (y j - q i j)) (hω₂ : ∀ i j, Γ ⊢[PRAAx] zle (y j - q i j) ω)
    (hlabel : ∀ i j, Γ ⊢[PRAAx] zle (X i j - q i j) (X i i - q i i)) (j : Fin (d + 1)) :
    (Γ ⊢[PRAAx] zle (-(ZT.natLit (2 * d) * (h + ω))) (ZT.natLit (d + 1) * (x j - y j))) ∧
      (Γ ⊢[PRAAx] zle (ZT.natLit (d + 1) * (x j - y j)) (ZT.natLit (2 * d) * (h + ω))) := by
  have hpair : ∀ i j, Γ ⊢[PRAAx] zle (x j - y j - (x i - y i)) (ZT.natLit 2 * (h + ω)) := fun i j =>
    pair_gap (transport (hmesh₁ i j) (hmesh₂ i j) (hω₁ i j) (hω₂ i j)).2
      (transport (hmesh₁ i i) (hmesh₂ i i) (hω₁ i i) (hω₂ i i)).1 (hlabel i j)
  exact ⟨avg_lower (fun j => x j - y j) (h + ω) hmass hpair j,
    avg_upper (fun j => x j - y j) (h + ω) hmass hpair j⟩

/-- `eq:main`, cleared by `J`: `(d+1) ρ ≤ 2d (h + ω)`, `N h ≤ J`, `2^m ω ≤ J` and `2^m ≤ N` with `m = k + 2`
give `(d+1) 2^k ρ ≤ d J`, that is `ρ/J ≤ (d/(d+1)) 2^{-k}`. -/
theorem main_bound (d k : ℕ) {ρ h ω J N : PTm n}
    (hres : Γ ⊢[PRAAx] le (num (d + 1) * ρ) (num (2 * d) * (h + ω))) (hh : Γ ⊢[PRAAx] le (N * h) J)
    (hω : Γ ⊢[PRAAx] le (num (2 ^ (k + 2)) * ω) J) (hN : Γ ⊢[PRAAx] le (num (2 ^ (k + 2))) N) :
    Γ ⊢[PRAAx] le (num ((d + 1) * 2 ^ k) * ρ) (num d * J) := by
  apply le_of_two_mul
  ipra_le (d : Groth (Q Γ)) * (sl hh + sl hN * 𝔟 h + sl hω) + 2 * 2 ^ k * sl hres using push_cast; ring

/-- Transfer along a `2^b`-Lipschitz retraction: residual `δ` becomes `2^b δ`. -/
theorem transfer_residual (b : ℕ) {dP dH δ : ZT n} (hL : Γ ⊢[PRAAx] zle dP (ZT.natLit (2 ^ b) * dH))
    (hδ : Γ ⊢[PRAAx] zle dH δ) : Γ ⊢[PRAAx] zle dP (ZT.natLit (2 ^ b) * δ) := by
  refine zle_of_comb (zsl hL + 2 ^ b * zsl hδ) ?_ (nn_add (nn_zsl _) (nn_mul (nn_pow (nn_ofNat 2) b) (nn_zsl _)))
  zsimp
  push_cast
  ring

/-! ## The direct cube certificate -/

/-- The two sign inequalities of the cubical labelling, transported to the initial vertex `u`:
`q_j(w) ≥ w_j` at the vertex of label `j` and `q_j(w') ≤ w'_j` at the vertex of label `d` give
`|y_j − u_j| ≤ h + ω`. -/
theorem cube_anchor {u y w q w' q' h ω : ZT n} (hq : Γ ⊢[PRAAx] zle w q) (hu : Γ ⊢[PRAAx] zle (u - w) h)
    (hy : Γ ⊢[PRAAx] zle (-ω) (y - q)) (hq' : Γ ⊢[PRAAx] zle q' w') (hu' : Γ ⊢[PRAAx] zle (-h) (u - w'))
    (hy' : Γ ⊢[PRAAx] zle (y - q') ω) :
    (Γ ⊢[PRAAx] zle (-(h + ω)) (y - u)) ∧ (Γ ⊢[PRAAx] zle (y - u) (h + ω)) := by
  refine ⟨?_, ?_⟩
  · ipra_zle zsl hy + zsl hq + zsl hu
  · ipra_zle zsl hy' + zsl hq' + zsl hu'

/-! ## The rational retraction onto the ball -/

section Ring

variable {A : Type*} [CommRing A] (z w : Fin d → A)

theorem expand (a b : A) :
    ∑ j, (a * z j - b * w j) ^ 2 =
      a ^ 2 * ∑ j, z j ^ 2 - 2 * a * b * ∑ j, z j * w j + b ^ 2 * ∑ j, w j ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem expand_right (b : A) :
    ∑ j, (z j - b * w j) ^ 2 = ∑ j, z j ^ 2 - 2 * b * ∑ j, z j * w j + b ^ 2 * ∑ j, w j ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem expand_one : ∑ j, (z j - w j) ^ 2 = ∑ j, z j ^ 2 - 2 * ∑ j, z j * w j + ∑ j, w j ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `‖t z − s w‖² = s t ‖z − w‖²` for `s = ‖z‖²`, `t = ‖w‖²`. -/
theorem outer_identity :
    ∑ j, ((∑ i, w i ^ 2) * z j - (∑ i, z i ^ 2) * w j) ^ 2 =
      (∑ i, z i ^ 2) * (∑ i, w i ^ 2) * ∑ j, (z j - w j) ^ 2 := by
  have h₁ := expand_one z w
  have h₂ := expand z w (∑ i, w i ^ 2) (∑ i, z i ^ 2)
  linear_combination h₂ - (∑ i, z i ^ 2) * (∑ i, w i ^ 2) * h₁

/-- `s² ‖z − w‖² − ‖z − s w‖² = s (s − 1) (‖z − w‖² + 1 − t)`. -/
theorem mixed_identity :
    (∑ i, z i ^ 2) ^ 2 * ∑ j, (z j - w j) ^ 2 - ∑ j, (z j - (∑ i, z i ^ 2) * w j) ^ 2 =
      (∑ i, z i ^ 2) * ((∑ i, z i ^ 2) - 1) * (∑ j, (z j - w j) ^ 2 + (1 - ∑ i, w i ^ 2)) := by
  have h₁ := expand_one z w
  have h₂ := expand_right z w (∑ i, z i ^ 2)
  linear_combination (∑ i, z i ^ 2) * h₁ - h₂

/-- `d M² − ∑ v_j² = ∑ (M − v_j)(v_j + M)`. -/
theorem sq_sum_identity (v : Fin d → A) (M : A) :
    (d : A) * (M * M) - ∑ j, v j ^ 2 = ∑ j, (M - v j) * (v j - -M) := by
  rw [Finset.sum_congr rfl fun j _ => show (M - v j) * (v j - -M) = M * M - v j ^ 2 by ring,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Ring

/-- Both points outside the ball: `‖t z − s w‖² = s t ‖z − w‖²`, so `‖R(z) − R(w)‖² = ‖z − w‖²/(st)`. -/
theorem ball_outer (z w : Fin d → ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.sumFin fun j => ZT.sq ((ZT.sumFin fun i => ZT.sq (w i)) * z j - (ZT.sumFin fun i => ZT.sq (z i)) * w j))
      ((ZT.sumFin fun i => ZT.sq (z i)) * (ZT.sumFin fun i => ZT.sq (w i)) *
        ZT.sumFin fun j => ZT.sq (z j - w j)) := by
  have e := outer_identity (fun j => ZT.toZ Γ (z j)) (fun j => ZT.toZ Γ (w j))
  beta_reduce at e
  apply ZT.derive
  zsimp
  linear_combination e

/-- One point outside (`s ≥ 1`), one inside (`t ≤ 1`): `‖z − s w‖² ≤ s² ‖z − w‖²`, so
`‖R(z) − w‖ ≤ ‖z − w‖`. -/
theorem ball_mixed (z w : Fin d → ZT n) (hs : Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin fun i => ZT.sq (z i)))
    (ht : Γ ⊢[PRAAx] zle (ZT.sumFin fun i => ZT.sq (w i)) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (ZT.sumFin fun j => ZT.sq (z j - (ZT.sumFin fun i => ZT.sq (z i)) * w j))
      ((ZT.sumFin fun i => ZT.sq (z i)) * (ZT.sumFin fun i => ZT.sq (z i)) *
        ZT.sumFin fun j => ZT.sq (z j - w j)) := by
  have e := mixed_identity (fun j => ZT.toZ Γ (z j)) (fun j => ZT.toZ Γ (w j))
  beta_reduce at e
  refine zle_of_comb ((zsl hs + 1) * zsl hs * ((∑ j, ZT.toZ Γ (z j - w j) ^ 2) + zsl ht)) ?_
    (nn_mul (nn_mul (nn_add (nn_zsl _) nn_one) (nn_zsl _))
      (nn_add (nn_sum _ _ fun j _ => nn_zsq _) (nn_zsl _)))
  zsimp
  linear_combination e

/-- `‖v‖_2² ≤ d ‖v‖²` for the maximum norm: `|v_j| ≤ M` gives `∑ v_j² ≤ d M²`. -/
theorem sq_sum_le (v : Fin d → ZT n) (M : ZT n) (h₁ : ∀ j, Γ ⊢[PRAAx] zle (-M) (v j))
    (h₂ : ∀ j, Γ ⊢[PRAAx] zle (v j) M) :
    Γ ⊢[PRAAx] zle (ZT.sumFin fun j => ZT.sq (v j)) (ZT.natLit d * (M * M)) := by
  refine zle_of_comb (∑ j, zsl (h₂ j) * zsl (h₁ j)) ?_ (nn_sum _ _ fun j _ => nn_mul (nn_zsl _) (nn_zsl _))
  zsimp
  exact sq_sum_identity (fun j => ZT.toZ Γ (v j)) (ZT.toZ Γ M)

end LeanProofs.IPRA.Topology.ApproximateBrouwer
