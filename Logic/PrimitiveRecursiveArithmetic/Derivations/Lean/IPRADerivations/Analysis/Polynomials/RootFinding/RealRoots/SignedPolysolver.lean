import IPRADerivations.Core.IntCertificates
import IPRADerivations.Algebra.AdjugateInverse

/-!
# The signed certified polynomial solver

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/04_polynomial.tex`, Theorem
`thm:polysolver` ("Certified polynomial solver"), for signed data: integer terms (`ZT`, rationals cleared of a
common denominator) in a fixed dimension `d`, absolute values as two-sided bounds, derived in iPRA with the
certificates of `Core/IntCertificates`. (The natural-term feedback theory is `Analysis/WeightedFeedback`.)

* `zle_sumFin`, `row_bound`: sums of derived inequalities, and the signed row bound
  `|∑_j c_j x_j| ≤ ∑_j A_j δ_j` from `|c_j| ≤ A_j`, `|x_j| ≤ δ_j` ("Rowwise triangle inequalities");
* `contract`, `contract_low`: the half-contraction from the gain bound `eq:polylip` and the certificate
  `eq:polycert`: `|D| ≤ ∑_j W_j δ_j`, `δ_j ≤ ρ v_j` and `2 ∑_j W_j v_j ≤ v_i` give `2|D| ≤ ρ v_i`
  ("`‖T(h) − T(k)‖_v ≤ ½ ‖h − k‖_v`");
* `ball_step`, `orbit_ball` (`eq:polyball`): "`‖T(h)‖_v ≤ ‖T(0)‖_v + ½‖h‖_v ≤ r/2 + r/2 = r`. This proves the
  invariant ball by induction": `|(h_n)_i| ≤ r v_i` for the orbit `h_0 = 0`, `h_{n+1} = T(h_n)`;
* `left_inverse`: "From the defining equation, `B F(x_0 + h_n) = h_n − h_{n+1}`. Multiplication by the checked
  left inverse `C` yields `F(x_0 + h_n) = C(h_n − h_{n+1})`", as an iPRA vector equation from `C B = I`;
* `residual_bound` (`eq:polyresidual`): `|F_i| ≤ ∑_j A_{ij} δ_j` for entry bounds `|C_{ij}| ≤ A_{ij}` and step
  bounds `|(h_n − h_{n+1})_j| ≤ δ_j`;
* `poly_step` (`eq:polystep`), `poly_tail`, `poly_tail_ball` (`eq:polytail`): the halving of the successive
  differences and the finite geometric tail, for weighted norms given as natural terms.
-/

namespace LeanProofs.IPRA.Analysis.SignedPolysolver

open_ipra
open LeanProofs.IPRA.Algebra.AdjugateInverse (conjFin_elim toZ_of_eqFm)

variable {n d : ℕ} {Γ : List (Fm PTm n)}

/-- A sum of derived inequalities. -/
theorem zle_sumFin {u v : Fin d → ZT n} (h : ∀ j, Γ ⊢[PRAAx] zle (u j) (v j)) :
    Γ ⊢[PRAAx] zle (ZT.sumFin u) (ZT.sumFin v) := by
  refine zle_of_comb (∑ j, zsl (h j)) ?_ (nn_sum _ _ fun j _ => nn_zsl _)
  simp only [zsl_def, ZT.toZ_sumFin]
  rw [Finset.sum_sub_distrib]

/-- The signed row bound: `|c_j| ≤ A_j` and `|x_j| ≤ δ_j` give `|∑ c_j x_j| ≤ ∑ A_j δ_j`. -/
theorem row_bound {c A x δ : Fin d → ZT n} (hc₁ : ∀ j, Γ ⊢[PRAAx] zle (-(A j)) (c j))
    (hc₂ : ∀ j, Γ ⊢[PRAAx] zle (c j) (A j)) (hx₁ : ∀ j, Γ ⊢[PRAAx] zle (-(δ j)) (x j))
    (hx₂ : ∀ j, Γ ⊢[PRAAx] zle (x j) (δ j)) :
    (Γ ⊢[PRAAx] zle (-(ZT.sumFin fun j => A j * δ j)) (ZT.sumFin fun j => c j * x j)) ∧
      (Γ ⊢[PRAAx] zle (ZT.sumFin fun j => c j * x j) (ZT.sumFin fun j => A j * δ j)) := by
  refine ⟨?_, zle_sumFin fun j => (zabs_mul (hc₁ j) (hc₂ j) (hx₁ j) (hx₂ j)).2⟩
  refine zle_of_comb (∑ j, zsl (zabs_mul (hc₁ j) (hc₂ j) (hx₁ j) (hx₂ j)).1) ?_
    (nn_sum _ _ fun j _ => nn_zsl _)
  simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_neg, ZT.toZ_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

section Contract

variable {W v δ : Fin d → ZT n} {D ρ vi : ZT n}

theorem sum_split :
    ∑ j, ZT.toZ Γ (W j) * (ZT.toZ Γ ρ * ZT.toZ Γ (v j) - ZT.toZ Γ (δ j)) =
      ZT.toZ Γ ρ * ∑ j, ZT.toZ Γ (W j) * ZT.toZ Γ (v j) - ∑ j, ZT.toZ Γ (W j) * ZT.toZ Γ (δ j) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The half-contraction, upper side: `D ≤ ∑ W_j δ_j`, `δ_j ≤ ρ v_j`, `2 ∑ W_j v_j ≤ v_i` give
`2 D ≤ ρ v_i`. -/
theorem contract (hD : Γ ⊢[PRAAx] zle D (ZT.sumFin fun j => W j * δ j))
    (hW : ∀ j, Γ ⊢[PRAAx] zle (ZT.natLit 0) (W j)) (hδ : ∀ j, Γ ⊢[PRAAx] zle (δ j) (ρ * v j))
    (hρ : Γ ⊢[PRAAx] zle (ZT.natLit 0) ρ)
    (hcert : Γ ⊢[PRAAx] zle (ZT.natLit 2 * ZT.sumFin fun j => W j * v j) vi) :
    Γ ⊢[PRAAx] zle (ZT.natLit 2 * D) (ρ * vi) := by
  have e := sum_split (Γ := Γ) (W := W) (v := v) (δ := δ) (ρ := ρ)
  refine zle_of_comb (2 * zsl hD + 2 * ∑ j, ZT.toZ Γ (W j) * zsl (hδ j) + ZT.toZ Γ ρ * zsl hcert) ?_
    (nn_add (nn_add (nn_mul (nn_ofNat 2) (nn_zsl _))
      (nn_mul (nn_ofNat 2) (nn_sum _ _ fun j _ => nn_mul (nn_zle0 (hW j)) (nn_zsl _))))
      (nn_mul (nn_zle0 hρ) (nn_zsl _)))
  zsimp
  linear_combination (-2) * e

/-- The half-contraction, lower side: `−∑ W_j δ_j ≤ D` gives `−ρ v_i ≤ 2 D`. -/
theorem contract_low (hD : Γ ⊢[PRAAx] zle (-(ZT.sumFin fun j => W j * δ j)) D)
    (hW : ∀ j, Γ ⊢[PRAAx] zle (ZT.natLit 0) (W j)) (hδ : ∀ j, Γ ⊢[PRAAx] zle (δ j) (ρ * v j))
    (hρ : Γ ⊢[PRAAx] zle (ZT.natLit 0) ρ)
    (hcert : Γ ⊢[PRAAx] zle (ZT.natLit 2 * ZT.sumFin fun j => W j * v j) vi) :
    Γ ⊢[PRAAx] zle (-(ρ * vi)) (ZT.natLit 2 * D) := by
  have e := sum_split (Γ := Γ) (W := W) (v := v) (δ := δ) (ρ := ρ)
  refine zle_of_comb (2 * zsl hD + 2 * ∑ j, ZT.toZ Γ (W j) * zsl (hδ j) + ZT.toZ Γ ρ * zsl hcert) ?_
    (nn_add (nn_add (nn_mul (nn_ofNat 2) (nn_zsl _))
      (nn_mul (nn_ofNat 2) (nn_sum _ _ fun j _ => nn_mul (nn_zle0 (hW j)) (nn_zsl _))))
      (nn_mul (nn_zle0 hρ) (nn_zsl _)))
  zsimp
  linear_combination (-2) * e

end Contract

/-- One step of the invariant ball: `2|T(0)| ≤ R` and `2|T(h) − T(0)| ≤ R` give `|T(h)| ≤ R`. -/
theorem ball_step {t0 th R : ZT n} (h0₁ : Γ ⊢[PRAAx] zle (-R) (ZT.natLit 2 * t0))
    (h0₂ : Γ ⊢[PRAAx] zle (ZT.natLit 2 * t0) R) (hc₁ : Γ ⊢[PRAAx] zle (-R) (ZT.natLit 2 * (th - t0)))
    (hc₂ : Γ ⊢[PRAAx] zle (ZT.natLit 2 * (th - t0)) R) :
    (Γ ⊢[PRAAx] zle (-R) th) ∧ (Γ ⊢[PRAAx] zle th R) := by
  refine ⟨zle_of_comb_two (zsl h0₁ + zsl hc₁) ?_ (by znn), zle_of_comb_two (zsl h0₂ + zsl hc₂) ?_ (by znn)⟩
  · zsimp; ring
  · zsimp; ring

/-- The orbit `h_0 = 0`, `h_{k+1} = T(h_k)`. -/
def orbit (T : (Fin d → ZT n) → Fin d → ZT n) : ℕ → Fin d → ZT n
  | 0 => fun _ => ZT.natLit 0
  | k + 1 => T (orbit T k)

/-- `eq:polyball`: the orbit stays in the weighted ball `|h_i| ≤ r v_i`. -/
theorem orbit_ball (T : (Fin d → ZT n) → Fin d → ZT n) (r : ZT n) (v : Fin d → ZT n)
    (hzero : ∀ i, (Γ ⊢[PRAAx] zle (-(r * v i)) (ZT.natLit 0)) ∧ (Γ ⊢[PRAAx] zle (ZT.natLit 0) (r * v i)))
    (h0 : ∀ i, (Γ ⊢[PRAAx] zle (-(r * v i)) (ZT.natLit 2 * T (fun _ => ZT.natLit 0) i)) ∧
      (Γ ⊢[PRAAx] zle (ZT.natLit 2 * T (fun _ => ZT.natLit 0) i) (r * v i)))
    (hstep : ∀ h : Fin d → ZT n,
      (∀ j, (Γ ⊢[PRAAx] zle (-(r * v j)) (h j)) ∧ (Γ ⊢[PRAAx] zle (h j) (r * v j))) →
      ∀ i, (Γ ⊢[PRAAx] zle (-(r * v i)) (ZT.natLit 2 * (T h i - T (fun _ => ZT.natLit 0) i))) ∧
        (Γ ⊢[PRAAx] zle (ZT.natLit 2 * (T h i - T (fun _ => ZT.natLit 0) i)) (r * v i))) :
    ∀ k i, (Γ ⊢[PRAAx] zle (-(r * v i)) (orbit T k i)) ∧ (Γ ⊢[PRAAx] zle (orbit T k i) (r * v i))
  | 0, i => hzero i
  | k + 1, i =>
    ball_step (h0 i).1 (h0 i).2 (hstep _ (orbit_ball T r v hzero h0 hstep k) i).1
      (hstep _ (orbit_ball T r v hzero h0 hstep k) i).2

/-- `C B = I` and `B f = h − h'` give `f = C (h − h')`. -/
theorem left_inverse (C B : Mat d n) (f h h' : Vec d n) (hCB : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul C B) Mat.one)
    (hB : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec B f) (Vec.sub h h')) :
    Γ ⊢[PRAAx] Vec.eqFm f (Mat.mulVec C (Vec.sub h h')) := by
  apply Vec.derive
  have e₁ := toZ_of_eqFm hCB
  rw [Mat.toZ_mul, Mat.toZ_one] at e₁
  have e₂ : Vec.toZ Γ (Mat.mulVec B f) = Vec.toZ Γ (Vec.sub h h') :=
    funext fun i => ZT.toZ_eq (conjFin_elim hB i)
  rw [Mat.toZ_mulVec] at e₂
  rw [Mat.toZ_mulVec, ← e₂, Matrix.mulVec_mulVec, e₁, Matrix.one_mulVec]

/-- `eq:polyresidual`: `|F_i| ≤ ∑_j A_{ij} δ_j`. -/
theorem residual_bound (C B A : Mat d n) (f h h' : Vec d n) (δ : Fin d → ZT n)
    (hCB : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul C B) Mat.one)
    (hB : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec B f) (Vec.sub h h'))
    (hC₁ : ∀ i j, Γ ⊢[PRAAx] zle (-(A i j)) (C i j)) (hC₂ : ∀ i j, Γ ⊢[PRAAx] zle (C i j) (A i j))
    (hδ₁ : ∀ j, Γ ⊢[PRAAx] zle (-(δ j)) (h j - h' j)) (hδ₂ : ∀ j, Γ ⊢[PRAAx] zle (h j - h' j) (δ j))
    (i : Fin d) :
    (Γ ⊢[PRAAx] zle (-(ZT.sumFin fun j => A i j * δ j)) (f i)) ∧
      (Γ ⊢[PRAAx] zle (f i) (ZT.sumFin fun j => A i j * δ j)) := by
  have e : ZT.toZ Γ (f i) = ZT.toZ Γ (ZT.sumFin fun j => C i j * (h j - h' j)) :=
    ZT.toZ_eq (conjFin_elim (left_inverse C B f h h' hCB hB) i)
  have rb := row_bound (hC₁ i) (hC₂ i) hδ₁ hδ₂
  exact ⟨zle_of_comb (zsl rb.1) (by rw [zsl_def, e]) (nn_zsl _),
    zle_of_comb (zsl rb.2) (by rw [zsl_def, e]) (nn_zsl _)⟩

/-! ## The step and tail estimates (weighted norms as natural terms) -/

/-- `eq:polystep`: "The first successive difference has norm `c_0`. Each subsequent difference is at most
half the preceding one": `s_0 ≤ c_0` and `2 s_{k+1} ≤ s_k` give `2^k s_k ≤ c_0`. -/
theorem poly_step (s : ℕ → PTm n) (c₀ : PTm n) (h0 : Γ ⊢[PRAAx] le (s 0) c₀)
    (hstep : ∀ k, Γ ⊢[PRAAx] le (PTm.num 2 * s (k + 1)) (s k)) (k : ℕ) :
    Γ ⊢[PRAAx] le (PTm.num (2 ^ k) * s k) c₀ := by
  induction k with
  | zero => ipra_le sl h0 using push_cast; ring
  | succ k ih =>
    have hk := hstep k
    ipra_le 2 ^ k * sl hk + sl ih using push_cast; ring

/-- `eq:polytail`: "Sum the `m` consecutive differences beginning at `n`. The finite geometric identity gives
`‖h_{n+m} − h_n‖_v ≤ 2 c_0 2^{-n} (1 − 2^{-m})`; after multiplying by `2^{n+m}`, this is an ordinary rational
inequality": with `D_m` the distance from `h_j` to `h_{j+m}`, `2^{j+m} D_m + 2 c_0 ≤ 2^{m+1} c_0`. -/
theorem poly_tail (s D : ℕ → PTm n) (c₀ : PTm n) (j : ℕ)
    (hs : ∀ k, Γ ⊢[PRAAx] le (PTm.num (2 ^ k) * s k) c₀) (hD0 : Γ ⊢[PRAAx] le (D 0) ConciseIPRA.PTm.zero)
    (htri : ∀ m, Γ ⊢[PRAAx] le (D (m + 1)) (D m + s (j + m))) (m : ℕ) :
    Γ ⊢[PRAAx] le (PTm.num (2 ^ (j + m)) * D m + PTm.num 2 * c₀) (PTm.num (2 ^ (m + 1)) * c₀) := by
  induction m with
  | zero => ipra_le 2 ^ j * sl hD0 using push_cast; ring
  | succ m ih =>
    have ht := htri m
    have hsm := hs (j + m)
    ipra_le 2 ^ (j + m + 1) * sl ht + 2 * sl ih + 2 * sl hsm using push_cast; ring

/-- The tail stays in the ball scale: `2 c_0 ≤ r` gives `2^{j+m} D_m ≤ 2^m r`, that is `D_m ≤ r 2^{-j}`. -/
theorem poly_tail_ball {Dm c₀ r : PTm n} (j m : ℕ)
    (ht : Γ ⊢[PRAAx] le (PTm.num (2 ^ (j + m)) * Dm + PTm.num 2 * c₀) (PTm.num (2 ^ (m + 1)) * c₀))
    (hr : Γ ⊢[PRAAx] le (PTm.num 2 * c₀) r) : Γ ⊢[PRAAx] le (PTm.num (2 ^ (j + m)) * Dm) (PTm.num (2 ^ m) * r) := by
  ipra_le sl ht + 2 ^ m * sl hr + 2 * Groth.ι (Q.mk Γ c₀) using push_cast; ring

end LeanProofs.IPRA.Analysis.SignedPolysolver
