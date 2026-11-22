import IPRADerivations.Core.IntCertificates

/-!
# The finite estimates of the even-sphere obstruction and the approximate hairy-ball theorem

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/07_spheres.tex`. All statements are iPRA
derivations about integer terms (`ZT`, the rational data cleared of a common denominator), proved with the
certificates of `Core/IntCertificates`:

* S04 (`thm:antipodal-finite`), the chain argument after the carrier lemma (`antipodal_finite`): if the
  push-forward of the prism boundary `c_top − c_bottom` is the target boundary of the pushed-forward prism
  chain, which vanishes ("Every `(n+1)`-simplex maps degenerately to the `n`-dimensional target"), while
  `c_top ↦ −z_n` and `c_bottom ↦ z_n` with positive facet coefficient `1`, then "`−1 = 1` in `ℤ`" and every
  formula is derivable;
* S05 (`thm:no-antipodal-homotopy`), the labels: "Since `‖H‖_1 = 1`, the selected magnitude is at least
  `1/d`" (`max_coord`: `Σ aᵢ = N` and `aᵢ ≤ a_j` give `N ≤ d a_j`), and vertices whose images differ by less
  than `1/(2d)` "cannot receive opposite labels" (`no_opposite_labels`);
* S06 (`thm:approx-hairy`): the scan lower bound `‖F(x)‖ ≥ ‖F(v)‖ − L‖x − v‖ > 3ε/4` (`scan_lower`); the
  tangency identity `‖w‖_2^2 = a^2‖x‖_2^2 + b^2‖F‖_2^2` (`tangent_norm`, for every commutative ring, and
  `tangent_norm_ipra`); the end-time case `|a(t)| ≥ 1/2` of the lower bound on `‖w‖`, by the finite Cauchy
  inequality (`end_case`: `‖w‖_2^2 ≥ 1/(4d)`); the middle-time case (`middle_time`: `|a(t)| < 1/2` gives
  `b(t) > 3/16`; `middle_case`: `‖w‖_2^2 ≥ (3δ/16)^2`); the Lipschitz bound
  `|w_i(x,t) − w_i(y,s)| ≤ (1 + L/4)‖x − y‖ + (2 + M)|t − s|` (`w_lipschitz`); and the normalization bound
  `|u_i/‖u‖_1 − v_i/‖v‖_1| ≤ ((d+1)/λ)‖u − v‖_∞` (`normalize_lipschitz`).

The scalings: points `x = X/N`, field values `F(x) = G/N`, times `t = T/K` with `0 ≤ T ≤ K`.
-/

namespace LeanProofs.IPRA.Topology.SphereEstimates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## S04 -/

/-- S04: the prism identity pushed forward, a vanishing degree-`(n+1)` image, bottom `z_n`, top `−z_n` and a
facet coefficient `1` are contradictory. -/
theorem antipodal_finite {N₀ N₁ : ℕ} (D : Fin N₀ → Fin N₁ → ZT n) (Tp Bt Z : Fin N₀ → ZT n) (F : Fin N₁ → ZT n)
    (hcomm : ∀ b, Γ ⊢[PRAAx] ZT.eq (Tp b - Bt b) (ZT.sumFin fun k => D b k * F k))
    (hdeg : ∀ k, Γ ⊢[PRAAx] ZT.eq (F k) (ZT.natLit 0))
    (htop : ∀ b, Γ ⊢[PRAAx] ZT.eq (Tp b) (-Z b)) (hbot : ∀ b, Γ ⊢[PRAAx] ZT.eq (Bt b) (Z b))
    (p : Fin N₀) (hp : Γ ⊢[PRAAx] ZT.eq (Z p) (ZT.natLit 1)) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  have hF : ∀ k, ZT.toZ Γ (F k) = 0 := fun k => by
    have := ZT.toZ_eq (hdeg k)
    simpa using this
  have e := ZT.toZ_eq (hcomm p)
  simp only [ZT.toZ_sub, ZT.toZ_sumFin, ZT.toZ_mul, hF, MulZeroClass.mul_zero, Finset.sum_const_zero] at e
  have et := ZT.toZ_eq (htop p)
  have eb := ZT.toZ_eq (hbot p)
  have ep := ZT.toZ_eq (hp)
  simp only [ZT.toZ_neg, ZT.toZ_natLit, Nat.cast_one] at et ep
  exact false_of_comb 1 (by linear_combination -e + et - eb - 2 * ep) nn_one φ

/-! ## S05 -/

/-- "The selected magnitude is at least `1/d`": `Σ aᵢ = N` and `aᵢ ≤ a_j` give `N ≤ d · a_j`. -/
theorem max_coord {d : ℕ} (a : Fin d → PTm n) {N : PTm n}
    (hsum : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => ZT.ofNat (a i)) (ZT.ofNat N)) {j : Fin d}
    (hj : ∀ i, Γ ⊢[PRAAx] le (a i) (a j)) : Γ ⊢[PRAAx] le N (PTm.num d * a j) := by
  have e := ZT.toZ_eq hsum
  simp only [ZT.toZ_sumFin, ZT.toZ_ofNat] at e
  refine le_of_comb (∑ i, sl (hj i)) ?_ (nn_sum _ _ fun i _ => nn_sl _)
  rw [← e]
  simp only [sl_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ipra_simps

/-- Opposite labels are impossible: `0 ≤ e`, `e ≤ a`, `b ≤ −e` and `2(a − b) < e` contradict (here `e`
is `1/d` and `a`, `b` are the chosen coordinate at two vertices of one simplex). -/
theorem no_opposite_labels {e a b : ZT n} (he : Γ ⊢[PRAAx] zle (ZT.natLit 0) e) (ha : Γ ⊢[PRAAx] zle e a)
    (hb : Γ ⊢[PRAAx] zle b (-e)) (hc : Γ ⊢[PRAAx] zle (ZT.natLit 2 * (a - b) + ZT.natLit 1) e)
    (φ : Fm PTm n) : Γ ⊢[PRAAx] φ :=
  false_of_comb (zsl hc + 2 * zsl ha + 2 * zsl hb + 3 * zsl he) (by zsimp; ring) (by znn) φ

/-! ## S06 -/

/-- `ε < F(v)`, `F(v) − F(x) ≤ L‖x − v‖` and `4 L‖x − v‖ ≤ ε` give `3ε < 4 F(x)`. -/
theorem scan_lower {ε Fv Fx Ld : ZT n} (hv : Γ ⊢[PRAAx] zle (ε + ZT.natLit 1) Fv)
    (hlip : Γ ⊢[PRAAx] zle (Fv - Fx) Ld) (hmesh : Γ ⊢[PRAAx] zle (ZT.natLit 4 * Ld) ε) :
    Γ ⊢[PRAAx] zle (ZT.natLit 3 * ε + ZT.natLit 1) (ZT.natLit 4 * Fx) := by
  ipra_zle 4 * zsl hv + 4 * zsl hlip + zsl hmesh + 3

/-- Tangency gives `‖a x + b F‖_2^2 = a^2 ‖x‖_2^2 + b^2 ‖F‖_2^2`, in every commutative ring. -/
theorem tangent_norm {R : Type*} [CommRing R] {d : ℕ} (x F : Fin d → R) (htan : ∑ i, x i * F i = 0) (a b : R) :
    ∑ i, (a * x i + b * F i) ^ 2 = a ^ 2 * ∑ i, x i ^ 2 + b ^ 2 * ∑ i, F i ^ 2 := by
  have e : ∀ i, (a * x i + b * F i) ^ 2 = a ^ 2 * x i ^ 2 + b ^ 2 * F i ^ 2 + 2 * a * b * (x i * F i) :=
    fun i => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, htan, MulZeroClass.mul_zero, _root_.add_zero]

variable {d : ℕ}

theorem tangent_toZ (X G : Fin d → ZT n) (htan : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => X i * G i) (ZT.natLit 0))
    (A B : ZT n) :
    ∑ i, (ZT.toZ Γ A * ZT.toZ Γ (X i) + ZT.toZ Γ B * ZT.toZ Γ (G i)) ^ 2 =
      ZT.toZ Γ A ^ 2 * ∑ i, ZT.toZ Γ (X i) ^ 2 + ZT.toZ Γ B ^ 2 * ∑ i, ZT.toZ Γ (G i) ^ 2 := by
  have e := ZT.toZ_eq htan
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] at e
  exact tangent_norm (fun i => ZT.toZ Γ (X i)) (fun i => ZT.toZ Γ (G i)) e _ _

/-- The tangency identity as an iPRA equation. -/
theorem tangent_norm_ipra (X G : Fin d → ZT n)
    (htan : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => X i * G i) (ZT.natLit 0)) (A B : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => ZT.sq (A * X i + B * G i))
      (ZT.sq A * ZT.sumFin (fun i => ZT.sq (X i)) + ZT.sq B * ZT.sumFin (fun i => ZT.sq (G i))) := by
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_sq, ZT.toZ_add, ZT.toZ_mul]
  exact tangent_toZ X G htan A B

/-- `toZ(u)^2 = |u|^2`. -/
theorem sq_abs_toZ (u : ZT n) : ZT.toZ Γ u ^ 2 = Groth.ι (Q.mk Γ (ad u.pos u.neg)) ^ 2 := by
  rw [← ZT.toZ_sq, sq_nat, Q.mk_mul, map_mul, sq]

/-- The end-time case: `Σ |Xᵢ| = N`, tangency and `M² ≤ 4A²` (that is, `|a(t)| ≥ 1/2` for `a = A/M`) give
`M² N² ≤ 4 d ‖A X + B G‖_2^2`, that is, `‖w‖_2^2 ≥ 1/(4d)`. -/
theorem end_case (X G : Fin d → ZT n) {A B : ZT n} {M N : PTm n}
    (hx : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => ZT.ofNat (ad (X i).pos (X i).neg)) (ZT.ofNat N))
    (htan : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => X i * G i) (ZT.natLit 0))
    (ha : Γ ⊢[PRAAx] zle (ZT.ofNat (M * M)) (ZT.natLit 4 * ZT.sq A)) :
    Γ ⊢[PRAAx] zle (ZT.ofNat (M * M * (N * N)))
      (ZT.natLit 4 * ZT.natLit d * ZT.sumFin fun i => ZT.sq (A * X i + B * G i)) := by
  have hC := cauchy_int (Γ := Γ) fun i => ZT.ofNat (ad (X i).pos (X i).neg)
  have hN := ZT.toZ_eq hx
  simp only [ZT.toZ_sumFin, ZT.toZ_ofNat] at hN
  have hS : ∑ i, Groth.ι (Q.mk Γ (ad (X i).pos (X i).neg)) ^ 2 = ∑ i, ZT.toZ Γ (X i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => (sq_abs_toZ (X i)).symm
  have ht := tangent_toZ X G htan A B
  have hSX : Nonneg Γ (∑ i, ZT.toZ Γ (X i) ^ 2) := nn_sum _ _ fun i _ => nn_zsq _
  have hSG : Nonneg Γ (∑ i, ZT.toZ Γ (G i) ^ 2) := nn_sum _ _ fun i _ => nn_zsq _
  refine zle_of_comb (4 * (d : Groth (Q Γ)) * ZT.toZ Γ B ^ 2 * ∑ i, ZT.toZ Γ (G i) ^ 2 +
      zsl ha * ((d : Groth (Q Γ)) * ∑ i, ZT.toZ Γ (X i) ^ 2) + Groth.ι (Q.mk Γ M) ^ 2 * zsl hC) ?_ (by znn)
  zsimp
  simp only [Q.mk_mul, map_mul]
  linear_combination (4 * (d : Groth (Q Γ))) * ht - (Groth.ι (Q.mk Γ M) ^ 2 * (d : Groth (Q Γ))) * hS +
    (Groth.ι (Q.mk Γ M) ^ 2 * (∑ i, Groth.ι (Q.mk Γ (ad (X i).pos (X i).neg)) + Groth.ι (Q.mk Γ N))) * hN

/-- The middle times: `2|K − 2T| < K` (that is, `|a(t)| < 1/2` for `t = T/K`) gives
`3K² < 16 T(K − T)`, that is, `b(t) > 3/16`. -/
theorem middle_time {T K : ZT n}
    (h₁ : Γ ⊢[PRAAx] zle (ZT.natLit 2 * (K - ZT.natLit 2 * T) + ZT.natLit 1) K)
    (h₂ : Γ ⊢[PRAAx] zle (ZT.natLit 2 * (ZT.natLit 2 * T - K) + ZT.natLit 1) K) :
    Γ ⊢[PRAAx] zle (ZT.natLit 3 * ZT.sq K + ZT.natLit 1) (ZT.natLit 16 * (T * (K - T))) := by
  ipra_zle zsl h₁ * zsl h₂ + zsl h₁ + zsl h₂

/-- The middle-time case: with `16 B > 3K²` (`B = T(K − T)`, `middle_time`), tangency and `Δ ≤ |G_j|`,
`9 K⁴ Δ² ≤ 256 ‖A X + B G‖_2^2`, that is, `‖w‖_2^2 ≥ (3δ/16)^2`. -/
theorem middle_case (X G : Fin d → ZT n) {A B K : ZT n} {Δ : PTm n}
    (htan : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => X i * G i) (ZT.natLit 0))
    (hm : Γ ⊢[PRAAx] zle (ZT.natLit 3 * ZT.sq K + ZT.natLit 1) (ZT.natLit 16 * B)) {j : Fin d}
    (hj : Γ ⊢[PRAAx] le Δ (ad (G j).pos (G j).neg)) :
    Γ ⊢[PRAAx] zle (ZT.natLit 9 * ZT.sq (ZT.sq K) * ZT.sq (ZT.ofNat Δ))
      (ZT.natLit 256 * ZT.sumFin fun i => ZT.sq (A * X i + B * G i)) := by
  have ht := tangent_toZ X G htan A B
  have hsplit : ZT.toZ Γ (G j) ^ 2 + ∑ i ∈ Finset.univ.erase j, ZT.toZ Γ (G i) ^ 2 = ∑ i, ZT.toZ Γ (G i) ^ 2 :=
    Finset.add_sum_erase Finset.univ (fun i => ZT.toZ Γ (G i) ^ 2) (Finset.mem_univ j)
  have hGj := sq_abs_toZ (Γ := Γ) (G j)
  have hSX : Nonneg Γ (∑ i, ZT.toZ Γ (X i) ^ 2) := nn_sum _ _ fun i _ => nn_zsq _
  have hR : Nonneg Γ (∑ i ∈ Finset.univ.erase j, ZT.toZ Γ (G i) ^ 2) := nn_sum _ _ fun i _ => nn_zsq _
  refine zle_of_comb (256 * ZT.toZ Γ A ^ 2 * ∑ i, ZT.toZ Γ (X i) ^ 2 +
      256 * ZT.toZ Γ B ^ 2 * ∑ i ∈ Finset.univ.erase j, ZT.toZ Γ (G i) ^ 2 +
      256 * ZT.toZ Γ B ^ 2 * (sl hj * (Groth.ι (Q.mk Γ (ad (G j).pos (G j).neg)) + Groth.ι (Q.mk Γ Δ))) +
      (zsl hm + 1) * (zsl hm + 1 + 6 * ZT.toZ Γ K ^ 2) * Groth.ι (Q.mk Γ Δ) ^ 2) ?_ (by znn)
  zsimp
  linear_combination 256 * ht - 256 * ZT.toZ Γ B ^ 2 * hsplit + 256 * ZT.toZ Γ B ^ 2 * hGj

/-- `w(x, t) = (1 − 2t) x + t(1 − t) F(x)` is Lipschitz: cleared by `K² N` (`t = T/K`, `s = S/K`,
`x = X/N`, `F(x) = G/N`), with `|X − Y| ≤ D`, `|G − H| ≤ L D`, `|H| ≤ M N`, `|Y| ≤ N` and `|T − S| ≤ E`,
`4 |W(x, t) − W(y, s)| ≤ (4 + L) K² D + 4 (2 + M) K N E`. -/
theorem w_lipschitz {K T S X Y G H D L M N E : ZT n}
    (hT₀ : Γ ⊢[PRAAx] zle (ZT.natLit 0) T) (hT₁ : Γ ⊢[PRAAx] zle T K)
    (hS₀ : Γ ⊢[PRAAx] zle (ZT.natLit 0) S) (hS₁ : Γ ⊢[PRAAx] zle S K)
    (hY₁ : Γ ⊢[PRAAx] zle (-N) Y) (hY₂ : Γ ⊢[PRAAx] zle Y N)
    (hH₁ : Γ ⊢[PRAAx] zle (-(M * N)) H) (hH₂ : Γ ⊢[PRAAx] zle H (M * N))
    (hXY₁ : Γ ⊢[PRAAx] zle (-D) (X - Y)) (hXY₂ : Γ ⊢[PRAAx] zle (X - Y) D)
    (hGH₁ : Γ ⊢[PRAAx] zle (-(L * D)) (G - H)) (hGH₂ : Γ ⊢[PRAAx] zle (G - H) (L * D))
    (hE₁ : Γ ⊢[PRAAx] zle (-E) (T - S)) (hE₂ : Γ ⊢[PRAAx] zle (T - S) E) :
    (Γ ⊢[PRAAx] zle (-((ZT.natLit 4 + L) * (K * K) * D + ZT.natLit 4 * (ZT.natLit 2 + M) * (K * N) * E))
      (ZT.natLit 4 * ((K * (K - ZT.natLit 2 * T) * X + T * (K - T) * G) -
        (K * (K - ZT.natLit 2 * S) * Y + S * (K - S) * H)))) ∧
    (Γ ⊢[PRAAx] zle (ZT.natLit 4 * ((K * (K - ZT.natLit 2 * T) * X + T * (K - T) * G) -
        (K * (K - ZT.natLit 2 * S) * Y + S * (K - S) * H)))
      ((ZT.natLit 4 + L) * (K * K) * D + ZT.natLit 4 * (ZT.natLit 2 + M) * (K * N) * E)) := by
  -- `|K| ≤ K`, `|K − 2T| ≤ K`, `|4T(K − T)| ≤ K²`, `|K − T − S| ≤ K`, `|2K| ≤ 2K`
  have k₁ : Γ ⊢[PRAAx] zle (-K) K := by ipra_zle 2 * zsl hT₀ + 2 * zsl hT₁
  have k₂ : Γ ⊢[PRAAx] zle K K := zle_of_comb 0 (by ring) nn_zero
  have a₁ : Γ ⊢[PRAAx] zle (-K) (K - ZT.natLit 2 * T) := by ipra_zle 2 * zsl hT₁
  have a₂ : Γ ⊢[PRAAx] zle (K - ZT.natLit 2 * T) K := by ipra_zle 2 * zsl hT₀
  have p := zabs_mul k₁ k₂ a₁ a₂
  have q := zabs_mul p.1 p.2 hXY₁ hXY₂
  have b₁ : Γ ⊢[PRAAx] zle (-(K * K)) (ZT.natLit 4 * (T * (K - T))) := by
    ipra_zle 4 * zsl hT₀ * zsl hT₁ + ZT.toZ Γ K ^ 2
  have b₂ : Γ ⊢[PRAAx] zle (ZT.natLit 4 * (T * (K - T))) (K * K) := by
    ipra_zle ZT.toZ Γ (K - ZT.natLit 2 * T) ^ 2
  have r := zabs_mul b₁ b₂ hGH₁ hGH₂
  have c₁ : Γ ⊢[PRAAx] zle (-(ZT.natLit 2 * K)) (ZT.natLit 2 * K) := by ipra_zle 4 * zsl hT₀ + 4 * zsl hT₁
  have c₂ : Γ ⊢[PRAAx] zle (ZT.natLit 2 * K) (ZT.natLit 2 * K) := zle_of_comb 0 (by ring) nn_zero
  have s₁ := zabs_mul c₁ c₂ hE₁ hE₂
  have s₂ := zabs_mul s₁.1 s₁.2 hY₁ hY₂
  have m₁ : Γ ⊢[PRAAx] zle (-K) (K - T - S) := by ipra_zle zsl hT₁ + zsl hS₁
  have m₂ : Γ ⊢[PRAAx] zle (K - T - S) K := by ipra_zle zsl hT₀ + zsl hS₀
  have u₁ := zabs_mul hE₁ hE₂ m₁ m₂
  have u₂ := zabs_mul u₁.1 u₁.2 hH₁ hH₂
  -- `W₁ − W₂ = K(K − 2T)(X − Y) − 2K(T − S)Y + T(K − T)(G − H) + (T − S)(K − T − S)H`
  constructor
  · ipra_zle 4 * zsl q.1 + zsl r.1 + 4 * zsl s₂.2 + 4 * zsl u₂.1
  · ipra_zle 4 * zsl q.2 + zsl r.2 + 4 * zsl s₂.1 + 4 * zsl u₂.2

/-- Normalization by `ℓ^1` norms `U, V ≥ λ ≥ 0` is `((d+1)/λ)`-Lipschitz coordinatewise, cleared of the
denominators `U V`: `|uᵢ − vᵢ| ≤ D`, `|U − V| ≤ d D` and `|vᵢ| ≤ V` give
`λ |uᵢ V − vᵢ U| ≤ (d + 1) D U V`. -/
theorem normalize_lipschitz {U V ui vi D l dd : ZT n} (hl : Γ ⊢[PRAAx] zle (ZT.natLit 0) l)
    (hU : Γ ⊢[PRAAx] zle l U) (hV : Γ ⊢[PRAAx] zle l V) (hv₁ : Γ ⊢[PRAAx] zle (-V) vi)
    (hv₂ : Γ ⊢[PRAAx] zle vi V) (huv₁ : Γ ⊢[PRAAx] zle (-D) (ui - vi)) (huv₂ : Γ ⊢[PRAAx] zle (ui - vi) D)
    (hUV₁ : Γ ⊢[PRAAx] zle (-(dd * D)) (V - U)) (hUV₂ : Γ ⊢[PRAAx] zle (V - U) (dd * D)) :
    (Γ ⊢[PRAAx] zle (-((dd + ZT.natLit 1) * D * U * V)) (l * (ui * V - vi * U))) ∧
      (Γ ⊢[PRAAx] zle (l * (ui * V - vi * U)) ((dd + ZT.natLit 1) * D * U * V)) := by
  have v₁ : Γ ⊢[PRAAx] zle (-V) V := by ipra_zle 2 * zsl hl + 2 * zsl hV
  have v₂ : Γ ⊢[PRAAx] zle V V := zle_of_comb 0 (by ring) nn_zero
  have p := zabs_mul huv₁ huv₂ v₁ v₂
  have q := zabs_mul hv₁ hv₂ hUV₁ hUV₂
  -- `uᵢV − vᵢU = (uᵢ − vᵢ)V + vᵢ(V − U)`, so `|uᵢV − vᵢU| ≤ (d + 1) D V =: Z`, and `λ|·| ≤ λ Z ≤ U Z`
  have z₁ : Γ ⊢[PRAAx] zle (-((dd + ZT.natLit 1) * D * V)) (ui * V - vi * U) := by
    ipra_zle zsl p.1 + zsl q.1
  have z₂ : Γ ⊢[PRAAx] zle (ui * V - vi * U) ((dd + ZT.natLit 1) * D * V) := by
    ipra_zle zsl p.2 + zsl q.2
  have hZ : Γ ⊢[PRAAx] zle (ZT.natLit 0) ((dd + ZT.natLit 1) * D * V) := by
    refine zle_of_comb_two (zsl z₂ + zsl z₁) ?_ (by znn)
    zsimp; ring
  have nZ := nn_zle0 hZ
  have nl := nn_zle0 hl
  constructor
  · refine zle_of_comb (zsl hU * ZT.toZ Γ ((dd + ZT.natLit 1) * D * V) + ZT.toZ Γ l * zsl z₁) ?_
      (nn_add (nn_mul (nn_zsl _) nZ) (nn_mul nl (nn_zsl _)))
    zsimp; ring
  · refine zle_of_comb (zsl hU * ZT.toZ Γ ((dd + ZT.natLit 1) * D * V) + ZT.toZ Γ l * zsl z₂) ?_
      (nn_add (nn_mul (nn_zsl _) nZ) (nn_mul nl (nn_zsl _)))
    zsimp; ring

end LeanProofs.IPRA.Topology.SphereEstimates
