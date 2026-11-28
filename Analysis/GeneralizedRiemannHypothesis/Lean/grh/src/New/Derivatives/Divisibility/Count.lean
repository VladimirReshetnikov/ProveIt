import New.Derivatives.Divisibility.NullFrames
import New.Derivatives.FormalGroup.ThetaProducts

/-!
# Divisibility of the jets of a series with the normal form along products of minors

* `New.norm_jet_le_of_isHomogeneous`: Legendre's bound for the jet of an integral series along a
  homogeneous integral polynomial.
* `New.minorProd`, `New.predictedDivisibility`: products of minors, and the divisibility predicted
  by their shape.
* `New.Parameters.norm_jet_minorProd_le_of_hasNormalForm`: the count. The jet of a series with the
  normal form along a product of minors has the predicted divisibility, up to an error term.
* `New.Parameters.norm_jet_minorProd_le_of_charges`: the count with charges. The columns of height
  one at a set of marked places are removed from the prediction, and powers `p ^ w` of `p` on the
  rows, the charges, pay for them. The exponents `w` satisfy the condition of `New.IsChargeExponent`
  for pairs of columns that occur in `κ`, and `New.fillingCharge` is their sum over the boxes.
* `New.exists_norm_schurJet_le_norm_jet_minorProd`: an entry of the Schur matrix may be replaced by
  a product of minors of `z y` with `y` integral.

A linear substitution makes the couplings that matter in the degree of the jet divisible by `π_p`,
so that the series becomes integral in that degree. Legendre's bound applies, and the chain rule
gives the factor whose valuation is deducted. Each box gains about `γ_p`, and the deduction is
`v(π_p)` times a sum of numbers `New.deductionTerm`. The argument is carried out once, with charges
(`New.Parameters.norm_jet_minorProd_le_of_isChargeExponent`); the count itself is the case without
marked places and with all charges equal to one.

Notions from other files:
* `valRingCp p`: the valuation ring of `ℂ_[p]`; its elements are called integral, and a lower bound
  for a valuation is written as an upper bound for the norm.
* `New.jet R Q F`: the number `(Q(∂) F)(0)`, for a polynomial `Q` and a power series `F`.
* `New.WeylIndex n κ`, `New.schur`, `New.schurJet`: `κ τ h` is the number of columns of height `h`
  of a diagram at the place `τ`. The standard fillings of these diagrams index the Schur matrix of a
  family of matrices `z_τ`, and `schurJet κ F` is the matrix of jets of `F` along its entries.
* `New.coupling pr e`: the series `Γ_e = ∑ z_(τ, c) ^ p ^ e * z_(pr e τ, c)`, where `pr e τ` is the
  partner of the place `τ`. `New.deductionTerm p κ N marked τ τ' e` is the real number
  `min (t / p ^ e) (r' + t') + r / p ^ e + min (B / p ^ e) B'`. Only heights below `N` count: `t`
  is the number of columns of height one at `τ` (zero if `τ ∈ marked`), `r` that of the low columns
  (the other ones) and `B` that of their boxes. The primed letters refer to `τ'`.
* For `K = ℚ(√-d)`: `χ_K = New.chiK d`, `π_p = New.piPrimeInt d` has valuation
  `v(π_p) = New.piPrimeValuation d p`, `ρ_p = New.varpiValuation d p`, and
  `γ_p = New.gammaPrime d p = 1 / (p - 1) - ρ_p`. The set `I_p° = New.partnerExponents d p` consists
  of the odd numbers if `p` is inert and of all numbers if `p = d`, and
  `I_p = New.positivePartnerExponents d p` of its positive elements. `New.Parameters.partner` is the
  partner `-p ^ e τ` of `τ`.
* `New.HasNormalForm`: `F(ϖ z)` is an integral series times the exponential of `ϖ ^ (p + 1) / p`
  times an integral combination of the powers `Γ_e ^ p ^ j`.

## Relation to the literature

One- and two-variable divisibility at inert `p` over an imaginary quadratic field is known in the
literature.

Related work: Katz, Divisibilities, congruences, and Cartier duality, 1981; Chellali, Congruences
entre nombres de Bernoulli–Hurwitz dans le cas supersingulier, 1990; Fujiwara, On divisibilities of
special values of real analytic Eisenstein series, 1988; Bannai–Kobayashi–Yasuda, Radius of
convergence of the p-adic sigma function, 2017.
-/

open Finset MvPolynomial Matrix Fintype

namespace New

section Factorials
variable {p : ℕ} [Fact p.Prime] {σ : Type} [Fintype σ]

/-- Legendre's bound for a multi-index `d`, of degree `l = d.degree`: the valuation of `∏ (d x)!`
is at least `l / (p - 1) - card σ * (1 + ⌊log_p l⌋)`. -/
lemma norm_prod_factorial_le (d : σ →₀ ℕ) :
    ‖d.prod fun (_ : σ) (k : ℕ) ↦ (k.factorial : ℂ_[p])‖ ≤
      p ^ (card σ * (p.log d.degree + 1) - d.degree / (p - 1) : ℝ) := by
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  have h_legendre (x : σ) :
      (d x / (p - 1) - padicValNat p (d x).factorial : ℝ) ≤ p.log d.degree + 1 := by
    have h_mem : (d x / (p - 1) - (p.log d.degree + 1 : ℕ) : ℝ) ≤ padicValNat p (d x).factorial :=
      (padicValNat_factorial_mem_Icc
        ((d.le_degree x).trans_lt (p.lt_pow_succ_log_self hp _))).1
    push_cast at h_mem
    linarith
  have h_sum : ∑ x, (d x / (p - 1) - padicValNat p (d x).factorial : ℝ) ≤
      card σ • (p.log d.degree + 1 : ℝ) := sum_le_card_nsmul univ _ _ fun x _ ↦ h_legendre x
  rw [sum_sub_distrib, ← sum_div, ← Nat.cast_sum, ← d.degree_eq_sum, nsmul_eq_mul] at h_sum
  calc
    _ = ∏ x, (p : ℝ)⁻¹ ^ padicValNat p (d x).factorial := by
      rw [d.prod_fintype _ (by simp), norm_prod]
      exact prod_congr rfl fun x _ ↦ norm_natCast_eq_inv_pow_padicValNat (d x).factorial_ne_zero
    _ = (p : ℝ) ^ (-∑ x, (padicValNat p (d x).factorial : ℝ)) := by
      rw [← Nat.cast_sum, Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow,
        prod_pow_eq_pow_sum]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (mod_cast hp.le) (by linarith)

/-- If the coefficients of degree `l` of the series `G` are integral and `Q` is a homogeneous
polynomial of degree `l` with integral coefficients, then the jet `(Q(∂) G)(0)` has valuation at
least `l / (p - 1) - card σ * (1 + ⌊log_p l⌋)`.

A consequence of the lower bound `v(m!) ≥ m / (p - 1) - (1 + ⌊log_p m⌋)` given by Legendre's
formula, applied to each exponent of each monomial of `Q`. -/
lemma norm_jet_le_of_isHomogeneous {G : MvPowerSeries σ ℂ_[p]} {l : ℕ}
    (hG : ∀ d : σ →₀ ℕ, d.degree = l → ‖G.coeff d‖ ≤ 1) {Q : MvPolynomial σ (valRingCp p)}
    (hQ : Q.IsHomogeneous l) :
    ‖jet ℂ_[p] (Q.map (valRingCp p).subtype) G‖ ≤
      p ^ (card σ * (p.log l + 1) - l / (p - 1) : ℝ) := by
  rw [Q.as_sum, map_sum, map_sum, LinearMap.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d hd ↦ ?_
  have h_deg : d.degree = l := by_contra fun h_ne ↦ mem_support_iff.1 hd (hQ.coeff_eq_zero h_ne)
  rw [map_monomial, jet_monomial, norm_mul, norm_mul, ← h_deg]
  grw [show ‖(valRingCp p).subtype (Q.coeff d)‖ ≤ 1 from (Q.coeff d).property, hG d h_deg,
    norm_prod_factorial_le, one_mul, mul_one]

end Factorials

section Minors
variable {Φ n n' R : Type} [Fintype Φ] [Fintype n] [Fintype n'] [DecidableEq n'] [CommRing R]
  {κ : Φ → ℕ → ℕ}

/-- The polynomial `P_y(z)` in the entries `X (τ, b, a)` of matrices `z_τ` of size `n' × n`. It is
the product, over the places `τ` and the columns `j` of height `h < card n'` of the diagram `κ τ`,
of the minor of `z_τ y_τ` on the rows `(i' τ).1 h j b` that the filling `i'` puts into the column
and on the first `h` columns. -/
noncomputable def minorProd (i' : WeylIndex n' κ) (y : Φ → n → ℕ → R) :
    MvPolynomial (Φ × n' × n) R :=
  ∏ τ : Φ, ∏ h : Fin (card n'), ∏ j : Fin (κ τ h),
    (of fun b k : Fin h ↦ ∑ a : n, y τ a k • X (τ, (i' τ).1 h j b, a)).det

end Minors

section Directions
variable {Φ n n' R : Type} [Fintype Φ] [Fintype n] [Fintype n'] [DecidableEq n']
  [CommRing R] {κ : Φ → ℕ → ℕ}

/-- The index type of the new variables `s_(τ h k b)`: an index `(⟨h, k⟩, τ, b)` consists of a
height `h < N`, a direction `k < h` of that height, a place `τ` and a row `b`. -/
abbrev DirectionVar (Φ n' : Type) (N : ℕ) : Type := (Σ h : Fin N, Fin h) × Φ × n'

omit [DecidableEq n'] in
lemma card_directionVar_le : card (DirectionVar Φ n' (card n')) ≤ card Φ * card n' ^ 3 := by
  have h_pairs : card (Σ h : Fin (card n'), Fin h) ≤ card n' * card n' := by
    simpa using sum_le_card_nsmul univ (fun h : Fin (card n') ↦ (h : ℕ)) _ fun h _ ↦ h.isLt.le
  rw [card_prod, card_prod]
  exact (Nat.mul_le_mul_right _ h_pairs).trans_eq (by ring)

/-- The matrix of the linear substitution `z(s)` with row factors `c` and directions `β`: row `b`
of `z_τ(s)` is `∑_(h, k) c_(τ h b) s_(τ h k b) β_(τ h k)`. So the entry at `x = (τ, b, a)` and
`o = (⟨h, k⟩, τ', b')` is `c τ h b * β τ h k a` if `(τ', b') = (τ, b)`, and zero otherwise. -/
noncomputable def directionSubst [DecidableEq Φ]
    {N : ℕ} (c : Φ → ℕ → n' → R) (β : Φ → ∀ h : ℕ, Fin h → n → R) :
    Matrix (Φ × n' × n) (DirectionVar Φ n' N) R := open Classical in
  of fun (x : Φ × n' × n) (o : DirectionVar Φ n' N) ↦
    if o.2 = (x.1, x.2.1) then c x.1 o.1.1 x.2.1 * β x.1 o.1.1 o.1.2 x.2.2 else 0

/-- The map `linSubst M` sends each variable `X o` to `∑_x M x o • X x`. For the matrix `M` of the
substitution `z(s)` it sends `s_(τ h k b)` to `c_(τ h b)` times the linear form
`∑_a β_(τ h k a) z_(τ b a)`. -/
lemma linSubst_directionSubst_X [DecidableEq Φ]
    {N : ℕ} (c : Φ → ℕ → n' → R) (β : Φ → ∀ h : ℕ, Fin h → n → R)
    (h : Fin N) (k : Fin h) (τ : Φ) (b : n') :
    linSubst (directionSubst c β) (X (⟨h, k⟩, τ, b)) =
      C (c τ h b) * ∑ a : n, C (β τ h k a) * X (τ, b, a) := by
  simp [directionSubst, linSubst, sum_prod_type, smul_eq_C_mul, mul_sum, ite_and,
    mul_assoc]

variable (R) in
/-- The polynomial `P_*` in the new variables: the product, over the places `τ` and the columns `j`
of height `h < card n'` of the diagram `κ τ`, of the determinants `det (s_(τ h k b))`, with `k < h`
and `b` among the rows that the filling `i'` puts into the column. -/
noncomputable def columnDetProd (i' : WeylIndex n' κ) :
    MvPolynomial (DirectionVar Φ n' (card n')) R :=
  ∏ τ : Φ, ∏ h : Fin (card n'), ∏ j : Fin (κ τ h),
    (of fun b k : Fin h ↦ X (⟨h, k⟩, τ, (i' τ).1 h j b)).det

/-- The polynomial `columnDetProd R i'` is compatible with change of the coefficient ring. -/
lemma map_columnDetProd {R' : Type} [CommRing R'] (φ : R →+* R') (i' : WeylIndex n' κ) :
    (columnDetProd R i').map φ = columnDetProd R' i' := by
  simp [columnDetProd, RingHom.map_det, Matrix.map]

omit [Fintype Φ] [Fintype n'] [DecidableEq n'] in
/-- The determinant of the `h × h` matrix of the variables `s_(τ h k b) = X (⟨h, k⟩, τ, I b)` of
`MvPolynomial (DirectionVar Φ n' N) R`, with rows `I b` and directions `k < h`, is homogeneous of
degree `h`. -/
lemma isHomogeneous_det_directionVar {N : ℕ} (τ : Φ) (h : Fin N) (I : Fin h → n') :
    IsHomogeneous (of fun b k : Fin h ↦
      (X (⟨h, k⟩, τ, I b) : MvPolynomial (DirectionVar Φ n' N) R)).det h := by
  have h_term (σ : Equiv.Perm (Fin h)) : IsHomogeneous
      (∏ k : Fin h, (X (⟨h, k⟩, τ, I (σ k)) : MvPolynomial (DirectionVar Φ n' N) R)) h := by
    simpa using IsHomogeneous.prod univ _ (fun _ ↦ 1) fun k _ ↦
      isHomogeneous_X R ((⟨h, k⟩, τ, I (σ k)) : DirectionVar Φ n' N)
  rw [det_apply']
  refine IsHomogeneous.sum univ _ h fun σ _ ↦ ?_
  simpa only [map_intCast, of_apply] using (h_term σ).C_mul ((Equiv.Perm.sign σ : ℤ) : R)

/-- The product `columnDetProd R i'` of the determinants of the columns of `κ` is homogeneous. Its
degree `boxes κ (card n')` is the number of boxes in the columns of height below `card n'`. -/
lemma isHomogeneous_columnDetProd (i' : WeylIndex n' κ) :
    (columnDetProd R i').IsHomogeneous (boxes κ (card n')) := by
  have h_boxes : boxes κ (card n') = ∑ τ : Φ, ∑ h : Fin (card n'), ∑ _ : Fin (κ τ h), (h : ℕ) := by
    simp [boxes, sum_range, mul_comm]
  rw [h_boxes, columnDetProd]
  exact .prod univ _ _ fun τ _ ↦ .prod univ _ _ fun h _ ↦ .prod univ _ _ fun j _ ↦
    isHomogeneous_det_directionVar τ h ((i' τ).1 h j)

/-- The chain rule for the substitution `z(s)` along the polynomial `P_* = columnDetProd R i'`. The
filling `i'` puts the row `(i' τ).1 h j b` into box `b` of column `j` of height `h` at the place
`τ`. With new variables `s_(τ h k r)`, `P_*` is the product over all `τ`, `h`, `j` of the
determinants `det (s_(τ h k r))`, with `k < h` and `r` among the rows of the column. The matrix
`directionSubst c (newDirection g y)` defines the substitution `z_(τ r a) = ∑_(h, k) c_(τ h r) *
β_(τ h k a) * s_(τ h k r)`, where `β_(τ h k a)` is the new direction
`∑_k' (g τ h)_(k k') y_(τ a k')`. The jet of `F(z(s))` along `P_*` is the jet of `F` along the
product of minors `minorProd i' y`, times `det (g τ h)` for each column and `c_(τ h r)` for each
box, `r` being its row. -/
lemma jet_columnDetProd_subst [DecidableEq Φ] (i' : WeylIndex n' κ) (c : Φ → ℕ → n' → R)
    (g : Φ → ∀ h : ℕ, Matrix (Fin h) (Fin h) R) (y : Φ → n → ℕ → R)
    (F : MvPowerSeries (Φ × n' × n) R) :
    jet R (columnDetProd R i')
        (F.subst fun x : Φ × n' × n ↦ linearSeries (directionSubst c (newDirection g y) x)) =
      (∏ τ : Φ, ∏ h : Fin (card n'), ∏ j : Fin (κ τ h),
        ((g τ h).det * ∏ b : Fin h, c τ h ((i' τ).1 h j b))) *
        jet R (minorProd i' y) F := by
  -- For one column, the matrix of derivatives along the `β` is that along the `y` times `gᵀ`,
  -- with the rows scaled by the `c`.
  have h_column (τ : Φ) (h : Fin (card n')) (I : Fin h → n') :
      (linSubst (directionSubst c (newDirection g y))).mapMatrix
          (of fun b k : Fin h ↦ X (⟨h, k⟩, τ, I b)) =
        diagonal (fun b ↦ C (c τ h (I b))) *
          (of fun b k : Fin h ↦ ∑ a : n, y τ a k • X (τ, I b, a)) * C.mapMatrix (g τ h)ᵀ := by
    ext b k : 1
    rw [Matrix.mul_assoc, diagonal_mul, AlgHom.mapMatrix_apply, map_apply, of_apply,
      linSubst_directionSubst_X]
    simp only [newDirection, dotProduct, mul_apply, of_apply, RingHom.mapMatrix_apply, map_apply,
      transpose_apply, map_sum, map_mul, smul_eq_C_mul, sum_mul]
    exact congrArg _ (sum_comm.trans (sum_congr rfl fun k' _ ↦ sum_congr rfl fun a _ ↦ by ring))
  have h_poly : linSubst (directionSubst c (newDirection g y)) (columnDetProd R i') =
      (∏ τ : Φ, ∏ h : Fin (card n'), ∏ j : Fin (κ τ h),
        ((g τ h).det * ∏ b : Fin h, c τ h ((i' τ).1 h j b))) • minorProd i' y := by
    rw [columnDetProd, minorProd, smul_eq_C_mul]
    simp only [map_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun τ _ ↦ prod_congr rfl fun h _ ↦ prod_congr rfl fun j _ ↦ ?_
    rw [AlgHom.map_det, h_column, det_mul, det_mul, det_diagonal, ← RingHom.map_det, det_transpose,
      map_mul, map_prod]
    ring
  rw [jet_subst_linearSeries, h_poly, LinearMap.map_smul₂, smul_eq_mul]

end Directions

section Couplings
variable {p : ℕ} [Fact p.Prime] {Φ n n' : Type} [Fintype Φ] [DecidableEq Φ] [Fintype n] [Fintype n']
  [DecidableEq n'] {π : valRingCp p} {pr : ℕ → Φ → Φ} {e : ℕ}

omit [DecidableEq Φ] in
/-- Let `π` divide `p`, let `α` be the index type of the entries at one place, and substitute linear
forms `∑_o z x o * s_o` for the variables `X_x`, `x = (τ, a) ∈ Φ × α`, of the coupling
`Γ_e = ∑ X_(τ, a) ^ p ^ e * X_(pr e τ, a)`. Modulo `p` the result is a combination of the
`s_o ^ p ^ e * s_q`. If `π` divides all coefficients of this combination, it divides the result. -/
lemma dvd_subst_coupling {α ι : Type} [Fintype α] [Fintype ι] (hπ : π ∣ p)
    {z : Φ × α → ι → valRingCp p}
    (hz : ∀ o q : ι, π ∣ ∑ x : Φ × α, z x o ^ p ^ e * z (pr e x.1, x.2) q) :
    MvPowerSeries.C π ∣ (coupling pr e : MvPowerSeries (Φ × α) (valRingCp p)).subst
      fun x : Φ × α ↦ linearSeries (z x) := by
  classical
  have hp : MvPowerSeries.C π ∣ (p : MvPowerSeries ι (valRingCp p)) := by
    simpa using map_dvd MvPowerSeries.C hπ
  have h_pow (x : Φ × α) : MvPowerSeries.C π ∣
      linearSeries (z x) ^ p ^ e - ∑ o, (z x o • MvPowerSeries.X o) ^ p ^ e :=
    dvd_sum_pow_sub_sum hp _ _ e
  have h_expand :
      ∑ x, (∑ o, (z x o • MvPowerSeries.X o) ^ p ^ e) * linearSeries (z (pr e x.1, x.2)) =
        ∑ o, ∑ q, (∑ x, z x o ^ p ^ e * z (pr e x.1, x.2) q) •
          (MvPowerSeries.X o ^ p ^ e * MvPowerSeries.X q) := by
    simp only [linearSeries, Finset.sum_mul_sum, smul_pow, smul_mul_smul_comm, sum_smul]
    exact sum_comm.trans (sum_congr rfl fun o _ ↦ sum_comm)
  have h_comb : MvPowerSeries.C π ∣
      ∑ x, (∑ o, (z x o • MvPowerSeries.X o) ^ p ^ e) * linearSeries (z (pr e x.1, x.2)) := by
    rw [h_expand]
    exact dvd_sum fun o _ ↦ dvd_sum fun q _ ↦ by
      simpa only [MvPowerSeries.smul_eq_C_mul] using (map_dvd _ (hz o q)).mul_right _
  rw [subst_coupling (MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp [linearSeries])),
    ← dvd_sub_left h_comb, ← sum_sub_distrib]
  simpa only [← sub_mul] using dvd_sum fun x (_ : x ∈ univ) ↦ (h_pow x).mul_right _

/-- Let `π` divide `p`. The source variables `s_(τ h k b)` are indexed by a height `h < N`, a
direction `k < h`, a place `τ` and a row `b`. The matrix `directionSubst c β` defines the
substitution `z_(τ b a) = ∑_(h, k) c_(τ h b) * β_(τ h k a) * s_(τ h k b)`, with row factors `c` and
directions `β`. If `π` divides `c ^ p ^ e * c'` times the pairing `[β, β']_e = ∑ β_a ^ p ^ e * β'_a`
for each place `τ` and its partner `pr e τ`, each row and all directions `β` at `τ` and `β'` at the
partner, then `π` divides `Γ_e(z(s))`. -/
lemma dvd_subst_coupling_directionSubst (hπ : π ∣ p) {N : ℕ} {c : Φ → ℕ → n' → valRingCp p}
    {β : Φ → ∀ h : ℕ, Fin h → n → valRingCp p}
    (h_pair : ∀ (τ : Φ) (b : n') (h : ℕ) (k : Fin h) (h' : ℕ) (k' : Fin h'),
      π ∣ c τ h b ^ p ^ e * c (pr e τ) h' b * ∑ a : n, β τ h k a ^ p ^ e * β (pr e τ) h' k' a) :
    MvPowerSeries.C π ∣ (coupling pr e : MvPowerSeries (Φ × n' × n) (valRingCp p)).subst
      fun x : Φ × n' × n ↦ linearSeries (directionSubst (N := N) c β x) := by
  classical
  refine dvd_subst_coupling hπ fun ⟨⟨h, k⟩, τ, b⟩ ⟨⟨h', k'⟩, τ', b'⟩ ↦ ?_
  -- The coefficient vanishes unless `τ'` is the partner of `τ` and `b' = b`.
  have h_coeff : ∑ x : Φ × n' × n, directionSubst c β x (⟨h, k⟩, τ, b) ^ p ^ e *
      directionSubst c β (pr e x.1, x.2) (⟨h', k'⟩, τ', b') =
      if τ' = pr e τ ∧ b' = b then
        c τ h b ^ p ^ e * c (pr e τ) h' b * ∑ a, β τ h k a ^ p ^ e * β (pr e τ) h' k' a
      else 0 := by
    simp only [directionSubst, of_apply, ite_pow, zero_pow (NeZero.ne (p ^ e)), ite_mul, zero_mul,
      Prod.mk.injEq, sum_prod_type, ite_and (τ = _), sum_ite_irrel, sum_const_zero,
      Fintype.sum_ite_eq]
    simp only [mul_ite, mul_zero, sum_ite_irrel, sum_const_zero, mul_pow, mul_sum,
      mul_mul_mul_comm _ (β τ h k _ ^ p ^ e)]
  rw [h_coeff]
  split_ifs
  exacts [h_pair τ b h k h' k', dvd_zero π]

/-- The charges `p ^ w τ h b` (place, height, row) cover the exempt pairs for the set `ev` of marked
places and the map `partner` on places. A pair consists of the height one at `τ` and a height `h` at
`partner τ`. It is exempt if `τ ∈ ev`, or if `h = 1` and `partner τ ∈ ev`. In each exempt pair and
each row `b`, one of the two exponents is not zero, so that `p` divides the product of the
charges. -/
def IsChargeExponent (partner : Φ → Φ) (ev : Finset Φ) (w : Φ → ℕ → n' → ℕ) : Prop :=
  ∀ (τ : Φ) (h : ℕ) (b : n'),
    τ ∈ ev ∨ h = 1 ∧ partner τ ∈ ev → w τ 1 b ≠ 0 ∨ w (partner τ) h b ≠ 0

/-- The sum of the exponents `w τ h r` over the boxes in the columns of height `h < card n'` of the
diagrams `κ τ`, where `r` is the row that the filling `i'` puts into the box. -/
def fillingCharge {κ : Φ → ℕ → ℕ} (w : Φ → ℕ → n' → ℕ) (i' : WeylIndex n' κ) : ℕ :=
  ∑ τ : Φ, ∑ h : Fin (card n'), ∑ j : Fin (κ τ h), ∑ b : Fin h, w τ h ((i' τ).val h j b)

omit [DecidableEq Φ] in
lemma fillingCharge_zero {κ : Φ → ℕ → ℕ} (i' : WeylIndex n' κ) :
    fillingCharge (0 : Φ → ℕ → n' → ℕ) i' = 0 := by simp [fillingCharge]

omit [DecidableEq Φ] in
/-- The sum `fillingCharge w i'` of the exponents `w` over the filling `i'` depends only on the
values `w τ h b` at the heights `h` that occur in `κ τ` (those with `κ τ h ≠ 0`). -/
lemma fillingCharge_congr {κ : Φ → ℕ → ℕ} {w w' : Φ → ℕ → n' → ℕ}
    (h_eq : ∀ (τ : Φ) (h : ℕ) (b : n'), κ τ h ≠ 0 → w τ h b = w' τ h b) (i' : WeylIndex n' κ) :
    fillingCharge w i' = fillingCharge w' i' :=
  sum_congr rfl fun τ _ ↦ sum_congr rfl fun h _ ↦ sum_congr rfl fun j _ ↦
    sum_congr rfl fun b _ ↦ h_eq τ h ((i' τ).val h j b) j.pos.ne'

/-- Let `π` divide `p` and let `marked` be a set of places. A pair of heights `h` at `τ` and `h'` at
the partner `τ' = pr e τ` is exempt (`IsExemptPair`) if `h = 1`, and `τ ∈ marked` or both `h' = 1`
and `τ' ∈ marked`. Suppose that `π` divides the pairings `∑ β_a ^ p ^ e * β'_a` of directions `β` at
`τ` and `β'` at `τ'`, except for the exempt pairs. If one of the two exponents `w` is positive in
each exempt pair (`IsChargeExponent`), then `π` divides the coupling
`Γ_e = ∑ z_(τ b a) ^ p ^ e * z_(pr e τ, b a)` after the substitution `directionSubst`. -/
lemma dvd_subst_coupling_directionSubst_of_charges (hπ : π ∣ p) {N : ℕ} {marked : Finset Φ}
    {w : Φ → ℕ → n' → ℕ} {β : Φ → ∀ h : ℕ, Fin h → n → valRingCp p}
    (hw : IsChargeExponent (pr e) marked w)
    (h_pair : ∀ (τ : Φ) (h : ℕ) (k : Fin h) (h' : ℕ) (k' : Fin h'),
      ¬IsExemptPair marked τ (pr e τ) h h' →
        π ∣ ∑ a : n, β τ h k a ^ p ^ e * β (pr e τ) h' k' a) :
    MvPowerSeries.C π ∣ (coupling pr e : MvPowerSeries (Φ × n' × n) (valRingCp p)).subst
      fun x : Φ × n' × n ↦ linearSeries (directionSubst (N := N)
        (fun (τ : Φ) (h : ℕ) (b : n') ↦ (p : valRingCp p) ^ w τ h b) β x) := by
  refine dvd_subst_coupling_directionSubst hπ fun τ b h k h' k' ↦ ?_
  by_cases h_exempt : IsExemptPair marked τ (pr e τ) h h'
  · obtain ⟨rfl, h_place⟩ := h_exempt
    have h_factor : (p : valRingCp p) ∣ (p ^ w τ 1 b) ^ p ^ e * p ^ w (pr e τ) h' b := by
      obtain h_left | h_right := hw τ h' b h_place
      · exact (dvd_pow (dvd_pow_self _ h_left) (pow_ne_zero e (Nat.Prime.ne_zero Fact.out))
          ).mul_right _
      · exact (dvd_pow_self _ h_right).mul_left _
    exact (hπ.trans h_factor).mul_right _
  · exact (h_pair τ h k h' k' h_exempt).mul_left _

/-- The chain rule in norms for `F(ϖ z)`. Here `z` is the linear substitution `directionSubst`, that
is `z_(τ r a) = ∑_(h, k) p ^ (w τ h r) * β_(τ h k a) * s_(τ h k r)` with the new directions
`β_(τ h k a) = ∑_k' (g τ h)_(k k') y_(τ a k')`, and `seriesToCp` reads an integral series as one
over `ℂ_[p]`. The filling `i'` puts a row `r` into each box of the `κ τ h` columns of height `h` at
the place `τ`. The polynomial `columnDetProd` is the product over the columns with `h < card n'` of
the determinants `det (s_(τ h k r))`, with `k < h` and `r` among the rows of the column, and
`minorProd` is the product of the corresponding minors of `z_τ y_τ`. The norm of the jet along the
former is that of the jet of `F` along the latter up to factors: each box gives `ϖ` and its row
factor, and each column gives `det (g τ h)`. -/
lemma norm_jet_columnDetProd_subst {κ : Φ → ℕ → ℕ} (i' : WeylIndex n' κ) (w : Φ → ℕ → n' → ℕ)
    (g : Φ → ∀ h : ℕ, Matrix (Fin h) (Fin h) (valRingCp p)) (y : Φ → n → ℕ → valRingCp p)
    (ϖ : ℂ_[p]) (F : MvPowerSeries (Φ × n' × n) ℂ_[p]) :
    ‖jet ℂ_[p] (columnDetProd ℂ_[p] i') (F.subst fun x : Φ × n' × n ↦ ϖ • seriesToCp
        (linearSeries (directionSubst (fun (τ : Φ) (h : ℕ) (b : n') ↦ p ^ w τ h b)
          (newDirection g y) x)))‖ =
      ‖ϖ‖ ^ boxes κ (card n') * (p : ℝ)⁻¹ ^ fillingCharge w i' *
        (∏ τ : Φ, ∏ h : Fin (card n'), ‖((g τ h).det : ℂ_[p])‖ ^ κ τ h) *
        ‖jet ℂ_[p] (minorProd i' fun (τ : Φ) (a : n) (k : ℕ) ↦ (y τ a k : ℂ_[p])) F‖ := by
  let g' (τ : Φ) (h : ℕ) : Matrix (Fin h) (Fin h) ℂ_[p] := (valRingCp p).subtype.mapMatrix (g τ h)
  have h_subst (x : Φ × n' × n) : ϖ • seriesToCp
      (linearSeries (directionSubst (fun τ h b ↦ p ^ w τ h b) (newDirection g y) x)) =
      linearSeries (directionSubst (N := card n') (fun τ h b ↦ ϖ * p ^ w τ h b)
        (newDirection g' fun τ a k ↦ (y τ a k : ℂ_[p])) x) := by
    simp only [linearSeries, map_sum, seriesToCp_smul, MvPowerSeries.map_X, smul_sum, smul_smul]
    refine sum_congr rfl fun o _ ↦ congrArg (· • _) ?_
    simp only [directionSubst, of_apply]
    split_ifs <;> simp [g', newDirection, dotProduct, mul_assoc]
  simp only [h_subst, jet_columnDetProd_subst, g', ← RingHom.map_det, Subring.subtype_apply, boxes,
    sum_range, fillingCharge, norm_prod, norm_mul, norm_pow, norm_p_eq_inv, prod_mul_distrib,
    prod_const, card_univ, Fintype.card_fin, ← pow_mul, prod_pow_eq_pow_sum]
  ring

end Couplings

section Predicted

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] (d p : ℕ) (pr : ℕ → Φ → Φ) (κ : Φ → ℕ → ℕ) (N : ℕ)

/-- The number `a_τ` of columns of height one at `τ`, among the heights below `N`. Here `κ τ h` is
the number of columns of height `h` at the place `τ`. -/
def heightOneColumns (τ : Φ) : ℕ := ∑ h ∈ range N, if h = 1 then κ τ h else 0

/-- The number `a'_τ` of low columns at `τ`, those whose height is below `N` and is not one. (A
diagram has no column of height zero; if `κ τ 0 ≠ 0`, these columns count here.) -/
def lowColumnCount (τ : Φ) : ℕ := ∑ h ∈ range N, if h = 1 then 0 else κ τ h

/-- The number `l_τ` of boxes in the low columns at `τ`, those whose height is below `N` and is not
one. -/
def lowBoxCount (τ : Φ) : ℕ := ∑ h ∈ range N, h * if h = 1 then 0 else κ τ h

/-- The diagrams `κ` without their columns of height one at the places of the set `ev`, the marked
places. -/
def eraseHeightOne (ev : Finset Φ) (τ : Φ) (h : ℕ) : ℕ :=
  if h = 1 ∧ τ ∈ ev then 0 else κ τ h

/-- The predicted divisibility at a prime `p`. Let `a_τ` be the number of columns of
height one, `a'_τ` the number of the other columns and `l_τ` the number of boxes in these, all
among the heights below `N`. With `τ' = pr e τ` the predicted divisibility is
`v(π_p) ∑_e ∑_τ ((a_τ / p ^ e - a_τ' - a'_τ')₊ + (l_τ / p ^ e - l_τ')₊ - a'_τ / p ^ e)`. Here
`v(π_p) = piPrimeValuation d p`, and `e` runs over `I_p = positivePartnerExponents d p` (the odd
numbers if `p` is inert, all `e ≥ 1` if `p = d`, none if `p` splits). If `p = d`, half the sum of
`min (a_τ, a_τ' + a'_τ') + a'_τ + min (l_τ, l_τ')` with `τ' = pr 0 τ` is subtracted. -/
noncomputable def predictedDivisibility [Fact d.Prime] : ℝ :=
  let a (τ : Φ) : ℝ := heightOneColumns κ N τ
  let a' (τ : Φ) : ℝ := lowColumnCount κ N τ
  let l (τ : Φ) : ℝ := lowBoxCount κ N τ
  piPrimeValuation d p * (∑' e : ℕ, if e ∈ positivePartnerExponents d p then
      ∑ τ : Φ,
        ((a τ / p ^ e - a (pr e τ) - a' (pr e τ))⁺ + (l τ / p ^ e - l (pr e τ))⁺ - a' τ / p ^ e)
    else 0) -
  if p = d then
    1 / 2 * ∑ τ : Φ, (min (a τ) (a (pr 0 τ) + a' (pr 0 τ)) + a' τ + min (l τ) (l (pr 0 τ)))
  else 0

/-- The sum of the deduction terms for the couplings of the places `τ` with their partners `pr e τ`,
without marked places; it is zero unless `e` lies in `I_p° = partnerExponents d p`. -/
noncomputable def deductionAt [Fact d.Prime] (e : ℕ) : ℝ :=
  if e ∈ partnerExponents d p then ∑ τ : Φ, deductionTerm p κ N ∅ τ (pr e τ) e else 0

omit [Fintype Φ] in
lemma eraseHeightOne_empty : eraseHeightOne κ ∅ = κ := by
  ext τ h
  simp [eraseHeightOne]

omit [Fintype Φ] in
/-- The deduction term without marked places, in terms of the numbers of columns of height one, of
low columns (those of other height) and of boxes in the low columns. -/
lemma deductionTerm_empty (τ τ' : Φ) (e : ℕ) :
    deductionTerm p κ N ∅ τ τ' e =
      min (heightOneColumns κ N τ / p ^ e : ℝ) (heightOneColumns κ N τ' + lowColumnCount κ N τ') +
        lowColumnCount κ N τ / p ^ e +
        min (lowBoxCount κ N τ / p ^ e : ℝ) (lowBoxCount κ N τ') := by
  simp only [deductionTerm, heightOneColumns, lowColumnCount, lowBoxCount, notMem_empty,
    not_false_eq_true, and_true, add_comm]

omit [Fintype Φ] in
/-- Marking the places of `marked` has the same effect on the deduction terms as removing their
columns of height one. -/
lemma deductionTerm_eraseHeightOne (marked : Finset Φ) (τ τ' : Φ) (e : ℕ) :
    deductionTerm p (eraseHeightOne κ marked) N ∅ τ τ' e = deductionTerm p κ N marked τ τ' e := by
  have h_one (σ : Φ) (h : ℕ) :
      (if h = 1 ∧ σ ∉ (∅ : Finset Φ) then eraseHeightOne κ marked σ h else 0) =
        if h = 1 ∧ σ ∉ marked then κ σ h else 0 := by grind [eraseHeightOne]
  have h_low (σ : Φ) (h : ℕ) : (if h = 1 then 0 else eraseHeightOne κ marked σ h) =
      if h = 1 then 0 else κ σ h := by grind [eraseHeightOne]
  simp only [deductionTerm, h_one, h_low]

omit [DecidableEq Φ] in
/-- The number `boxes κ N` of boxes in the columns of height below `N` is the sum over the places
`τ` of `heightOneColumns κ N τ`, the columns of height one, and `lowBoxCount κ N τ`, the boxes in
the columns of other height below `N`. -/
lemma boxes_eq_sum :
    (boxes κ N : ℝ) = ∑ τ : Φ, (heightOneColumns κ N τ + lowBoxCount κ N τ : ℝ) := by
  have h_split (τ : Φ) (h : ℕ) :
      h * κ τ h = (if h = 1 then κ τ h else 0) + h * if h = 1 then 0 else κ τ h := by grind
  simp only [boxes, heightOneColumns, lowBoxCount, ← Nat.cast_add, ← Nat.cast_sum,
    ← sum_add_distrib, ← h_split]

lemma deductionAt_nonneg [Fact d.Prime] (e : ℕ) : 0 ≤ deductionAt d p pr κ N e := by
  simp only [deductionAt, deductionTerm_empty]
  positivity

/-- The sums of deduction terms are summable over `e`: they are bounded by a constant times `p⁻ᵉ`.
The term `deductionAt d p pr κ N e` is the sum over `τ` of `deductionTerm p κ N ∅ τ (pr e τ) e` if
`e ∈ partnerExponents d p` (odd if `p` is inert in `ℚ(√-d)`, arbitrary if `p = d`, none if `p`
splits), and zero otherwise. -/
lemma summable_deductionAt [Fact p.Prime] [Fact d.Prime] :
    Summable (deductionAt d p pr κ N) := by
  have hp : (1 : ℝ) < p := mod_cast Nat.Prime.one_lt Fact.out
  let c : ℝ := ∑ τ : Φ, (heightOneColumns κ N τ + lowColumnCount κ N τ + lowBoxCount κ N τ : ℝ)
  -- Term by term the count at `e` is at most `c / p ^ e`, a geometric series.
  refine ((summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp)).mul_left c
    ).of_nonneg_of_le (deductionAt_nonneg d p pr κ N) fun e ↦ ?_
  rw [deductionAt]
  split_ifs
  · rw [inv_pow, ← div_eq_mul_inv, sum_div]
    refine sum_le_sum fun τ _ ↦ ?_
    rw [deductionTerm_empty, add_div, add_div]
    gcongr <;> exact min_le_left _ _
  · positivity

/-- The deduction is `γ_p B` less the predicted divisibility. Here `d` is the prime of `ℚ(√-d)`, `p`
the prime at which one counts, `pr e τ` the partner of the place `τ`, `κ τ h` the number of columns
of height `h` at `τ`, `B` the number of boxes in the columns of height below `N`, and as usual
`v(π_p) = piPrimeValuation d p`, `γ_p = gammaPrime d p`. -/
lemma mul_tsum_deductionAt [Fact p.Prime] [Fact d.Prime] :
    piPrimeValuation d p * ∑' e : ℕ, deductionAt d p pr κ N e =
      gammaPrime d p * boxes κ N - predictedDivisibility d p pr κ N := by
  unfold predictedDivisibility
  extract_lets a a' l
  -- `a`, `a'`, `l` count columns of height one, low columns and their boxes. `zerothTerm` is the
  -- count at `e = 0`. Term by term, `u - min (u, u') = (u - u')₊`.
  let zerothTerm : ℝ := if p = d then
    ∑ τ : Φ, (min (a τ) (a (pr 0 τ) + a' (pr 0 τ)) + a' τ + min (l τ) (l (pr 0 τ))) else 0
  have h_posPart (u u' : ℝ) : (u - u')⁺ = u - min u u' := by
    rw [posPart_def, ← max_sub_sub_left, sub_self, max_comm]
  have h_term (e : ℕ) : (if e ∈ positivePartnerExponents d p then ∑ τ : Φ,
      ((a τ / p ^ e - a (pr e τ) - a' (pr e τ))⁺ + (l τ / p ^ e - l (pr e τ))⁺ - a' τ / p ^ e)
      else 0) =
      (if e ∈ positivePartnerExponents d p then (boxes κ N / p ^ e : ℝ) else 0) +
        (if e = 0 then zerothTerm else 0) - deductionAt d p pr κ N e := by
    simp only [deductionAt, deductionTerm_empty, boxes_eq_sum, sum_div, sub_sub, h_posPart,
      mem_positivePartnerExponents]
    obtain rfl | he := e.eq_zero_or_pos
    · simp [zerothTerm, a, a', l, mem_partnerExponents]
    · simp only [he, he.ne', true_and, ite_false, add_zero]
      split_ifs
      · rw [← sum_sub_distrib]
        exact sum_congr rfl fun τ _ ↦ by ring
      · rw [sub_zero]
  have h_sum : HasSum (fun e : ℕ ↦
      (if e ∈ positivePartnerExponents d p then (boxes κ N / p ^ e : ℝ) else 0) +
        (if e = 0 then zerothTerm else 0) - deductionAt d p pr κ N e)
      (boxes κ N * gammaPrime d p / piPrimeValuation d p + zerothTerm -
        ∑' e : ℕ, deductionAt d p pr κ N e) :=
    ((hasSum_div_pow_positivePartnerExponents d p (boxes κ N)).add (hasSum_ite_eq 0 zerothTerm)).sub
      (summable_deductionAt d p pr κ N).hasSum
  rw [tsum_congr h_term, h_sum.tsum_eq]
  simp only [zerothTerm, piPrimeValuation]
  split_ifs <;> ring

/-- Let `d` and `p` be primes, `pr e τ` the partner of the place `τ` and `κ τ h` the number of
columns of height `h` at `τ`; only heights below `N` count. The deduction for the set `marked` of
places is `v(π_p) = piPrimeValuation d p` times the sum of `deductionTerm p κ N marked τ (pr e τ) e`
over all `τ` and the `e ≤ e₀` in `I_p° = partnerExponents d p`. It is at most `γ_p B°` less the
predicted divisibility of `κ° = eraseHeightOne κ marked`, which is `κ` without its columns of height
one at the marked places. Here `B°` is the number of boxes of `κ°` and `γ_p = gammaPrime d p`. -/
lemma mul_sum_deductionTerm_le [Fact p.Prime] [Fact d.Prime] (marked : Finset Φ) (e₀ : ℕ) :
    piPrimeValuation d p *
        ∑ e ≤ e₀ with e ∈ partnerExponents d p, ∑ τ : Φ, deductionTerm p κ N marked τ (pr e τ) e ≤
      gammaPrime d p * boxes (eraseHeightOne κ marked) N -
        predictedDivisibility d p pr (eraseHeightOne κ marked) N := by
  rw [← mul_tsum_deductionAt]
  refine mul_le_mul_of_nonneg_left ?_ (piPrimeValuation_pos d p).le
  calc
    _ = ∑ e ≤ e₀, deductionAt d p pr (eraseHeightOne κ marked) N e := by
      simp only [sum_filter, deductionAt, deductionTerm_eraseHeightOne]
    _ ≤ _ := (summable_deductionAt d p pr _ N).sum_le_tsum (Iic e₀)
      fun e _ ↦ deductionAt_nonneg d p pr _ N e

end Predicted

namespace Parameters
variable (P : Parameters) (s : ℕ) {p : ℕ} [Fact p.Prime] [PadicPlace p] {n n' : Type} [Fintype n]
  [Fintype n'] {κ : P.Φ s → ℕ → ℕ} {ϖ : ℂ_[p]} {l : ℕ → ℕ → valRingCp p}
  {F : MvPowerSeries (P.Φ s × n' × n) ℂ_[p]}

/-- The count with charges, with the deduction cut at `⌊log_p B⌋`. Here `P` fixes the prime `d` of
`K = ℚ(√-d)`, `P.Φ s` is the set of infinite places of the field of level `s`, the instance
`PadicPlace p` is an embedding of `ℂ` into `ℂ_[p]`, and `κ τ h` is the number of columns of height
`h` at the place `τ`. Let `p` be non-split (`chiK P.d p ≠ 1`), let `v(ϖ) = ρ_p`, where
`ρ_p = varpiValuation P.d p = v(π_p) / (q_p - 1)` for the norm `q_p` of a prime above `p`, and let
`F` have the normal form for the exponents `e ∈ I_p°` (odd; all `e` if `p = d`): `F(ϖ z)` is an
integral series times the exponential of the product of `ϖ ^ (p + 1) / p` with a combination of
powers `Γ_e ^ p ^ j` of couplings, whose integral coefficients are given by `l`. Mark a set `marked`
of places, and give row `b` of the columns of height `h` at `τ` a charge `p ^ w τ h b`. For a
partner `τ'` of `τ`, one of `w τ 1 b` and `w τ' h b` is positive if `τ ∈ marked`, or if `h = 1` and
`τ' ∈ marked` (`IsChargeExponent`). The filling `i'` puts a row into each box of `κ`, and with the
integral matrices `y_τ` it defines the product of minors `P_y = minorProd i' y`: over the columns,
the minor of `z_τ y_τ` on the rows of the column and the first `h` columns. Let `B` be the number of
boxes. Then the valuation of `jet` of `F` along `P_y`, plus the sum `fillingCharge w i'` of the
exponents over the boxes, is at least `gammaPrime P.d p * B`, less `v(π_p) = piPrimeValuation P.d p`
times the sum of `deductionTerm` over all places and the exponents `e ∈ I_p°` with `e ≤ ⌊log_p B⌋`,
and less `f N ^ 3 (1 + ⌊log_p B⌋)`. Here `f` is the number of infinite places, `N` the number of
rows, and only columns of height below `N` are counted. -/
theorem norm_jet_minorProd_le_of_isChargeExponent [DecidableEq n'] (hp : chiK P.d p ≠ 1)
    (hϖ : ‖ϖ‖ = p ^ (-varpiValuation P.d p))
    (hF : HasNormalForm (partnerExponents P.d p) (P.partner s p) ϖ l F)
    (marked : Finset (P.Φ s)) (w : P.Φ s → ℕ → n' → ℕ)
    (hw : ∀ e ∈ partnerExponents P.d p, IsChargeExponent (P.partner s p e) marked w)
    (i' : WeylIndex n' κ) (y : P.Φ s → n → ℕ → valRingCp p) :
    let N : ℕ := card n'
    let B : ℕ := boxes κ N
    ‖jet ℂ_[p] (minorProd i' fun (τ : P.Φ s) (a : n) (k : ℕ) ↦ (y τ a k : ℂ_[p])) F‖ ≤
      p ^ (fillingCharge w i' - (gammaPrime P.d p * B -
        piPrimeValuation P.d p * ∑ e ≤ p.log B with e ∈ partnerExponents P.d p,
          ∑ τ : P.Φ s, deductionTerm p κ N marked τ (P.partner s p e τ) e -
        card (P.Φ s) * N ^ 3 * (p.log B + 1)) : ℝ) := by
  classical
  intro N B
  set m : ℕ := fillingCharge w i'
  have hp_pos : (0 : ℝ) < p := mod_cast Nat.Prime.pos Fact.out
  let π : valRingCp p := piPrimeInt P.d
  have hπ_dvd : π ∣ p := piPrimeInt_dvd_natCast P.d
  have hπ : ‖(π : ℂ_[p])‖ = p ^ (-piPrimeValuation P.d p) := norm_piPrimeInt P.d
  -- Step 1: new directions, and the chain rule.
  let S : Finset ℕ := {e ≤ p.log B | e ∈ partnerExponents P.d p}
  let D : ℝ := ∑ e ∈ S, ∑ τ : P.Φ s, deductionTerm p κ N marked τ (P.partner s p e τ) e
  obtain ⟨g, h_pair, h_det : ‖(π : ℂ_[p])‖ ^ D ≤
      ∏ τ : P.Φ s, ∏ h : Fin N, ‖((g τ h).det : ℂ_[p])‖ ^ κ τ h⟩ :=
    exists_newDirection_dvd hπ_dvd (P.partner s p) S N κ marked y
  let z := directionSubst (N := N) (fun τ h b ↦ (p : valRingCp p) ^ w τ h b) (newDirection g y)
  let G : MvPowerSeries (DirectionVar (P.Φ s) n' N) ℂ_[p] :=
    F.subst fun x ↦ ϖ • seriesToCp (linearSeries (z x))
  let c : ℝ := ‖ϖ‖ ^ B * (p : ℝ)⁻¹ ^ m * ∏ τ, ∏ h : Fin N, ‖((g τ h).det : ℂ_[p])‖ ^ κ τ h
  have h_chain : ‖jet ℂ_[p] (columnDetProd ℂ_[p] i') G‖ =
      c * ‖jet ℂ_[p] (minorProd i' fun τ a k ↦ (y τ a k : ℂ_[p])) F‖ :=
    norm_jet_columnDetProd_subst i' w g y ϖ F
  -- Step 2: `G` is integral in degree `B`, as `π` divides the couplings of `z` for `e ∈ S`.
  have hG (d : DirectionVar (P.Φ s) n' N →₀ ℕ) (hd : d.degree = B) : ‖G.coeff d‖ ≤ 1 :=
    hF.norm_coeff_subst_le_one (P.norm_pow_succ_div_mul_piPrimeInt hp hϖ).le
      (by simp [linearSeries]) (fun e he he_le ↦ dvd_subst_coupling_directionSubst_of_charges
        hπ_dvd (hw e he) (h_pair e (by simpa [S] using And.intro he_le he))) hd.le
  -- Step 3: Legendre's bound for `G`, divided by the factor `c` of the chain rule.
  have h_legendre : ‖jet ℂ_[p] (columnDetProd ℂ_[p] i') G‖ ≤
      p ^ (card (P.Φ s) * N ^ 3 * (p.log B + 1) - B / (p - 1) : ℝ) := by
    rw [← map_columnDetProd (valRingCp p).subtype]
    refine (norm_jet_le_of_isHomogeneous hG (isHomogeneous_columnDetProd i')).trans ?_
    gcongr
    exacts [mod_cast Nat.Prime.one_le Fact.out, mod_cast card_directionVar_le]
  have h_factor : p ^ (-varpiValuation P.d p * B - m + -piPrimeValuation P.d p * D : ℝ) ≤ c := by
    rw [Real.rpow_add hp_pos, Real.rpow_sub hp_pos, Real.rpow_mul_natCast hp_pos.le, ← hϖ,
      Real.rpow_natCast, div_eq_mul_inv, ← inv_pow, Real.rpow_mul hp_pos.le, ← hπ]
    exact mul_le_mul_of_nonneg_left h_det (by positivity)
  refine le_of_mul_le_mul_left ?_ (h_factor.trans_lt' (by positivity))
  calc
    _ ≤ (p : ℝ) ^ (card (P.Φ s) * N ^ 3 * (p.log B + 1) - B / (p - 1) : ℝ) :=
      h_chain.symm.trans_le h_legendre
    _ = p ^ (-varpiValuation P.d p * B - m + -piPrimeValuation P.d p * D : ℝ) *
        p ^ (m - (gammaPrime P.d p * B - piPrimeValuation P.d p * D -
          card (P.Φ s) * N ^ 3 * (p.log B + 1)) : ℝ) := by
      rw [← Real.rpow_add hp_pos, gammaPrime]
      ring_nf
    _ ≤ _ := by gcongr

/-- **The count with charges.** Here `P` fixes the prime `d` of `K = ℚ(√-d)`, `P.Φ s` is the set of
infinite places of the field of level `s`, the instance `PadicPlace p` is an embedding of `ℂ` into
`ℂ_[p]`, and `κ τ h` is the number of columns of height `h` at the place `τ`. Let `p` be non-split,
let `v(ϖ) = ρ_p`, where `ρ_p = varpiValuation P.d p = v(π_p) / (q_p - 1)` for the norm `q_p` of a
prime above `p`, let `F` have the normal form for the exponents `e ∈ I_p°` (odd; all `e` if
`p = d`): `F(ϖ z)` is an integral series times the exponential of `ϖ ^ (p + 1) / p` times a
combination of powers `Γ_e ^ p ^ j` of couplings, with integral coefficients `l`. The filling `i'`
puts a row into each box of `κ` and, with the integral matrices `y_τ`, defines
`P_y = minorProd i' y`: the product over the columns of the minor of `z_τ y_τ` on the rows of the
column and the first `h` columns, `h` being its height. Let `κ°` arise from `κ` by removing the
columns of height one at the places of `marked`. Let charges `p ^ w` be given such that one of
`w τ 1 b` and `w τ' h b` is positive whenever `τ'` is a partner of `τ`, the heights `1` at `τ` and
`h` at `τ'` occur, and either `τ ∈ marked`, or `h = 1` and `τ' ∈ marked`. Then the valuation of the
jet of `F` along `P_y`, plus the sum `fillingCharge w i'` of the exponents over the boxes, is at
least the predicted divisibility of `κ°`, plus `γ_p = gammaPrime P.d p` for each removed box, less
`f N ^ 3 (1 + log_p max (B, 1))`. Here `f` is the number of infinite places, `N` the number of rows
and `B` the number of boxes of `κ` in columns of height below `N`. -/
theorem norm_jet_minorProd_le_of_charges [DecidableEq n'] (hp : chiK P.d p ≠ 1)
    (hϖ : ‖ϖ‖ = p ^ (-varpiValuation P.d p))
    (hF : HasNormalForm (partnerExponents P.d p) (P.partner s p) ϖ l F)
    (marked : Finset (P.Φ s)) (w : P.Φ s → ℕ → n' → ℕ)
    (hw : ∀ e ∈ partnerExponents P.d p, ∀ (τ : P.Φ s) (h : ℕ) (b : n'),
      κ τ 1 ≠ 0 → κ (P.partner s p e τ) h ≠ 0 → τ ∈ marked ∨ h = 1 ∧ P.partner s p e τ ∈ marked →
        w τ 1 b ≠ 0 ∨ w (P.partner s p e τ) h b ≠ 0)
    (i' : WeylIndex n' κ) (y : P.Φ s → n → ℕ → valRingCp p) :
    let N : ℕ := card n'
    let B : ℕ := boxes κ N
    ‖jet ℂ_[p] (minorProd i' fun (τ : P.Φ s) (a : n) (k : ℕ) ↦ (y τ a k : ℂ_[p])) F‖ ≤
      p ^ (fillingCharge w i' -
        (predictedDivisibility P.d p (P.partner s p) (eraseHeightOne κ marked) N +
          gammaPrime P.d p * (B - boxes (eraseHeightOne κ marked) N) -
          card (P.Φ s) * N ^ 3 * (1 + Real.logb p (max B 1 : ℕ))) : ℝ) := by
  intro N B
  -- Heights that do not occur may carry any charge.
  let w' (τ : P.Φ s) (h : ℕ) (b : n') : ℕ := if κ τ h = 0 then 1 else w τ h b
  have hw' (e : ℕ) (he : e ∈ partnerExponents P.d p) :
      IsChargeExponent (P.partner s p e) marked w' := fun τ h b h_exempt ↦ by grind [hw e he τ h b]
  have h_error : (card (P.Φ s) * N ^ 3 * (p.log B + 1) : ℝ) ≤
      card (P.Φ s) * N ^ 3 * (1 + Real.logb p (max B 1 : ℕ)) := by
    grw [Nat.log_mono_right (le_max_left B 1), Real.natLog_le_logb, add_comm]
  refine (P.norm_jet_minorProd_le_of_isChargeExponent s hp hϖ hF marked w' hw' i' y).trans
    (Real.rpow_le_rpow_of_exponent_le (mod_cast Nat.Prime.one_le Fact.out) ?_)
  rw [fillingCharge_congr (w := w') (fun τ h b h_occurs ↦ ite_eq_right h_occurs) i']
  linarith [h_error, mul_sum_deductionTerm_le P.d p (P.partner s p) κ N marked (p.log B)]

/-- **The count.** Here `P` fixes the prime `d` of `K = ℚ(√-d)`, `P.Φ s` is the set of infinite
places of the field of level `s`, and the instance `PadicPlace p` is an embedding of `ℂ` into
`ℂ_[p]`. Let `p` be non-split (`chiK P.d p ≠ 1`), and let `v(ϖ) = ρ_p`, where
`ρ_p = varpiValuation P.d p = v(π_p) / (q_p - 1)` for the norm `q_p` of a prime above `p`. Let `F`
have the normal form (`HasNormalForm`) for the exponents `e ∈ I_p°` (odd; all `e` if `p = d`):
`F(ϖ z)` is an integral series times the exponential of `ϖ ^ (p + 1) / p` times a combination of
powers `Γ_e ^ p ^ j` of couplings, with integral coefficients `l`. The filling `i'` puts a row into
each box of `κ` and, with the integral matrices `y_τ`, defines `P_y = minorProd i' y`, the product
over the columns of the minor of `z_τ y_τ` on the rows of the column and the first `h` columns, `h`
being its height. Then the valuation of the jet `P_y(∂)F(0)` of `F` along `P_y` is at least the
predicted divisibility of `κ`, less `f N ^ 3 (1 + log_p max (B, 1))`. Here `f` is the number of
infinite places, `N` the number of rows and `B` the number of boxes of `κ` in columns of height
below `N`. The predicted divisibility is
`v(π_p) ∑_e ∑_τ ((a_τ / p ^ e - a_τ' - a'_τ')₊ + (l_τ / p ^ e - l_τ')₊ - a'_τ / p ^ e)` over
positive `e ∈ I_p°`, where `τ' = P.partner s p e τ = -p ^ e τ` is the partner
of `τ` and `a`, `a'`, `l` count the columns of height one, the other columns and the boxes in these;
for `p = d` half a term for `e = 0` is subtracted (`predictedDivisibility`). -/
theorem norm_jet_minorProd_le_of_hasNormalForm [DecidableEq n'] (hp : chiK P.d p ≠ 1)
    (hϖ : ‖ϖ‖ = p ^ (-varpiValuation P.d p))
    (hF : HasNormalForm (partnerExponents P.d p) (P.partner s p) ϖ l F)
    (i' : WeylIndex n' κ) (y : P.Φ s → n → ℕ → valRingCp p) :
    let N : ℕ := card n'
    ‖jet ℂ_[p] (minorProd i' fun (τ : P.Φ s) (a : n) (k : ℕ) ↦ (y τ a k : ℂ_[p])) F‖ ≤
      p ^ (-(predictedDivisibility P.d p (P.partner s p) κ N -
        card (P.Φ s) * N ^ 3 * (1 + Real.logb p (max (boxes κ N) 1 : ℕ))) : ℝ) := by
  -- With no marked places and all charges equal to one, no column is removed.
  simpa [eraseHeightOne_empty, fillingCharge_zero] using
    P.norm_jet_minorProd_le_of_charges s hp hϖ hF ∅ 0 (by simp) i' y

end Parameters

/-! ## From entries of the Schur matrix to products of minors -/

section SchurEntries
variable {p : ℕ} [Fact p.Prime] {Φ n n' R : Type} [Fintype Φ] [DecidableEq Φ] [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] [CommRing R] {κ : Φ → ℕ → ℕ}

/-- If polynomials `b t` over the valuation ring of `ℂ_[p]` stay linearly independent over the
residue field, then for all numbers `α t` there is an integral point `y` at which
`∑ α t * b t (y)` has norm at least that of a given `α t₁`. -/
lemma exists_norm_le_norm_sum_mul_eval {ι σ : Type} [Fintype ι]
    {b : ι → MvPolynomial σ (valRingCp p)}
    (hb : LinearIndependent (IsLocalRing.ResidueField (valRingCp p))
      fun t : ι ↦ (b t).map (IsLocalRing.residue (valRingCp p)))
    (α : ι → ℂ_[p]) (t₁ : ι) :
    ∃ y : σ → valRingCp p, ‖α t₁‖ ≤ ‖∑ t : ι, α t * (eval y (b t) : valRingCp p)‖ := by
  have : Nonempty ι := ⟨t₁⟩
  obtain ⟨t₀, h_max⟩ := Finite.exists_max fun t ↦ ‖α t‖
  by_cases h_zero : α t₀ = 0
  · exact ⟨0, (h_max t₁).trans (by simp [h_zero])⟩
  -- Divide by `α t₀` and reduce: the polynomial is not zero, so it has a non-zero value over the
  -- residue field, which is algebraically closed and hence infinite.
  let β (t : ι) : valRingCp p :=
    ⟨α t / α t₀, (norm_div _ _).trans_le (div_le_one_of_le₀ (h_max t) (norm_nonneg _))⟩
  have hβ : β t₀ = 1 := Subtype.ext (div_self h_zero)
  have h_ne : (∑ t, β t • b t).map (IsLocalRing.residue (valRingCp p)) ≠ 0 := fun h_map ↦ by
    simpa [hβ] using Fintype.linearIndependent_iff.1 hb
      (fun t ↦ IsLocalRing.residue (valRingCp p) (β t))
      (by simpa only [map_sum, smul_eq_C_mul, map_mul, map_C] using h_map) t₀
  have : IsAlgClosed (IsLocalRing.ResidueField (valRingCp p)) :=
    ((Variety.IsAbsIntegrallyClosed.of_isIntegrallyClosedIn ℂ_[p]).of_surjective
      IsLocalRing.residue_surjective).isAlgClosed
  obtain ⟨x, hx⟩ : ∃ x : σ → IsLocalRing.ResidueField (valRingCp p),
      eval x ((∑ t, β t • b t).map (IsLocalRing.residue (valRingCp p))) ≠ 0 := by
    contrapose! h_ne
    exact MvPolynomial.funext fun x ↦ by rw [h_ne x, map_zero]
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective.comp_left x
  have h_unit : IsUnit (eval y (∑ t, β t • b t)) := by
    rwa [← IsLocalRing.residue_ne_zero_iff_isUnit, map_eval]
  have h_eq : ∑ t, α t * (eval y (b t) : valRingCp p) =
      α t₀ * (eval y (∑ t, β t • b t) : valRingCp p) := by
    simp [β, mul_sum, smul_eval, ← mul_assoc, mul_div_cancel₀ _ h_zero]
  refine ⟨y, (h_max t₁).trans_eq ?_⟩
  rw [h_eq, norm_mul, isUnit_integer_iff_norm_eq_one.1 h_unit, mul_one]

/-- Expansion of the product of minors `P_y(z) = minorProd i' y`: the entries of row `i'` of the
Schur matrix of the variables `z_τ` are its coefficients in the family `nablaBasis i * detPow`
evaluated at `y`. Here `nablaBasis i` is the product of minors for the filling `i`, and `detPow` is
the product, over the places `τ`, of the determinant of the first `card n` columns of `y_τ`, each to
the power `schurDetExp`: the number `κ τ (card n)` if `card n < card n'`, and zero otherwise. The
hypothesis `FitsRanks` says `card n ≤ card n'` and that `κ` has no column of height strictly between
the two. -/
lemma minorProd_eq_sum (hκ : FitsRanks (fun _ : Φ ↦ n) (fun _ : Φ ↦ n') κ) (i' : WeylIndex n' κ)
    (y : (Σ _ : Φ, n) × ℕ → R) :
    minorProd i' (fun (τ : Φ) (a : n) (k : ℕ) ↦ y (⟨τ, a⟩, k)) =
      ∑ i : WeylIndex n κ, eval y (nablaBasis R (fun _ : Φ ↦ n) κ i *
          detPow R (fun _ : Φ ↦ n) (schurDetExp (fun _ : Φ ↦ n) (fun _ : Φ ↦ n') κ)) •
        schur κ (fun τ : Φ ↦ of fun (b : n') (a : n) ↦ X (τ, b, a)) i' i := by
  -- Evaluate at `y` the defining expansion of the Schur matrix of the variables `z`.
  let z (τ : Φ) : Matrix n' n (MvPolynomial (Φ × n' × n) R) := of fun b a ↦ X (τ, b, a)
  calc
    minorProd i' (fun τ a k ↦ y (⟨τ, a⟩, k))
      = eval (C ∘ y) (rowSubst z (nablaBasis _ (fun _ : Φ ↦ n') κ i')) := by
      simp only [minorProd, nablaBasis, tableauPoly, minor, map_prod, AlgHom.map_det,
        RingHom.map_det]
      congr! 4
      ext b k : 1
      simp [z, rowSubst, smul_eq_C_mul, mul_comm]
    _ = _ := by
      rw [← sum_schur_smul_nablaBasis hκ z i', map_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [smul_eval, ← map_nablaBasis C, ← map_detPow C, ← map_mul, ← map_eval, smul_eq_C_mul,
        mul_comm]

/-- An entry of the Schur matrix `schur κ z` may be replaced by a product of minors. Suppose
`card n ≤ card n'` and that `κ` has no column of height strictly between the two (`FitsRanks`). Take
a power series `F` and standard fillings `i'`, `i`. Let `P` be the polynomial entry of `schur κ z`
at `(i', i)`. Then there are matrices `y_τ` with entries in `valRingCp p` such that
`schurJet κ F i' i = (P(∂) F)(0)` has norm at most that of `(P_y(∂) F)(0)`, where
`P_y = minorProd i' y`. -/
lemma exists_norm_schurJet_le_norm_jet_minorProd
    (hκ : FitsRanks (fun _ : Φ ↦ n) (fun _ : Φ ↦ n') κ)
    (F : MvPowerSeries (Φ × n' × n) ℂ_[p]) (i' : WeylIndex n' κ) (i : WeylIndex n κ) :
    ∃ y : Φ → n → ℕ → valRingCp p,
      ‖schurJet κ F i' i‖ ≤ ‖jet ℂ_[p]
        (minorProd i' fun (τ : Φ) (a : n) (k : ℕ) ↦ (y τ a k : ℂ_[p])) F‖ := by
  let b (t : WeylIndex n κ) : MatrixPoly (Σ _ : Φ, n) (valRingCp p) :=
    nablaBasis (valRingCp p) (fun _ ↦ n) κ t *
      detPow (valRingCp p) (fun _ ↦ n) (schurDetExp (fun _ ↦ n) (fun _ ↦ n') κ)
  have hb : LinearIndependent (IsLocalRing.ResidueField (valRingCp p))
      fun t ↦ (b t).map (IsLocalRing.residue (valRingCp p)) := by
    simpa only [b, map_mul, map_nablaBasis, map_detPow] using
      GL.linearIndependent_nablaBasis_mul_detPow (schurDetExp (fun _ ↦ n) (fun _ ↦ n') κ)
  obtain ⟨y, hy⟩ : ∃ y : (Σ _ : Φ, n) × ℕ → valRingCp p,
      ‖schurJet κ F i' i‖ ≤ ‖∑ t, schurJet κ F i' t * (eval y (b t) : valRingCp p)‖ :=
    exists_norm_le_norm_sum_mul_eval hb (schurJet κ F i') i
  have h_eval (t : WeylIndex n κ) : ((eval y (b t) : valRingCp p) : ℂ_[p]) =
      eval (fun x ↦ (y x : ℂ_[p])) ((b t).map (valRingCp p).subtype) :=
    map_eval (valRingCp p).subtype y (b t)
  have h_entry (t : WeylIndex n κ) : schurJet κ F i' t =
      jet ℂ_[p] (schur κ (fun τ : Φ ↦ of fun (r : n') (a : n) ↦ X (τ, r, a)) i' t) F := rfl
  refine ⟨fun τ a k ↦ y (⟨τ, a⟩, k), hy.trans_eq ?_⟩
  rw [minorProd_eq_sum hκ i' fun x ↦ (y x : ℂ_[p]), map_sum, LinearMap.sum_apply]
  refine congrArg norm (sum_congr rfl fun t _ ↦ ?_)
  rw [LinearMap.map_smul₂, smul_eq_mul, mul_comm, h_entry, h_eval, map_mul, map_nablaBasis,
    map_detPow]

end SchurEntries

end New
