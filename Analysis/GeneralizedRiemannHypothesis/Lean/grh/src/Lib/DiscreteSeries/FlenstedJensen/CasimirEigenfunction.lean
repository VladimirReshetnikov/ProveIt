import Lib.DiscreteSeries.FlenstedJensen.FlagDensities

/-!
# Flensted-Jensen's integral, analyticity of c_λ and its Casimir eigenvalue

This file studies the coefficient c_λ = `New.HCParam.dsCoeff l`, with `l = 2λ`, on the group
`U(diag ε)`, where `K = U(diag ε) ∩ U(n)`. It proves that c_λ is complex analytic, so defines a
smooth function `New.HCParam.dsCoeffSmooth` in `New.SmoothU`. For a parameter with a gap
(`New.HCParam.HasGap`, assumed in all results listed below), Flensted-Jensen's integral over `K`,
which gives c_λ, does not depend on the admissible block diagonal factor, and c_λ is an
eigenfunction of the Casimir operator of `gl_n`.

## Main definitions and results

* `New.flenstedJensen_eq_of_accretive`, `New.dsCoeff_eq_flenstedJensen`: any block diagonal `a` with
  `a⁻¹ g` accretive (`Matrix.IsAccretive`: `z + zᴴ` positive definite) gives the same value. The
  integrand is a density on the flag variety of `K_ℂ`; polarization makes the integral locally
  constant, and the admissible `a` form a convex set.
* `New.flenstedJensen_eq_integral_of_eq_mul_mul_conjTranspose`,
  `New.dsCoeff_eq_integral_of_eq_mul_mul_conjTranspose`: the value as an integral over `K` for any
  splitting `g = p z qᴴ` with `p`, `q` block diagonal and `z` accretive.
* `New.DiscreteSeries.splitCoeff_triangular_mul_mul_triangular`,
  `New.DiscreteSeries.flenstedJensen_triangular_mul_mul_triangular`: block diagonal triangular
  factors, lower on the left and upper on the right, come out as characters.
* `New.casimir_dsCoeffSmooth`: the function c_λ (`New.HCParam.dsCoeffSmooth`, l = 2λ) on U(diag ε)
  is an eigenfunction of the Casimir operator Σ_{a,b} E_ab E_ba of gl_n, acting by right derivatives
  (`New.rightDeriv`), with eigenvalue `New.HCParam.casimirValue` l = |λ|² − |ρ|². Near a point c_λ
  is an average over k in K = `New.maxCompactU` of functions that are lowest weight vectors of
  weight λ + ρ (highest vectors for the roots positive for −l) in the basis k E_ab k⁻¹ of gl_n, and
  the Casimir operator does not depend on the basis.

Notions from other files:
* `New.USign`: For a vector of signs ε, the unitary group U(J) of the diagonal matrix J=diag(ε).
* `New.SmoothU`: Smooth functions on `U(diag ε)`: the restrictions of the smooth functions on all
  matrices.
* `New.HCParam.HasGap`: the entries of `l = 2λ` are distinct, of the parity of `card n - 1`, and
  those with different signs differ by at least `2h`.
* `New.blockDiagAlg ε`: the matrices that commute with `diag ε`, the block diagonal matrices.

## Relation to the literature

Known; see `Lib.DiscreteSeries.FlenstedJensen.PsiKTypes` for sources.
-/

/-!
## Flensted-Jensen's integral and analyticity of the coefficient

Flensted-Jensen's integral `New.HCParam.flenstedJensen l a z` is the integral over
`K = U(diag ε) ∩ U(n)` of `m_Λ(a k) * conj m_Λ(k) / m_{-λ-ρ}(kᴴ z k)`, normalised by `∫ |m_Λ|²`,
where `m_w = New.weightMinors w` is a product of principal minors, `Λ = New.HCParam.lowestKType l`
and `λ + ρ = New.paramAddRho l`. The function `New.HCParam.dsCoeff l g` is its value at
`(a, a⁻¹ g)` with `a = New.blockDiagPart ε g` the block diagonal part of `g`.

For a parameter of some gap the value is the same for every block diagonal `a` with `a⁻¹ g`
accretive: these `a` form a convex set, so it is enough that the derivative in `a` vanishes. Up to
the normalising constant the integral is `I(a, 1)`, where `I = New.HCParam.splittingIntegral l g` is
analytic at each pair `(p, r)` with `r g⁻¹ p` accretive. For a parameter of some gap the integrand
of `I` is a density for the triangular subgroup of `K_ℂ`, so `I(p x, xᴴ r) = I(p, r)` for invertible
block diagonal `x`. Polarization of this invariance shows that the derivative of `I` in `p` vanishes
in the block diagonal directions.
-/

namespace New

open Matrix MeasureTheory Finset ComplexConjugate ComplexOrder DiscreteSeries Norms.L2Operator
  ContinuousMap

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {l : HCParam ε}

omit [DecidableEq n] in
/-- For an integer vector `l`, the sum `2ρ = twoRho l ⊤` of all roots that are positive for `l` has
its entries in the strict order of those of `l`. -/
theorem twoRho_lt_twoRho {l : n → ℤ} {a b : n} (hab : l a < l b) : twoRho l ⊤ a < twoRho l ⊤ b := by
  -- both sides are sums of signs of differences of entries of `l`; compare them term by term
  have h_sum (i : n) : twoRho l ⊤ i =
      ∑ j : n, ((if l j < l i then 1 else 0) - (if l i < l j then 1 else 0)) := by
    simp [twoRho, ← sum_boole, sum_sub_distrib]
  rw [h_sum, h_sum]
  exact sum_lt_sum (fun j _ ↦ by split_ifs <;> lia) ⟨a, mem_univ a, by split_ifs <;> lia⟩

@[fun_prop]
theorem DiscreteSeries.analyticAt_matrix_inv {s : Matrix n n ℂ} (hs : s.det ≠ 0) :
    AnalyticAt ℂ (·⁻¹) s := by
  obtain ⟨u, rfl⟩ : IsUnit s := (isUnit_iff_isUnit_det s).2 hs.isUnit
  simpa only [funext nonsing_inv_eq_ringInverse] using analyticAt_inverse (𝕜 := ℂ) u

/-- The derivative of an equivariant function in an elementary direction. Let `f` have derivative
`D` at `s`. Suppose that `f (c b) = diagChar w b * f s`, with `diagChar w b = ∏ a, b a a ^ w a`,
whenever `c b` is near `s` and `b` is block diagonal, invertible and triangular for the order
`-o`. Suppose also that `c` maps the line `1 + t • single i j 1`, where `ε i = ε j` and
`o j ≤ o i`, to the line `s + t • v`. Then `D v` is `w i * f s` if `i = j`, and `0` otherwise. -/
theorem fderiv_eq_of_borel_equivariant (ε : n → ℤˣ) {s v : Matrix n n ℂ} {f : Matrix n n ℂ → ℂ}
    {o w : n → ℤ} {D : Matrix n n ℂ →L[ℂ] ℂ} {i j : n} (hf : HasFDerivAt f D s) (h_le : o j ≤ o i)
    (h_sign : ε i = ε j) (c : Matrix n n ℂ → Matrix n n ℂ)
    (h_equivariant : ∀ᶠ x : Matrix n n ℂ in nhds s, ∀ b ∈ blockDiagAlg ε,
      IsBorelMatrix (-o) b → x = c b → f x = diagChar w b * f s)
    (h_direction : ∀ t : ℂ, s + t • v = c (1 + t • single i j 1)) :
    D v = (if i = j then (w i : ℂ) else 0) * f s := by
  -- For small `t` the matrix `b t = 1 + t • single i j 1` is invertible and triangular, so along
  -- the line `s + t • v` the function is `∏ a, b t a a ^ w a * f s`. Differentiate at `t = 0`.
  let Y : Matrix n n ℂ := single i j 1
  have h_factor (a : n) : HasDerivAt (fun t : ℂ ↦ (1 + t * Y a a) ^ w a) (w a * Y a a) 0 := by
    simpa [Function.comp_def] using
      (hasDerivAt_zpow (w a) _ (by simp)).comp 0 ((hasDerivAt_mul_const (Y a a)).const_add 1)
  have h_prod : HasDerivAt (fun t : ℂ ↦ ∏ a, (1 + t * Y a a) ^ w a)
      (if i = j then (w i : ℂ) else 0) 0 := by
    simpa [Y, single, ite_and, comm] using
      HasDerivAt.fun_finsetProd (u := univ) fun a _ ↦ h_factor a
  have h_det : ∀ᶠ t : ℂ in nhds 0, (1 + t • Y).det ≠ 0 :=
    ContinuousAt.eventually_ne (by fun_prop) (by simp)
  refine (hf.hasLineDerivAt v).unique ((h_prod.mul_const (f s)).congr_of_eventuallyEq ?_)
  have h_line : Filter.Tendsto (fun t : ℂ ↦ s + t • v) (nhds 0) (nhds s) :=
    Continuous.tendsto' (by fun_prop) 0 s (by simp)
  filter_upwards [h_line.eventually h_equivariant, h_det] with t ht ht_det
  have h_entry (a b : n) : (1 + t • Y) a b = (if a = b then 1 else 0) +
      (if i = a ∧ j = b then t else 0) := by simp [Y, single, Matrix.one_apply]
  have h_mem : 1 + t • Y ∈ blockDiagAlg ε := mem_blockDiagAlg.2 fun a b hab ↦ by grind
  have h_tri : (1 + t • Y).BlockTriangular (-o) := fun a b (hab : -o b < -o a) ↦ by grind
  simpa [diagChar] using ht (1 + t • Y) h_mem ⟨h_tri, ht_det⟩ (h_direction t)

/-! ### Analyticity of the coefficient -/

/-- Let `a` be analytic at the matrix `g` with `(a g)⁻¹ g` accretive (positive definite Hermitian
part). Then the integrand of `New.HCParam.flenstedJensen l (a x) ((a x)⁻¹ * x)`, made of the
products of principal minors `weightMinors` of weights `Λ = l.lowestKType` and `-(λ + ρ)`, is an
analytic family in `x` near `g`: it is given by an analytic function with values in `C(K, ℂ)`,
`K = maxCompactU ε` being the compact group `U(diag ε) ∩ U(n)`. -/
theorem isAnalyticFamily_flenstedJensen (l : HCParam ε) {g : Matrix n n ℂ}
    {a : Matrix n n ℂ → Matrix n n ℂ} (ha : AnalyticAt ℂ a g)
    (h_acc : ((a g)⁻¹ * g).IsAccretive) :
    IsAnalyticFamily
      (fun (x : Matrix n n ℂ) (k : maxCompactU ε) ↦
        weightMinors l.lowestKType (a x * k) * conj (weightMinors l.lowestKType k) /
          weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * ((a x)⁻¹ * x) * k))
      g := by
  obtain ⟨ha_det, -⟩ : (a g).det ≠ 0 ∧ g.det ≠ 0 := by simpa using h_acc.det_ne_zero
  -- The integrand is an analytic function `Θ` of `x` and the pair `(k, kᴴ)`.
  let Θ : Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ → ℂ := fun (x, y, z) ↦
    weightMinors l.lowestKType (a x * y) * weightMinors l.lowestKType z /
      weightMinors (-paramAddRho l) (z * ((a x)⁻¹ * x) * y)
  simp only [conj_weightMinors]
  refine IsAnalyticFamily.of_analyticAt (by fun_prop) Θ
    (ι := fun k : maxCompactU ε ↦ ((k : Matrix n n ℂ), (k : Matrix n n ℂ)ᴴ)) fun k ↦ ?_
  have hz : ((k : Matrix n n ℂ)ᴴ * ((a g)⁻¹ * g) * k).IsAccretive :=
    h_acc.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)
  -- The side conditions of `fun_prop` are the nonvanishing of minors and determinants; `det_mul`
  -- is applied only where it does not hide the product in `hz`.
  fun_prop (disch := simp [ha_det, hz, hz.det_ne_zero, -det_mul, det_mul (a g),
    GeneralLinearGroup.det_ne_zero])

/-- For all signs ε and integer vectors l = 2λ, the function c_λ = `l.dsCoeff`, Flensted-Jensen's
integral with the block diagonal part of the matrix as factor, is complex analytic at every point
g of U(diag ε). -/
theorem HCParam.analyticAt_dsCoeff (g : USign ε) : AnalyticAt ℂ l.dsCoeff g := by
  -- Differentiate under the integral sign, with the block diagonal part as the analytic factor.
  unfold HCParam.dsCoeff HCParam.flenstedJensen
  exact ((isAnalyticFamily_flenstedJensen l (a := fun x ↦ blockDiagPart ε x) (by fun_prop)
    (isAccretive_blockDiagPart_inv_mul g).2).analyticAt_integral (haarK ε)).div_const

-- `grind` may use that `2ρ` is ordered as `l` wherever two entries of `λ + ρ` occur.
grind_pattern twoRho_lt_twoRho => paramAddRho l a, paramAddRho l b

/-! ### Dominance of the weights -/

section

omit [DecidableEq n]

/-- For a parameter `l = 2λ` of gap `h`, the entries of `λ + ρ = paramAddRho l`, with ρ the half sum
of the roots positive for `l`, are ordered as those of `l`. -/
theorem HCParam.HasGap.paramAddRho_lt_iff {h : ℕ} (hl : l.HasGap h) {i j : n} :
    paramAddRho l i < paramAddRho l j ↔ l i < l j := by
  grind [paramAddRho, HasGap]

/-- For a parameter `l = 2λ` of gap `h`, the weight `-(λ + ρ)` is dominant for the order `l` with
all signs equal: its entries decrease as those of `l` increase. -/
theorem HCParam.HasGap.isKDominant_neg_paramAddRho {h : ℕ} (hl : l.HasGap h) :
    IsKDominant 1 l (-paramAddRho l) := by
  simp_all [IsKDominant, hl.paramAddRho_lt_iff, le_of_lt]

/-- For a parameter l = 2λ of gap h, the weight Λ = λ+ρ−2ρ_c, with 2ρ_c the sum of the roots
e_i − e_j with ε_i = ε_j that are positive for l, is K-dominant for the order −l: Λ_j ≤ Λ_i whenever
ε_i = ε_j and l_j < l_i. -/
theorem HCParam.HasGap.isKDominant_lowestKType {h : ℕ} (hl : l.HasGap h) :
    IsKDominant ε (-l) l.lowestKType := by
  intro i j h_sign (h_lt : -l i < -l j)
  -- The entries of `l` are distinct and of one parity, so the numbers `l a` and `l a - 1` are all
  -- distinct, and at most `l i - l j` of them lie in `Ico (l j) (l i)`.
  let s : Finset (n × Fin 2) := {x | l x.1 - x.2 ∈ Ico (l j) (l i)}
  have h_card : #s ≤ #(Ico (l j) (l i)) :=
    card_le_card_of_injOn (fun x ↦ l x.1 - x.2) (by grind [Set.MapsTo]) fun _ ↦ by grind [HasGap]
  have h_count : (#s : ℤ) = ∑ a : n,
      ((if l j ≤ l a ∧ l a < l i then 1 else 0) + (if l j < l a ∧ l a ≤ l i then 1 else 0)) := by
    simp [s, ← sum_boole, Fintype.sum_prod_type]
  have h_value (m : n) : 2 * l.lowestKType m - l m =
      twoRho l (fun a b ↦ ε a ≠ ε b) m - twoRho l (fun a b ↦ ε a = ε b) m := by
    linarith [two_mul_lowestKType hl m]
  -- `2 * l.lowestKType - l` is a difference of `twoRho` terms. To its value at `j` less its value
  -- at `i`, each index `a` contributes at most the number of `l a`, `l a - 1` in that interval.
  have h_diff : 2 * l.lowestKType j - l j - (2 * l.lowestKType i - l i) ≤ #s := by
    simp only [h_value, twoRho, h_count, ← sum_boole, h_sign, ← sum_sub_distrib]
    refine sum_le_sum fun a _ ↦ ?_
    lia
  grind [Int.card_Ico]

end

/-! ### The splitting integral -/

/-- The function `F(y) = m_Λ(p y) · conj m_Λ(q y) / m_{λ+ρ}(yᴴ qᴴ g⁻¹ p y)`, written in `r = qᴴ`
so that it depends holomorphically on the pair `(p, r)`. Here `l = 2λ`, `Λ = l.lowestKType` and
`m_w = weightMinors w` is the product of principal minors of weight `w`. -/
noncomputable def HCParam.splittingIntegrand (l : HCParam ε) (g p r y : Matrix n n ℂ) : ℂ :=
  weightMinors l.lowestKType (p * y) * weightMinors l.lowestKType (yᴴ * r) /
    weightMinors (paramAddRho l) (yᴴ * (r * g⁻¹ * p) * y)

/-- The integral `I(p, r)` of `splittingIntegrand` over `K = U(diag ε) ∩ U(n)` for its Haar measure
`haarK ε` of mass one, as a function of the pair `(p, r)`, where `r` stands for `qᴴ`. -/
noncomputable def HCParam.splittingIntegral (l : HCParam ε) (g : Matrix n n ℂ)
    (pr : Matrix n n ℂ × Matrix n n ℂ) : ℂ :=
  ∫ k : maxCompactU ε, l.splittingIntegrand g pr.1 pr.2 (k : Matrix n n ℂ) ∂haarK ε

/-- For a matrix `a` with `a⁻¹ g` accretive, Flensted-Jensen's normalised integral at `(a, a⁻¹ g)`
is the integral `I(a, 1) = l.splittingIntegral g (a, 1)` divided by
`Λ.kTypeNormSq = ∫_K |m_Λ|²`, where `Λ = l.lowestKType`. -/
theorem flenstedJensen_eq_splittingIntegral {g a : Matrix n n ℂ} (ha_acc : (a⁻¹ * g).IsAccretive) :
    l.flenstedJensen a (a⁻¹ * g) = l.splittingIntegral g (a, 1) / l.lowestKType.kTypeNormSq := by
  obtain ⟨ha_det, -⟩ : a.det ≠ 0 ∧ g.det ≠ 0 := by simpa using ha_acc.det_ne_zero
  have h_inv (k : maxCompactU ε) :
      ((k : Matrix n n ℂ)ᴴ * (a⁻¹ * g) * k)⁻¹ = (k : Matrix n n ℂ)ᴴ * (1 * g⁻¹ * a) * k := by
    simp [← maxCompactU.coe_inv, Matrix.mul_inv_rev, ha_det, mul_assoc]
  simp only [flenstedJensen, HCParam.splittingIntegral, HCParam.splittingIntegrand,
    weightMinors_neg (ha_acc.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)).det_ne_zero,
    h_inv, conj_weightMinors, mul_one]

lemma DiscreteSeries.conjTranspose_mem_blockDiagAlg {X : Matrix n n ℂ} (hX : X ∈ blockDiagAlg ε) :
    Xᴴ ∈ blockDiagAlg ε :=
  mem_blockDiagAlg.2 fun i j hij ↦ by simp [mem_blockDiagAlg.1 hX j i hij.symm]

/-- The adjoint of an invertible matrix that is lower triangular for the order `o` is invertible
and upper triangular for `o`. -/
lemma DiscreteSeries.isBorelMatrix_conjTranspose {o : n → ℤ} {X : Matrix n n ℂ}
    (hX : IsBorelMatrix (-o) X) : IsBorelMatrix o Xᴴ :=
  ⟨fun i j hij ↦ by simp [hX.left (neg_lt_neg hij)], by simpa using hX.right⟩

/-- Let `l = 2λ` be a parameter of some gap `h` (distinct entries congruent to `card n - 1` mod 2).
Let `F = l.splittingIntegrand g p r` be the function
`F(y) = m_Λ(p y) · conj m_Λ(q y) / m_{λ+ρ}(yᴴ qᴴ g⁻¹ p y)`,
written with `r = qᴴ`, where `Λ = l.lowestKType` and `m_w` is the product of principal
minors of weight `w`. If `r g⁻¹ p` is accretive and `y` is invertible, then
`F(y b) = |b^(-2ρ_c)|² F(y)` for every invertible block diagonal `b` (commuting with diag ε) that is
upper triangular in the order of decreasing `l`, so `F` is a density. Here `2ρ_c` is the sum of the
compact positive roots (the roots e_i − e_j with `ε i = ε j` that are positive for `l`), and
`b^w = diagChar w b` is ∏ b_ii^(w_i). -/
theorem splittingIntegrand_mul_borel {h : ℕ} (hl : l.HasGap h) {g p r y b : Matrix n n ℂ}
    (h_acc : (r * g⁻¹ * p).IsAccretive) (hy : y.det ≠ 0)
    (hb_mem : b ∈ blockDiagAlg ε) (hb : IsBorelMatrix (-l) b) :
    l.splittingIntegrand g p r (y * b) =
      ‖diagChar (-twoRho l fun i j : n ↦ ε i = ε j) b‖ ^ 2 * l.splittingIntegrand g p r y := by
  -- Each of the three products of minors in `F` is multiplied by a character of `b` (or `bᴴ`).
  have h_inj : (-l).Injective := hl.neg.injective
  have h_low : IsKDominant ε (-l) l.lowestKType := hl.isKDominant_lowestKType
  have h_rho : IsKDominant ε (-l) (paramAddRho l) :=
    fun i j _ hij ↦ (hl.paramAddRho_lt_iff.2 (neg_lt_neg_iff.1 hij)).le
  obtain ⟨⟨hr, -⟩, hp⟩ : (r.det ≠ 0 ∧ g.det ≠ 0) ∧ p.det ≠ 0 := by simpa using h_acc.det_ne_zero
  have hz : (yᴴ * (r * g⁻¹ * p) * y).det ≠ 0 := (h_acc.conjTranspose_mul_mul hy).det_ne_zero
  have hzb : (yᴴ * (r * g⁻¹ * p) * y * b).det ≠ 0 :=
    (det_mul _ b).trans_ne (mul_ne_zero hz hb.right)
  have hb'_mem : bᴴ ∈ blockDiagAlg ε := conjTranspose_mem_blockDiagAlg hb_mem
  have hb_adj : IsBorelMatrix (- -l) bᴴ := isBorelMatrix_conjTranspose (by rwa [neg_neg])
  have h_adj (w : n → ℤ) : diagChar w bᴴ = conj (diagChar w b) := by simp [diagChar]
  -- The rule `m_w(b' z b) = b'^w b^w m_w(z)` for `b'` lower and `b` upper triangular, applied to
  -- each of the three factors.
  have h_p_factor : weightMinors l.lowestKType (p * (y * b)) =
      weightMinors l.lowestKType (p * y) * diagChar l.lowestKType b := by
    rw [← mul_assoc, h_low.weightMinors_mul_borel h_inj (by simp [hp, hy]) hb_mem hb]
  have h_r_factor : weightMinors l.lowestKType ((y * b)ᴴ * r) =
      conj (diagChar l.lowestKType b) * weightMinors l.lowestKType (yᴴ * r) := by
    rw [conjTranspose_mul, mul_assoc,
      h_low.weightMinors_oppBorel_mul h_inj (by simp [hr, hy]) hb'_mem hb_adj, h_adj]
  have h_denom : weightMinors (paramAddRho l) ((y * b)ᴴ * (r * g⁻¹ * p) * (y * b)) =
      conj (diagChar (paramAddRho l) b) * (weightMinors (paramAddRho l) (yᴴ * (r * g⁻¹ * p) * y) *
        diagChar (paramAddRho l) b) := by
    rw [← h_rho.weightMinors_mul_borel h_inj hz hb_mem hb, ← h_adj,
      ← h_rho.weightMinors_oppBorel_mul h_inj hzb hb'_mem hb_adj]
    simp only [conjTranspose_mul, mul_assoc]
  -- The characters combine because `Λ = (λ + ρ) - 2 ρ_c` with `λ + ρ = paramAddRho l`.
  have h_char : diagChar l.lowestKType b =
      diagChar (paramAddRho l) b * diagChar (-twoRho l fun i j ↦ ε i = ε j) b := by
    simp [lowestKType, zpow_sub₀, hb.diag_ne_zero h_inj, div_eq_mul_inv, prod_mul_distrib, diagChar]
  have h_ne : diagChar (paramAddRho l) b ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ ↦ zpow_ne_zero _ (hb.diag_ne_zero h_inj i)
  simp only [HCParam.splittingIntegrand, h_p_factor, h_r_factor, h_denom, h_char, map_mul,
    ← Complex.mul_conj']
  field_simp [h_ne, (map_ne_zero conj).2 h_ne]

/-- Invariance: for a parameter `l` of gap `h`, a matrix `r g⁻¹ p` that is accretive and an
invertible block diagonal `x`, one has `I(p x, xᴴ r) = I(p, r)`, where
`I = l.splittingIntegral g` and a matrix `z` is accretive if `z + zᴴ` is positive definite. -/
theorem splittingIntegral_mul_conjTranspose_mul {h : ℕ} (hl : l.HasGap h) {g p r x : Matrix n n ℂ}
    (h_acc : (r * g⁻¹ * p).IsAccretive) (hx_mem : x ∈ blockDiagAlg ε) (hx_det : x.det ≠ 0) :
    l.splittingIntegral g (p * x, xᴴ * r) = l.splittingIntegral g (p, r) := by
  obtain ⟨⟨hr, -⟩, hp⟩ : (r.det ≠ 0 ∧ g.det ≠ 0) ∧ p.det ≠ 0 := by simpa using h_acc.det_ne_zero
  have h_cont : ContinuousOn (l.splittingIntegrand g p r) {y | y ∈ blockDiagAlg ε ∧ y.det ≠ 0} := by
    rintro y ⟨-, hy⟩
    have hz : (yᴴ * (r * g⁻¹ * p) * y).IsAccretive := h_acc.conjTranspose_mul_mul hy
    have h_minors (w : n → ℤ) {u : Matrix n n ℂ → Matrix n n ℂ} (hu : Continuous u)
        (hu_det : (u y).det ≠ 0) : ContinuousAt (fun y ↦ weightMinors w (u y)) y :=
      (analyticAt_weightMinors hu_det).continuousAt.comp hu.continuousAt
    exact ContinuousAt.continuousWithinAt (.div
      (.mul (h_minors _ (u := (p * ·)) (by fun_prop) (by simp [hp, hy]))
        (h_minors _ (u := (·ᴴ * r)) (by fun_prop) (by simp [hr, hy])))
      (h_minors _ (by fun_prop) hz.det_ne_zero) (hz.weightMinors_ne_zero _))
  -- Replacing `(p, r)` by `(p x, xᴴ r)` replaces `F(y)` by `F(x y)`.
  have h_shift (y : Matrix n n ℂ) :
      l.splittingIntegrand g (p * x) (xᴴ * r) y = l.splittingIntegrand g p r (x * y) := by
    simp only [HCParam.splittingIntegrand, conjTranspose_mul, mul_assoc]
  simpa only [HCParam.splittingIntegral, h_shift] using
    integral_haarK_mul_left_of_density hl.injective h_cont
      (fun y _ hy b hb_mem hb ↦ splittingIntegrand_mul_borel hl h_acc hy hb_mem hb) hx_mem hx_det

/-- The integral `I = HCParam.splittingIntegral l g` over `K` is complex analytic at each pair
`(p, r)` for which `r g⁻¹ p` is accretive. -/
theorem analyticAt_splittingIntegral {l : HCParam ε} {g p r : Matrix n n ℂ}
    (h_acc : (r * g⁻¹ * p).IsAccretive) :
    AnalyticAt ℂ (l.splittingIntegral g) (p, r) := by
  obtain ⟨⟨hr, -⟩, hp⟩ : (r.det ≠ 0 ∧ g.det ≠ 0) ∧ p.det ≠ 0 := by simpa using h_acc.det_ne_zero
  -- The integrand is an analytic function `Θ` of `(p, r)` and the pair `(k, kᴴ)`.
  let Θ : (Matrix n n ℂ × Matrix n n ℂ) × Matrix n n ℂ × Matrix n n ℂ → ℂ := fun ((p, r), y, z) ↦
    weightMinors l.lowestKType (p * y) * weightMinors l.lowestKType (z * r) /
      weightMinors (paramAddRho l) (z * (r * g⁻¹ * p) * y)
  refine (IsAnalyticFamily.of_analyticAt (by fun_prop) Θ
    (ι := fun k : maxCompactU ε ↦ ((k : Matrix n n ℂ), (k : Matrix n n ℂ)ᴴ))
    fun k ↦ ?_).analyticAt_integral _
  have hz : ((k : Matrix n n ℂ)ᴴ * (r * g⁻¹ * p) * k).IsAccretive :=
    h_acc.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)
  -- The side conditions of `fun_prop` are the nonvanishing of minors and determinants; `det_mul`
  -- is applied only where it does not hide the product in `hz`.
  fun_prop (disch := simp [hp, hr, hz, hz.det_ne_zero, -det_mul, det_mul p, det_mul _ r,
    GeneralLinearGroup.det_ne_zero])

/-- Polarization: a complex linear form on pairs that vanishes at `(p Y, Yᴴ)` for all `Y` in a
complex subspace vanishes at `(p X, 0)` for each `X` in it, since `Y ↦ Yᴴ` is antilinear. -/
theorem apply_mul_zero_eq_zero_of_polarization {D : Matrix n n ℂ × Matrix n n ℂ →L[ℂ] ℂ}
    {S : Submodule ℂ (Matrix n n ℂ)} {p X : Matrix n n ℂ}
    (hD : ∀ Y ∈ S, D (p * Y, Yᴴ) = 0) (hX : X ∈ S) : D (p * X, 0) = 0 := by
  have h_sum : D (p * X, 0) + D (0, Xᴴ) = 0 := by simpa [← map_add] using hD X hX
  have h_pair : ((p * (Complex.I • X), (Complex.I • X)ᴴ) : Matrix n n ℂ × Matrix n n ℂ) =
      Complex.I • ((p * X, 0) - (0, Xᴴ)) := by simp
  have h_diff : D (p * X, 0) - D (0, Xᴴ) = 0 := by
    rw [← smul_eq_zero_iff_right Complex.I_ne_zero, ← map_sub, ← map_smul, ← h_pair]
    exact hD _ (S.smul_mem Complex.I hX)
  linear_combination (h_sum + h_diff) / 2

/-- Let `l` have gap `h`, let `p` be block diagonal for the signs and let `g⁻¹ p` be accretive.
Then the derivative at `(p, 1)` of `I = HCParam.splittingIntegral l g` vanishes at `(X, 0)` for
each block diagonal `X`. -/
theorem fderiv_splittingIntegral_eq_zero {l : HCParam ε} {h : ℕ} (hl : l.HasGap h)
    {g p X : Matrix n n ℂ} (hp : p ∈ blockDiagAlg ε) (h_acc : (g⁻¹ * p).IsAccretive)
    (hX : X ∈ blockDiagAlg ε) :
    fderiv ℂ (l.splittingIntegral g) (p, 1) (X, 0) = 0 := by
  have h_acc' : (1 * g⁻¹ * p).IsAccretive := by rwa [one_mul]
  have h_diff : DifferentiableAt ℂ (l.splittingIntegral g) (p, 1) :=
    (analyticAt_splittingIntegral h_acc').differentiableAt
  -- By invariance `I` is constant along `t ↦ (p x, xᴴ)`, `x = 1 + t Y`, for small real `t`.
  have h_real (Y : Matrix n n ℂ) (hY : Y ∈ (blockDiagAlg ε).toSubmodule) :
      fderiv ℂ (l.splittingIntegral g) (p, 1) (p * Y, Yᴴ) = 0 := by
    refine ((h_diff.hasFDerivAt.restrictScalars ℝ).hasLineDerivAt (p * Y, Yᴴ)).unique
      ((hasDerivAt_const 0 (l.splittingIntegral g (p, 1))).congr_of_eventuallyEq ?_)
    have h_det : ∀ᶠ t : ℝ in nhds 0, (1 + t • Y).det ≠ 0 :=
      ContinuousAt.eventually_ne (by fun_prop) (by simp)
    filter_upwards [h_det] with t ht
    simpa [mul_add, star_trivial] using splittingIntegral_mul_conjTranspose_mul hl h_acc'
      (add_mem (one_mem _) ((blockDiagAlg ε).smul_mem hY (t : ℂ)) : 1 + t • Y ∈ blockDiagAlg ε) ht
  simpa [h_acc.det_ne_zero_and_inv_mul.1] using apply_mul_zero_eq_zero_of_polarization h_real
    (mul_mem (blockDiagAlg.inv_mem hp) hX : p⁻¹ * X ∈ blockDiagAlg ε)

/-! ### Independence of the splitting -/

/-- Independence of the splitting: let `l = 2λ` have gap `h` (distinct entries ≡ `card n - 1` mod 2,
`|λ i - λ j| ≥ h` when `ε i ≠ ε j`) and let `g` be any complex matrix. Then Flensted-Jensen's
integral `l.flenstedJensen a z = ∫_K m_Λ(ak) conj(m_Λ(k)) / m_{−λ−ρ}(kᴴzk) dk / ∫_K |m_Λ|²` at
`z = a⁻¹ g` is the same for all `a` commuting with `diag ε` with `a⁻¹ g` accretive (`z + zᴴ`
positive definite). -/
theorem flenstedJensen_eq_of_accretive {l : HCParam ε} {h : ℕ} (hl : l.HasGap h)
    {g a b : Matrix n n ℂ} (ha : a ∈ blockDiagAlg ε) (ha_acc : (a⁻¹ * g).IsAccretive)
    (hb : b ∈ blockDiagAlg ε) (hb_acc : (b⁻¹ * g).IsAccretive) :
    l.flenstedJensen b (b⁻¹ * g) = l.flenstedJensen a (a⁻¹ * g) := by
  -- The `p` that commute with the signs and make `g⁻¹ p` accretive form a convex set, and
  -- `p ↦ I(p, 1)` has derivative zero along it; so it is constant on the segment from `a` to `b`.
  have h_convex : Convex ℝ {p : Matrix n n ℂ | (g⁻¹ * p).IsAccretive} :=
    convex_iff_forall_pos.2 fun x hx y hy s t hs ht _ ↦ by
      simpa [IsAccretive, mul_add, add_mul, add_add_add_comm, star_trivial] using
        (hx.smul hs).add (hy.smul ht)
  have h_deriv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ l.splittingIntegral g (a + t • (b - a), 1)) 0 t := by
    have h_mem : a + t • (b - a) ∈ blockDiagAlg ε :=
      add_mem ha ((blockDiagAlg ε).smul_mem (sub_mem hb ha) (t : ℂ))
    have h_acc : (g⁻¹ * (a + t • (b - a))).IsAccretive := h_convex.add_smul_sub_mem
      ha_acc.det_ne_zero_and_inv_mul.2 hb_acc.det_ne_zero_and_inv_mul.2 ht
    have h_line : HasDerivAt (fun t : ℝ ↦ (a + t • (b - a), (1 : Matrix n n ℂ))) (b - a, 0) t := by
      simpa using (((hasDerivAt_id t).smul_const (b - a)).const_add a).prodMk (hasDerivAt_const t 1)
    have h_diff : DifferentiableAt ℂ (l.splittingIntegral g) (a + t • (b - a), 1) :=
      (analyticAt_splittingIntegral (by rwa [one_mul])).differentiableAt
    exact ((h_diff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t h_line).congr_deriv
      (fderiv_splittingIntegral_eq_zero hl h_mem h_acc (sub_mem hb ha))
  have h_const : l.splittingIntegral g (b, 1) = l.splittingIntegral g (a, 1) := by
    simpa using constant_of_has_deriv_right_zero (HasDerivAt.continuousOn h_deriv)
      (fun t ht ↦ (h_deriv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 (by simp)
  simp [flenstedJensen_eq_splittingIntegral, ha_acc, hb_acc, h_const]

/-- Let `l = 2λ` be a parameter of some gap `m` (distinct entries of one parity, those of `λ` at
opposite signs at least `m` apart) and `g` in `U(diag ε)`. Then c_λ(g) = `l.dsCoeff g` is
Flensted-Jensen's integral at `(a, a⁻¹ g)` for any block diagonal `a` such that `a⁻¹ g` is
accretive (positive definite Hermitian part). -/
theorem dsCoeff_eq_flenstedJensen {l : HCParam ε} {m : ℕ} (hl : l.HasGap m) {g : USign ε}
    {a : Matrix n n ℂ} (ha : a ∈ blockDiagAlg ε) (ha_acc : (a⁻¹ * g).IsAccretive) :
    l.dsCoeff g = l.flenstedJensen a (a⁻¹ * g) :=
  flenstedJensen_eq_of_accretive hl ha ha_acc (blockDiagPart_mem _) (by simp)

/-- Let `l = 2λ` be a parameter of gap `h` and `g = p z qᴴ` with `p`, `q` block diagonal and `z`
accretive (`z + zᴴ > 0`). For block diagonal `a` with `a⁻¹ g` accretive, Flensted-Jensen's integral
at `(a, a⁻¹ g)` is `∫_K m_Λ(p k) conj m_Λ(q k) / m_{-λ-ρ}(kᴴ z k) dk / ∫_K |m_Λ|²`, with the
products of minors `m_w = weightMinors w`, `Λ = l.lowestKType` and `λ + ρ = paramAddRho l`. For
invertible `p`, `q` one such `a` is `p q⁻¹`, so the integral depends only on the product
`p z qᴴ`. -/
theorem flenstedJensen_eq_integral_of_eq_mul_mul_conjTranspose {h : ℕ} (hl : l.HasGap h)
    {g a p q z : Matrix n n ℂ} (ha : a ∈ blockDiagAlg ε) (ha_acc : (a⁻¹ * g).IsAccretive)
    (hp : p ∈ blockDiagAlg ε) (hq : q ∈ blockDiagAlg ε) (hz : z.IsAccretive)
    (h_split : g = p * z * qᴴ) :
    l.flenstedJensen a (a⁻¹ * g) =
      (∫ k : maxCompactU ε, weightMinors l.lowestKType (p * k) *
          conj (weightMinors l.lowestKType (q * k)) /
          weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z * k) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
  -- The integral is `I(p, qᴴ)`, `I = l.splittingIntegral g`. By invariance it is `I(p q⁻¹, 1)`,
  -- the value at the splitting `g = (p q⁻¹) (q z qᴴ)`, which does not depend on the left factor.
  obtain ⟨hp_det, hq_det⟩ : p.det ≠ 0 ∧ q.det ≠ 0 := by
    simpa [h_split, hz.det_ne_zero] using ha_acc.det_ne_zero_and_inv_mul.1
  have h_left : (p * q⁻¹)⁻¹ * g = q * z * qᴴ := by
    simp [h_split, Matrix.mul_inv_rev, mul_assoc, hp_det, hq_det]
  have h_acc : ((p * q⁻¹)⁻¹ * g).IsAccretive := by
    simpa [h_left] using hz.conjTranspose_mul_mul (show qᴴ.det ≠ 0 by simp [hq_det])
  have h_invariance : l.splittingIntegral g (p * q⁻¹, 1) = l.splittingIntegral g (p, qᴴ) := by
    have h_shift :
        l.splittingIntegral g (p * q⁻¹ * q, qᴴ * 1) = l.splittingIntegral g (p * q⁻¹, 1) :=
      splittingIntegral_mul_conjTranspose_mul hl (by simpa using h_acc.det_ne_zero_and_inv_mul.2) hq
        hq_det
    rw [← h_shift, nonsing_inv_mul_cancel_right q p hq_det.isUnit, mul_one]
  have h_value : l.flenstedJensen a (a⁻¹ * g) =
      l.splittingIntegral g (p, qᴴ) / l.lowestKType.kTypeNormSq := by
    rw [flenstedJensen_eq_of_accretive hl (mul_mem hp (blockDiagAlg.inv_mem hq)) h_acc ha ha_acc,
      flenstedJensen_eq_splittingIntegral h_acc, h_invariance]
  -- It remains to compare the denominators of the two integrands.
  have h_middle : qᴴ * g⁻¹ * p = z⁻¹ := by
    simp [h_split, Matrix.mul_inv_rev, mul_assoc, hp_det, hq_det]
  have h_denom (k : maxCompactU ε) :
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z * k) =
        weightMinors (paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z⁻¹ * k) := by
    have h_inv : ((k : Matrix n n ℂ)ᴴ * z * k)⁻¹ = (k : Matrix n n ℂ)ᴴ * z⁻¹ * k := by
      simp [← maxCompactU.coe_inv, Matrix.mul_inv_rev, mul_assoc]
    rw [weightMinors_neg (hz.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)).det_ne_zero,
      h_inv]
  simp only [h_value, HCParam.splittingIntegral, HCParam.splittingIntegrand, h_middle, h_denom,
    conj_weightMinors, conjTranspose_mul]

/-! ### The coefficient as a holomorphic function on the set of products -/

variable (ε) in
/-- The set of the matrices `g` for which `z = a⁻¹ g` is accretive (`z + zᴴ > 0`) for some `a` that
is block diagonal for the signs `ε`; such an `a` is invertible. These are the products `p z qᴴ` with
`p`, `q` invertible and block diagonal and `z` accretive; see `New.mem_splittable_iff`. -/
def splittable : Set (Matrix n n ℂ) :=
  {g : Matrix n n ℂ | ∃ a ∈ blockDiagAlg ε, (a⁻¹ * g).IsAccretive}

/-- A matrix lies in `New.splittable ε` if and only if it is a product `p z qᴴ` with `p`, `q`
invertible and block diagonal for the signs `ε` and `z` accretive. -/
theorem mem_splittable_iff {g : Matrix n n ℂ} :
    g ∈ splittable ε ↔ ∃ p ∈ blockDiagAlg ε, ∃ q ∈ blockDiagAlg ε, ∃ z : Matrix n n ℂ,
      p.det ≠ 0 ∧ q.det ≠ 0 ∧ z.IsAccretive ∧ g = p * z * qᴴ := by
  constructor
  · rintro ⟨a, ha, ha_acc⟩
    obtain ⟨ha_det, -⟩ : a.det ≠ 0 ∧ g.det ≠ 0 := by simpa using ha_acc.det_ne_zero
    exact ⟨a, ha, 1, one_mem _, a⁻¹ * g, ha_det, by simp, ha_acc, by simp [ha_det]⟩
  · rintro ⟨p, hp, q, hq, z, hp_det, hq_det, hz, rfl⟩
    have h_left : (p * q⁻¹)⁻¹ * (p * z * qᴴ) = qᴴᴴ * z * qᴴ := by
      simp [Matrix.mul_inv_rev, mul_assoc, hp_det, hq_det]
    refine ⟨p * q⁻¹, mul_mem hp (blockDiagAlg.inv_mem hq), ?_⟩
    rw [h_left]
    exact hz.conjTranspose_mul_mul (by simp [hq_det])

/-- If `a⁻¹ g` is accretive, then so is `a⁻¹ x` for all `x` near `g`. -/
theorem eventually_isAccretive_inv_mul {a g : Matrix n n ℂ} (h_acc : (a⁻¹ * g).IsAccretive) :
    ∀ᶠ x : Matrix n n ℂ in nhds g, (a⁻¹ * x).IsAccretive :=
  (continuous_const_mul a⁻¹).continuousAt.eventually h_acc.setOf_mem_nhds

/-- The set `splittable ε` is open in `Matrix n n ℂ`. This is the set of complex matrices `g` with
`a⁻¹ g` accretive (`z + zᴴ > 0`) for some block diagonal `a`, that is, the products `p z qᴴ` with
`p`, `q` invertible block diagonal and `z` accretive. -/
theorem isOpen_splittable : IsOpen (splittable ε) :=
  isOpen_iff_eventually.2 fun _ ⟨a, ha, ha_acc⟩ ↦
    (eventually_isAccretive_inv_mul ha_acc).mono fun _ hx ↦ ⟨a, ha, hx⟩

open scoped Classical in
/-- The coefficient on the set `New.splittable ε` of products: Flensted-Jensen's integral at
`(a, a⁻¹ g)` for a chosen block diagonal `a` with `a⁻¹ g` accretive, and `0` off this set. -/
noncomputable def HCParam.splitCoeff (l : HCParam ε) (g : Matrix n n ℂ) : ℂ :=
  if h_mem : g ∈ splittable ε then l.flenstedJensen h_mem.choose (h_mem.choose⁻¹ * g) else 0

/-- For a parameter `l` of gap `h`, the coefficient `l.splitCoeff g` is Flensted-Jensen's integral
at `(a, a⁻¹ g)` for every block diagonal `a` with `a⁻¹ g` accretive. -/
theorem splitCoeff_eq_flenstedJensen {h : ℕ} (hl : l.HasGap h) {g a : Matrix n n ℂ}
    (ha : a ∈ blockDiagAlg ε) (ha_acc : (a⁻¹ * g).IsAccretive) :
    l.splitCoeff g = l.flenstedJensen a (a⁻¹ * g) := by
  have h_mem : g ∈ splittable ε := ⟨a, ha, ha_acc⟩
  rw [HCParam.splitCoeff, dite_eq_left h_mem]
  obtain ⟨hb, hb_acc⟩ := h_mem.choose_spec
  exact flenstedJensen_eq_of_accretive hl ha ha_acc hb hb_acc

/-- The coefficient at a product. Let `l = 2λ` be a parameter of gap `h`: its entries are distinct
and congruent to `card n - 1` mod 2, and `|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`. Let `p`, `q` be
invertible and block diagonal (commuting with `diag ε`) and `z` accretive (`z + zᴴ > 0`). Consider
`l.splitCoeff`, which at a matrix `g` with `a⁻¹ g` accretive for some block diagonal `a` is
Flensted-Jensen's integral at `(a, a⁻¹ g)` for a chosen such `a`, and is `0` elsewhere. Then
`l.splitCoeff (p z qᴴ)` is `∫_K m_Λ(p k) conj m_Λ(q k) / m_{-λ-ρ}(kᴴ z k) dk / ∫_K |m_Λ|²`; here
`K = U(diag ε) ∩ U(n)` carries its Haar measure of mass one, `m_w = weightMinors w` is the product
of principal minors of weight `w`, `Λ = l.lowestKType` and `λ + ρ = paramAddRho l`. -/
theorem splitCoeff_mul_mul_conjTranspose {h : ℕ} (hl : l.HasGap h) {p q z : Matrix n n ℂ}
    (hp : p ∈ blockDiagAlg ε) (hq : q ∈ blockDiagAlg ε) (hp_det : p.det ≠ 0) (hq_det : q.det ≠ 0)
    (hz : z.IsAccretive) :
    l.splitCoeff (p * z * qᴴ) =
      (∫ k : maxCompactU ε, weightMinors l.lowestKType (p * k) *
          conj (weightMinors l.lowestKType (q * k)) /
          weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z * k) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
  obtain ⟨a, ha, ha_acc⟩ := mem_splittable_iff.2 ⟨p, hp, q, hq, z, hp_det, hq_det, hz, rfl⟩
  rw [splitCoeff_eq_flenstedJensen hl ha ha_acc]
  exact flenstedJensen_eq_integral_of_eq_mul_mul_conjTranspose hl ha ha_acc hp hq hz rfl

/-- Let `l = 2λ` be a parameter of gap `h`: its entries are distinct and congruent to `card n - 1`
mod 2, and `|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`. Then for every `g` in `U(diag ε)`,
`l.splitCoeff g = l.dsCoeff g`. Here `splitCoeff` is Flensted-Jensen's integral at `(a, a⁻¹ g)` for
a block diagonal `a` with `a⁻¹ g` accretive (and `0` if there is none), and `dsCoeff` is
`c_λ(g) = Ξ(a, a⁻¹ g)` with `a` the block diagonal part of `g`. -/
theorem splitCoeff_eq_dsCoeff {h : ℕ} (hl : l.HasGap h) (g : USign ε) :
    l.splitCoeff g = l.dsCoeff g :=
  splitCoeff_eq_flenstedJensen hl (blockDiagPart_mem _) (isAccretive_blockDiagPart_inv_mul g).2

/-- The coefficient in any splitting. Let `l = 2λ` be a parameter of gap `m`: its entries are
distinct and congruent to `card n - 1` mod 2, and `|λ i - λ j| ≥ m` whenever `ε i ≠ ε j`. Let `g` in
`U(diag ε)` be a product `p z qᴴ` with `p`, `q` block diagonal (commuting with `diag ε`) and `z`
accretive (`z + zᴴ > 0`). Then `l.dsCoeff g`, the function `c_λ(g) = Ξ(a, a⁻¹g)` with `a` the block
diagonal part of `g` and `Ξ` Flensted-Jensen's normalised integral, is `∫_K m_Λ(p k) conj m_Λ(q
k) / m_{-λ-ρ}(kᴴ z k) dk / ∫_K |m_Λ|²`; here `K = U(diag ε) ∩ U(n)` carries its Haar measure of mass
one, `m_w = weightMinors w` is the product of principal minors of weight `w`, `Λ = l.lowestKType`
and `λ + ρ = paramAddRho l`. -/
theorem dsCoeff_eq_integral_of_eq_mul_mul_conjTranspose {m : ℕ} (hl : l.HasGap m) {g : USign ε}
    {p q z : Matrix n n ℂ} (hp : p ∈ blockDiagAlg ε) (hq : q ∈ blockDiagAlg ε)
    (hz : z.IsAccretive) (h_split : (g : Matrix n n ℂ) = p * z * qᴴ) :
    l.dsCoeff g =
      (∫ k : maxCompactU ε, weightMinors l.lowestKType (p * k) *
          conj (weightMinors l.lowestKType (q * k)) /
          weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z * k) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
  obtain ⟨hp_det, hq_det⟩ : p.det ≠ 0 ∧ q.det ≠ 0 := by
    simpa [h_split, hz.det_ne_zero] using GeneralLinearGroup.det_ne_zero (g : GL n ℂ)
  rw [← splitCoeff_eq_dsCoeff hl, h_split]
  exact splitCoeff_mul_mul_conjTranspose hl hp hq hp_det hq_det hz

/-- For a parameter `l` of gap `h`, the coefficient `l.splitCoeff` is holomorphic on the open set
`New.splittable ε` of the products `p z qᴴ` with `p`, `q` invertible and block diagonal and `z`
accretive (`z + zᴴ > 0`). On this set, `l.splitCoeff g` is Flensted-Jensen's integral at
`(a, a⁻¹ g)` for a block diagonal `a` with `a⁻¹ g` accretive. This is a corollary of the
independence of the splitting; on the group itself the later proofs use
`New.HCParam.analyticAt_dsCoeff`. -/
theorem analyticOnNhd_splitCoeff {h : ℕ} (hl : l.HasGap h) :
    AnalyticOnNhd ℂ l.splitCoeff (splittable ε) := by
  -- Near `g` one factor `a` serves for all points, and for fixed `a` the integral is analytic.
  rintro g ⟨a, ha, ha_acc⟩
  refine AnalyticAt.congr (f := fun x : Matrix n n ℂ ↦ l.flenstedJensen a (a⁻¹ * x)) ?_
    ((eventually_isAccretive_inv_mul ha_acc).mono fun x hx ↦
      (splitCoeff_eq_flenstedJensen hl ha hx).symm)
  unfold HCParam.flenstedJensen
  exact ((isAnalyticFamily_flenstedJensen l (a := fun _ ↦ a) analyticAt_const
    ha_acc).analyticAt_integral (haarK ε)).div_const

end New

/-! ## Triangular factors -/

namespace New.DiscreteSeries

open Matrix MeasureTheory ComplexConjugate ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {h : ℕ}

/-- Let `l = 2λ` be a parameter of gap `h` (in particular with distinct entries), and let `b'` and
`b` be block diagonal and invertible, with `b'` lower and `b` upper triangular in the order of
decreasing `l`. Let `c = l.splitCoeff` be Flensted-Jensen's integral at `(a, a⁻¹ g)` for a block
diagonal `a` with `a⁻¹ g` accretive, on the open set `New.splittable ε` of the products `p z qᴴ`
with `p`, `q` invertible and block diagonal and `z` accretive (`z + zᴴ > 0`). Then for `g` in this
set, `c (b' g b) = b' ^ Λ b ^ Λ c g`, where `b ^ Λ = ∏ i, b i i ^ Λ i` and `Λ = l.lowestKType` is
the highest weight of the lowest `K`-type. -/
theorem splitCoeff_triangular_mul_mul_triangular {l : HCParam ε} (hl : l.HasGap h)
    {b' g b : Matrix n n ℂ} (hb'_mem : b' ∈ blockDiagAlg ε) (hb' : IsBorelMatrix l b')
    (hb_mem : b ∈ blockDiagAlg ε) (hb : IsBorelMatrix (-l) b) (hg : g ∈ splittable ε) :
    l.splitCoeff (b' * g * b) =
      diagChar l.lowestKType b' * diagChar l.lowestKType b * l.splitCoeff g := by
  -- Replace `p`, `q` by `b' p`, `bᴴ q` in the integral; both factors come out of the minors.
  obtain ⟨p, hp, q, hq, z, hp_det, hq_det, hz, rfl⟩ := mem_splittable_iff.1 hg
  have hb_adj_mem : bᴴ ∈ blockDiagAlg ε := conjTranspose_mem_blockDiagAlg hb_mem
  have hb_adj : IsBorelMatrix l bᴴ := isBorelMatrix_conjTranspose hb
  have h_minors {a x : Matrix n n ℂ} (ha_mem : a ∈ blockDiagAlg ε) (ha : IsBorelMatrix l a)
      (hx : x.det ≠ 0) (k : maxCompactU ε) : weightMinors l.lowestKType (a * x * k) =
        diagChar l.lowestKType a * weightMinors l.lowestKType (x * k) := by
    rw [mul_assoc]
    exact hl.isKDominant_lowestKType.weightMinors_oppBorel_mul hl.neg.injective
      (by simp [hx, GeneralLinearGroup.det_ne_zero]) ha_mem (by rwa [neg_neg])
  have h_char : conj (diagChar l.lowestKType bᴴ) = diagChar l.lowestKType b := by simp [diagChar]
  have h_split : b' * (p * z * qᴴ) * b = b' * p * z * (bᴴ * q)ᴴ := by simp [mul_assoc]
  have hb'p : (b' * p).det ≠ 0 := by simp [hb'.right, hp_det]
  have hbq : (bᴴ * q).det ≠ 0 := by simp [hb.right, hq_det]
  rw [h_split, splitCoeff_mul_mul_conjTranspose hl hp hq hp_det hq_det hz,
    splitCoeff_mul_mul_conjTranspose hl (mul_mem hb'_mem hp) (mul_mem hb_adj_mem hq) hb'p hbq hz,
    ← mul_div_assoc, ← integral_const_mul]
  -- Both sides now have the same denominator, and the integrands agree at each `k`.
  congr 1
  refine integral_congr_ae (.of_forall fun k ↦ ?_)
  simp only [h_minors hb'_mem hb' hp_det, h_minors hb_adj_mem hb_adj hq_det, map_mul, h_char]
  ring

/-- Let `l = 2λ` be a parameter of gap `h` (in particular with distinct entries), and
let `b'` and `b` be block diagonal and invertible, `b'` lower and `b` upper triangular in the order
of decreasing `l`. If `y` and `b' y b` are accretive (positive definite Hermitian part), then
Flensted-Jensen's coefficient `c = l.flenstedJensen 1` satisfies `c (b' y b) = b' ^ Λ b ^ Λ c y`,
where `b ^ Λ = ∏ i, b i i ^ Λ i` for the highest weight `Λ` of the lowest `K`-type. -/
theorem flenstedJensen_triangular_mul_mul_triangular {l : HCParam ε} (hl : l.HasGap h)
    {b' y b : Matrix n n ℂ} (hb'_mem : b' ∈ blockDiagAlg ε) (hb' : IsBorelMatrix l b')
    (hb_mem : b ∈ blockDiagAlg ε) (hb : IsBorelMatrix (-l) b) (hy : y.IsAccretive)
    (hb'yb : (b' * y * b).IsAccretive) :
    l.flenstedJensen 1 (b' * y * b) =
      diagChar l.lowestKType b' * diagChar l.lowestKType b * l.flenstedJensen 1 y := by
  -- At an accretive matrix the left factor `1` is admissible.
  have h_value {x : Matrix n n ℂ} (hx : x.IsAccretive) : l.flenstedJensen 1 x = l.splitCoeff x := by
    simpa using (splitCoeff_eq_flenstedJensen hl (one_mem _) (by simpa using hx)).symm
  rw [h_value hy, h_value hb'yb]
  exact splitCoeff_triangular_mul_mul_triangular hl hb'_mem hb' hb_mem hb
    ⟨1, one_mem _, by simpa using hy⟩

end New.DiscreteSeries

/-! ## c_λ as a smooth function on U(diag ε) -/

section PsiSmooth

open Set Matrix.Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} (l : New.HCParam (n := n) ε)

/-- The function c_λ, l = 2λ, regarded as an element of the space of smooth complex functions on
U(diag ε). -/
@[simps]
noncomputable def New.HCParam.dsCoeffSmooth : SmoothU ε ℂ :=
  ⟨(l.dsCoeff ·),
    -- Multiply `dsCoeff` by a smooth cutoff that is `1` on the closed image of the group and is
    -- supported where `dsCoeff` is analytic.
    have ⟨f, hf⟩ : ∃ f : SmoothPartitionOfUnity Unit (modelWithCornersSelf ℝ (Matrix n n ℂ))
          (Matrix n n ℂ) (range fun x : U (signMatrix ε) ↦ x),
        f.IsSubordinate fun _ : Unit ↦ {x : Matrix n n ℂ | AnalyticAt ℂ l.dsCoeff x} :=
      SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ (Matrix n n ℂ))
        isClosedEmbedding_U.isClosed_range _ (fun _ ↦ isOpen_analyticAt ℂ l.dsCoeff)
        (subset_iUnion_of_subset () (range_subset_iff.mpr analyticAt_dsCoeff))
    ⟨⟨_, (f.contMDiff_finsum_smul fun i _ hx ↦
        (hf i hx).restrictScalars.contDiffAt.contMDiffAt).contDiff⟩,
      funext (by simp [↓← finsum_smul, f.sum_eq_one])⟩⟩

/-- The function c_λ = `HCParam.dsCoeff l` is continuous on U(diag ε): its composite with any
continuous map `f : X → U(diag ε)` is continuous. Here c_λ(g) = Ξ(a, a⁻¹g), with `a` the block
diagonal part of `g` and Ξ Flensted-Jensen's normalised integral. -/
@[fun_prop]
lemma New.continuous_dsCoeff {X : Type*} [TopologicalSpace X] {f : X → USign ε}
    (hf : Continuous f) : Continuous (fun x : X ↦ l.dsCoeff (f x)) :=
  (SmoothU.continuous l.dsCoeffSmooth).comp hf

end PsiSmooth

/-! ## The Casimir eigenvalue of c_λ -/

namespace New

open Matrix Filter Norms.L2Operator ContinuousMap GlModule U HCParam

variable {n : Type _} [Fintype n] {ε : n → ℤˣ} {h : ℕ}

/-- The indices can be numbered so that an injective integer vector l is strictly increasing. -/
theorem exists_equiv_fin_lt_iff {l : n → ℤ} (hl : l.Injective) :
    ∃ e : Fin (Fintype.card n) ≃ n, ∀ a b : Fin (Fintype.card n), l (e a) < l (e b) ↔ a < b := by
  -- Enumerate `n` increasingly for the linear order pulled back along `l`.
  let _ : LinearOrder n := .lift' l hl
  exact ⟨(monoEquivOfFin n rfl).toEquiv, fun a b ↦ (monoEquivOfFin n rfl).lt_iff_lt⟩

/-- For a parameter `l = 2λ` of gap `h`, the eigenvalue |λ|² − |ρ|² = `HCParam.casimirValue l` is
the value `casimirKValue` that the Casimir operator takes on a lowest weight vector of weight
`λ + ρ`, that is, a highest vector for the roots positive for `-l`, all pairs of indices counting
as compact (`compactForm`). -/
theorem casimirValue_eq_casimirKValue_paramAddRho [DecidableEq n] {l : HCParam (n := n) ε}
    (hl : l.HasGap h) :
    (l.casimirValue : ℂ) = (-l).compactForm.casimirKValue (paramAddRho l) := by
  -- Substitute `l = 2 (λ + ρ) - 2ρ`; the positive roots for `-l` are the negatives of those of `l`.
  simp [casimirKValue, casimirValue, twoRho_neg, ← sub_eq_of_eq_add (two_mul_paramAddRho hl _)]
  simp only [twoRho, Pi.top_apply, Prop.top_eq_true, true_and]
  grind

/-- Let `l` have gap `h`, let `y` be in U(diag ε), `k` in K and `a⁻¹ y` accretive. Let `F`, with
values in continuous functions on K, be differentiable at `y`, and let `F x k` agree for matrices
`x` near `y` with the integrand of Flensted-Jensen's integral at `(a, a⁻¹ x)`, a quotient of
products of principal minors `weightMinors`. For `l i ≤ l j`, the derivative of `F` in the direction
`y (k E_ij k⁻¹)`, evaluated at `k`, is `(λ + ρ) i` times `F y k` if `i = j` and zero otherwise,
where λ + ρ = `paramAddRho l`. -/
theorem fderiv_flenstedJensen_integrand_single [DecidableEq n] {l : HCParam (n := n) ε}
    (hl : l.HasGap h) {a : Matrix n n ℂ} {F : Matrix n n ℂ → C(maxCompactU ε, ℂ)} {y : USign ε}
    (k : maxCompactU ε)
    (hF : ∀ᶠ x : Matrix n n ℂ in nhds (y : Matrix n n ℂ), F x k =
      weightMinors l.lowestKType (a * k) * starRingEnd ℂ (weightMinors l.lowestKType k) /
        weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * (a⁻¹ * x) * k))
    (hF_diff : DifferentiableAt ℂ F y) (h_acc : (a⁻¹ * y).IsAccretive) {i j : n} (hij : l i ≤ l j) :
    fderiv ℂ F y ((y : Matrix n n ℂ) * ((k : Matrix n n ℂ) * single i j 1 * (k : GL n ℂ)⁻¹.val)) k =
      (if i = j then (paramAddRho l i : ℂ) else 0) * F y k := by
  -- Under `y ↦ c t = y * (k * t * k⁻¹)` with `t` triangular for `l` the integrand is multiplied by
  -- `diagChar (paramAddRho l) t`, because the argument of `weightMinors (-paramAddRho l)` is
  -- multiplied by `t` on the right.
  let c : Matrix n n ℂ → Matrix n n ℂ := fun t ↦ y * (k * t * (k : GL n ℂ)⁻¹.val)
  have h_equivariant : ∀ᶠ x : Matrix n n ℂ in nhds (y : Matrix n n ℂ), ∀ t ∈ blockDiagAlg 1,
      IsBorelMatrix (- -l) t → x = c t → F x k = diagChar (paramAddRho l) t * F y k := by
    filter_upwards [hF] with x hx t t_mem t_tri x_eq
    have h_arg :
        (k : Matrix n n ℂ)ᴴ * (a⁻¹ * c t) * k = (k : Matrix n n ℂ)ᴴ * (a⁻¹ * y) * k * t := by
      simp [c, mul_assoc, GeneralLinearGroup.det_ne_zero]
    rw [hx, hF.self_of_nhds, x_eq, h_arg,
      hl.isKDominant_neg_paramAddRho.weightMinors_mul_borel hl.injective
        (h_acc.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)).det_ne_zero t_mem
        (by rwa [neg_neg] at t_tri)]
    simp [diagChar, field]
  -- Differentiate along `t = 1 + s • single i j 1`, which is triangular as `l i ≤ l j`.
  have h_direction (s : ℂ) : ↑y + s • c (single i j 1) = c (1 + s • single i j 1) := by
    simp [c, mul_add, add_mul, -smul_single]
  exact fderiv_eq_of_borel_equivariant 1 (f := evalCLM ℂ k ∘ F) (o := -l)
    ((evalCLM ℂ k).hasFDerivAt.comp _ hF_diff.hasFDerivAt) (neg_le_neg hij) rfl c h_equivariant
    h_direction

/-- Let `l = 2λ` have gap `h` (distinct entries congruent to `card n - 1` mod 2, with
|λ_i − λ_j| ≥ h whenever ε_i ≠ ε_j), let `f` be a smooth function on U(diag ε) with values in `E`,
let `L` be a continuous linear form on `E` and `k` an invertible matrix. Suppose that near `g` the
function `L ∘ f` is a lowest weight vector of weight λ + ρ = `paramAddRho l` in the basis
`k E_ab k⁻¹` of gl_n, acting by right derivatives. Then the Casimir operator `casimirK 1` of gl_n
multiplies the value of `L ∘ f` at `g` by |λ|² − |ρ|² = `l.casimirValue`. -/
theorem apply_casimirK_rightDeriv_of_lowest_weight [DecidableEq n] {l : HCParam (n := n) ε}
    (hl : l.HasGap h) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : SmoothU ε E)
    (L : E →L[ℂ] ℂ) (k : GL n ℂ) (g : USign ε)
    (h_lowest : ∀ a b : n, l a ≤ l b → ∀ᶠ y : USign ε in nhds g,
      L ((rightDeriv ε E (k.val * single a b 1 * k⁻¹.val) f).val y) =
        (if a = b then (paramAddRho l a : ℂ) else 0) * L (f.val y)) :
    L (((rightDeriv ε E).casimirK 1 f).val g) = l.casimirValue * L (f.val g) := by
  -- The germs at `g` of the functions `L ∘ u` form a module `σ`, as right derivatives are local.
  let germ : SmoothU ε E →ₗ[ℂ] Germ (nhds g) ℂ :=
    { toFun u := Germ.ofFun (L ∘ u.val)
      map_add' u v := congrArg Germ.ofFun (funext fun y ↦ L.map_add (u.val y) (v.val y))
      map_smul' c u := congrArg Germ.ofFun (funext fun y ↦ L.map_smul c (u.val y)) }
  have h_ker (X : Matrix n n ℂ) (u : SmoothU ε E) (hu : germ u = 0) :
      germ (rightDeriv ε E X u) = 0 :=
    have h_zero : (0 : SmoothU ε ℂ).val =ᶠ[nhds g] L ∘ u.val := Germ.coe_eq.1 hu.symm
    have h_deriv : (rightDeriv ε ℂ X 0).val =ᶠ[nhds g] L ∘ (rightDeriv ε E X u).val :=
      rightDeriv_comp_clm L h_zero
    h_deriv.germ_eq.symm.trans (by simp)
  obtain ⟨σ, hσ⟩ : ∃ σ : GlModule n germ.range, ∀ (X : Matrix n n ℂ) (u : SmoothU ε E),
      σ X (germ.rangeRestrict u) = germ.rangeRestrict (rightDeriv ε E X u) :=
    (rightDeriv ε E).exists_action_on_range germ h_ker
  -- In the basis `k E_ab k⁻¹`, given by `σ.adTwist k`, the germ of `L ∘ f` is a highest vector.
  have highest : (-l).compactForm.IsKHighest (σ.adTwist k) (paramAddRho l)
      (germ.rangeRestrict f) := by
    refine .of_E_eq_smul fun a b _ hab ↦ (hσ _ f).trans (Subtype.ext ?_)
    -- As germs at `g`, this is the hypothesis on `L ∘ f`.
    exact Germ.coe_eq.2 (h_lowest a b (neg_le_neg_iff.1 hab))
  -- On a highest vector the Casimir, which does not depend on the basis, is a scalar.
  have h_germ : germ.rangeRestrict ((rightDeriv ε E).casimirK 1 f) =
      (l.casimirValue : ℂ) • germ.rangeRestrict f := by
    rw [casimirValue_eq_casimirKValue_paramAddRho hl,
      ← highest.casimirK_eq_smul (hg := hl.neg.signs_one), casimirK_one_adTwist]
    simp [GlModule.casimir, hσ]
  exact congrArg (fun v : germ.range ↦ v.val.value) h_germ

/-- Let `l = 2λ` be a parameter of gap `h`: its entries are distinct and congruent to `card n - 1`
mod 2, and `|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`. Then the Casimir operator Ω = Σ_{a,b} E_ab E_ba
of gl_n, acting on smooth functions on U(diag ε) by complexified right derivatives, satisfies
Ωc_λ = (|λ|² − |ρ|²) c_λ. Here c_λ is `HCParam.dsCoeffSmooth l`, ρ is the half sum of the roots
positive for `l`, and the eigenvalue is `HCParam.casimirValue l`. The operator
`New.GlModule.casimirK` sums over the pairs with equal signs; for the constant sign vector 1 these
are all pairs, so `casimirK 1` is Ω.

This proves the Casimir eigenvalue formula of Harish-Chandra's discrete series in the case of the
explicit function c_λ on U(p,q) (Flensted-Jensen's function), for any gap. -/
theorem casimir_dsCoeffSmooth [DecidableEq n] {l : HCParam (n := n) ε} [hl : l.HasGap h] :
    (rightDeriv ε ℂ).casimirK 1 l.dsCoeffSmooth = (l.casimirValue : ℂ) • l.dsCoeffSmooth := by
  -- Near `g`, `l.dsCoeffSmooth` is the average over `k` of the integrand `Φ · k` of
  -- `flenstedJensen`, with the block diagonal factor frozen at `blockDiagPart ε g`. For fixed
  -- `k` the germ of `Φ · k` is a lowest weight vector in the basis `k E_ij k⁻¹`.
  ext g
  let Φ (x : Matrix n n ℂ) (k : maxCompactU ε) : ℂ :=
    weightMinors l.lowestKType (blockDiagPart ε g * k) *
      starRingEnd ℂ (weightMinors l.lowestKType k) /
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * ((blockDiagPart ε g)⁻¹ * x) * k)
  -- Near `g`, `Φ` is given by an analytic map `F₀` into `C(K, ℂ)`, so by a globally smooth `F`.
  obtain ⟨F₀, F₀_an, F₀_eq⟩ : DiscreteSeries.IsAnalyticFamily Φ g :=
    isAnalyticFamily_flenstedJensen l analyticAt_const (isAccretive_blockDiagPart_inv_mul g).2
  obtain ⟨F, F_smooth, F_eq⟩ := exists_contDiff_eventuallyEq F₀_an.restrictScalars.contDiffAt
  have F_Φ : ∀ᶠ x : Matrix n n ℂ in nhds (g : Matrix n n ℂ), F x = Φ x := by
    filter_upwards [F₀_eq, F_eq] with x hx₀ hx using by rw [hx, hx₀]
  have near : ∀ᶠ y : USign ε in nhds g, (∀ᶠ x in nhds (y : Matrix n n ℂ), F x = Φ x) ∧
      AnalyticAt ℂ F y ∧ ((blockDiagPart ε g)⁻¹ * y).IsAccretive :=
    continuous_mat.tendsto g <| F_Φ.eventually_nhds.and <|
      (F₀_an.congr F_eq.symm).eventually_analyticAt.and <|
        eventually_isAccretive_inv_mul (isAccretive_blockDiagPart_inv_mul g).2
  -- `f` is the restriction of `F` to the group.
  let f : SmoothU ε C(maxCompactU ε, ℂ) := ⟨fun y : USign ε ↦ F y, ⟨F, F_smooth⟩, rfl⟩
  have f_eigen :
      ((rightDeriv ε C(_, ℂ)).casimirK 1 f).val g = (l.casimirValue : ℂ) • f.val g := by
    ext k
    refine apply_casimirK_rightDeriv_of_lowest_weight hl f (evalCLM ℂ k) k g fun i j hij ↦ ?_
    filter_upwards [near] with y ⟨hy, y_an, y_acc⟩
    rw [rightDeriv_apply_eq_of_hasFDerivAt (f := f) y_an.differentiableAt.hasFDerivAt fun _ ↦ rfl]
    exact fderiv_flenstedJensen_integrand_single hl k (hy.mono fun x hx ↦ congrFun hx k)
      y_an.differentiableAt y_acc hij
  -- `L` is the normalised integral over `K`; it commutes with right derivatives.
  obtain ⟨L, psi_eq⟩ : ∃ L : C(maxCompactU ε, ℂ) →L[ℂ] ℂ,
      l.dsCoeffSmooth.val =ᶠ[nhds g] L ∘ f.val := by
    refine ⟨l.lowestKType.kTypeNormSq⁻¹ • strongIntegral (haarK ε) (evalCLM ℂ), ?_⟩
    filter_upwards [near] with y ⟨hy, _, y_acc⟩
    simp [f, Φ, strongIntegral_eval, hy.self_of_nhds,
      dsCoeff_eq_flenstedJensen hl (blockDiagPart_mem g), y_acc, flenstedJensen, field]
  -- Right derivatives are local and commute with `L`.
  have h_casimir : ((rightDeriv ε ℂ).casimirK 1 l.dsCoeffSmooth).val g =
      L (((rightDeriv ε C(_, ℂ)).casimirK 1 f).val g) := by
    simp [GlModule.casimir, fun X Y : Matrix n n ℂ ↦ (rightDeriv_comp_clm (X := X) L
      (rightDeriv_comp_clm (X := Y) L psi_eq)).eq_of_nhds]
  rw [h_casimir, f_eigen, map_smul, SetLike.val_smul, Pi.smul_apply, psi_eq.eq_of_nhds,
    Function.comp_apply]

end New
