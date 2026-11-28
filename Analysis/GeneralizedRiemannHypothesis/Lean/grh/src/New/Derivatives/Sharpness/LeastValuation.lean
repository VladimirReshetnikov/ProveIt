import New.Derivatives.Sharpness.OneCurve

/-!
# Least valuations of coefficients of theta products

The file bounds the least valuation `val_n(ν)` of a coefficient of degree `ν` in a product
`∏ (H_c Θ)(z_c)` over `n` copies of the variables.

The imported notions used in the statements are:

* `CMLattice d`: a lattice in `ℂ`, with a marked point `t` of order two and normalized at `t`, that
  is stable under the ring of integers of `ℚ(√-d)` if `d ≠ 0`. The results that need `d` to be a
  prime with `d ≡ 7 (mod 8)` assume `PrimeSevenModEight d`. Its function `C.θ` is the twisted
  translate by `t` of the sigma function with value `1` at `0`, and `C.translatedY` is an affine
  combination of `℘'(z + t)` and `℘(z + t)`.
* `PadicPlace p`: a ring homomorphism `ιₚ : ℂ →+* ℂ_[p]`. By `taylorVia ιₚ f` is meant the Taylor
  series of `f` at `0` with `ιₚ` applied to the coefficients.
* `C.thetaProd μ m`: the series `Θ = ∏ θ(μ_j z) ^ m j`, where `θ` is the Taylor series of `C.θ`
  and the `μ_j` are linear forms over `ℂ_p`.
* `C.multiSeriesRing μ`: the ring of integral power series in the series `y(μ_j z)`, where `y` is
  the Taylor series of `C.translatedY`.
* `varpiValuation d p`: the number `ρ_p`, equal to `1 / (p - 1)`, `1 / (p² - 1)`, `1 / (2 p - 2)`
  when `p` is split, inert, ramified in `ℚ(√-d)`. A scaling of valuation at least `ρ_p` makes the
  series in `y` integral.
* `gammaPrime d p`: the rate `γ_p = 1 / (p - 1) - ρ_p`.

## Main definitions and results

* `New.CMLattice.LeastValLE`: the relation `val_n(ν) ≤ r` for the least valuation of a coefficient
  of degree `ν` in a product `∏ (H_c Θ)(z_c)` over `n` copies of the variables.
* `New.CMLattice.LeastValLE.add`, `New.CMLattice.leastValLE_of_copySubst`: the two rules, for
  products and for integral substitutions.
* `New.CMLattice.scaledThetaProd`: the product `∏ Θ(δ_c z)` of scaled copies of `Θ`.
* `New.CMLattice.exists_scaledThetaProd_mem_mul_eq_one`: six scaled copies of `Θ` multiply to a unit
  of the ring of integral series in the `y(μ_j z)`.
* `New.CMLattice.leastValLE_of_unit_coefficients`, `New.CMLattice.leastValLE_zero_of_span`: two
  bounds for `val₆` in all degrees, when one form has unit coefficients and when integral
  combinations of the forms give the coordinates up to a unit.
-/

/-!
## Least valuations of coefficients of theta products

For suitable scales in `ℤ_p` whose squares add up to zero, the product of six scaled copies of `Θ`
is a unit of the ring of integral series in the `y(μ_j z)`.
-/

section LeastValuation

open MvPowerSeries Finset Nat

namespace New

section LowestTerm
variable {X R : Type} [CommRing R]

/-- `c z ^ m` is the lowest term of `f` for the weight `w`: in weight at most that of `m`, the
coefficients of `f` are those of the monomial `c z ^ m` (here `c = 0` is allowed). -/
def IsLowestTerm (w : X → ℕ) (f : MvPowerSeries X R) (m : X →₀ ℕ) (c : R) : Prop :=
  ∀ d : X →₀ ℕ, d.weight w ≤ m.weight w → coeff d f = (monomial m c).coeff d

/-- The lowest term of a product is the product of the lowest terms: if `f` has lowest term
`c * z ^ D` and `g` has lowest term `d * z ^ D'` for the weights `w`, then `f * g` has lowest term
`(c * d) * z ^ (D + D')`. -/
lemma IsLowestTerm.mul {w : X → ℕ} {f g : MvPowerSeries X R} {D D' : X →₀ ℕ} {c d : R}
    (hf : IsLowestTerm w f D c) (hg : IsLowestTerm w g D' d) :
    IsLowestTerm w (f * g) (D + D') (c * d) := by
  classical
  intro e he
  -- Compare the coefficients of the two products at `e` term by term, over all `x + y = e`.
  rw [← monomial_mul_monomial, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun ⟨x, y⟩ hxy ↦ ?_
  obtain rfl : x + y = e := mem_antidiagonal.1 hxy
  rw [map_add, map_add] at he
  by_cases hx : x.weight w ≤ D.weight w
  · by_cases hy : y.weight w ≤ D'.weight w
    · rw [hf x hx, hg y hy]
    · -- `y` is heavier than `D'`, so `x` is lighter than `D` and both first factors vanish.
      rw [hf x hx, coeff_monomial_ne (by grind : x ≠ D), zero_mul, zero_mul]
  · -- `x` is heavier than `D`, so `y` is lighter than `D'` and both second factors vanish.
    rw [hg y (by omega), coeff_monomial_ne (by grind : y ≠ D'), mul_zero, mul_zero]

end LowestTerm

/-- If each factor `f i` has lowest term `c i * z ^ α i` for the weights `w`, then the product of
the `f i` has lowest term `(∏ c i) * z ^ (∑ α i)`. -/
lemma IsLowestTerm.prod {X R ι : Type} [Fintype X] [CommRing R] {w : X → ℕ} {s : Finset ι}
    {f : ι → MvPowerSeries X R} {α : ι → X →₀ ℕ} {c : ι → R}
    (hf : ∀ i ∈ s, IsLowestTerm w (f i) (α i) (c i)) :
    IsLowestTerm w (∏ i ∈ s, f i) (∑ i ∈ s, α i) (∏ i ∈ s, c i) := by
  induction s using cons_induction with
  | empty => simp [IsLowestTerm]
  | cons i s hi ih =>
    simp only [prod_cons, sum_cons]
    exact (hf i (mem_cons_self i s)).mul (ih fun j hj ↦ hf j (mem_cons_of_mem hj))

/-- If `f` has lowest term `c * z ^ α`, then `f ^ k` has lowest term `c ^ k * z ^ (k • α)`. -/
lemma IsLowestTerm.pow {X R : Type} [Fintype X] [CommRing R] {w : X → ℕ} {f : MvPowerSeries X R}
    {α : X →₀ ℕ} {c : R} (hf : IsLowestTerm w f α c) (k : ℕ) :
    IsLowestTerm w (f ^ k) (k • α) (c ^ k) := by
  simpa using IsLowestTerm.prod (s := range k) fun _ _ ↦ hf

/-- The substitution `F ↦ F (∑ a_k z_k)` of a linear combination of copies `z_k` of the variables
`z`, with the same coefficients `a_k` for all variables. The copy `k` of the variable `x` is the
variable `(x, k)`. -/
noncomputable def copySubst {X K R : Type} [Fintype X] [Fintype K] [CommRing R] (a : K → R) :
    MvPowerSeries X R →ₐ[R] MvPowerSeries (X × K) R :=
  substAlgHom (a := fun x : X ↦ ∑ k : K, a k • MvPowerSeries.X (x, k))
    (hasSubst_of_constantCoeff_zero (by simp))

section copySubst
variable {X K R : Type} [Fintype X] [Fintype K] [CommRing R]

lemma hasSubst_sum_smul_X (a : K → R) :
    HasSubst fun x : X ↦ ∑ k : K, a k • (MvPowerSeries.X (x, k) : MvPowerSeries (X × K) R) :=
  hasSubst_of_constantCoeff_zero (by simp)

lemma copySubst_apply (a : K → R) (F : MvPowerSeries X R) :
    copySubst a F = F.subst fun x : X ↦ ∑ k : K, a k • MvPowerSeries.X (x, k) :=
  substAlgHom_apply _ F

/-- The chain rule: the derivative of `F (∑ a_l z_l)` in the `k`-th copy of the variable `x` is
`a_k` times `(∂_x F) (∑ a_l z_l)`. -/
lemma pderiv_copySubst (a : K → R) (F : MvPowerSeries X R) (x : X) (k : K) :
    pderiv (x, k) (copySubst a F) = a k • copySubst a (pderiv x F) := by
  classical
  have h_form (y : X) : pderiv (x, k) (∑ k' : K, a k' • MvPowerSeries.X (y, k')) =
      if y = x then a k • (1 : MvPowerSeries (X × K) R) else 0 := by
    simp [pderiv_X, Pi.single_apply, Prod.ext_iff, ite_and]
  -- `-map_sum`: the derivative of each linear form is rewritten as a whole by `h_form`
  simp [copySubst_apply, pderiv_subst (hasSubst_sum_smul_X a), h_form, -map_sum]

/-- The substitution of copies commutes with a change of coefficients along a ring map. -/
lemma map_copySubst {S : Type} [CommRing S] (f : R →+* S) (a : K → R) (F : MvPowerSeries X R) :
    map f (copySubst a F) = copySubst (fun k : K ↦ f (a k)) (map f F) := by
  rw [copySubst_apply, copySubst_apply, map_subst (hasSubst_sum_smul_X a)]
  simp [smul_eq_C_mul]

/-- Setting all copies but the `k`-th to zero turns `F (∑ a_l z_l)` into `F (a_k z)`. -/
lemma killCompl_copySubst (a : K → R) (F : MvPowerSeries X R) (k : K) :
    killCompl (Function.Embedding.sectL X k) (copySubst a F) = rescale (fun _ : X ↦ a k) F := by
  have h_form (x : X) : killCompl (Function.Embedding.sectL X k)
      (∑ k' : K, a k' • MvPowerSeries.X (x, k')) = a k • MvPowerSeries.X (R := R) x := by
    rw [map_sum, sum_eq_single_of_mem k (mem_univ k), map_smul]
    · exact congrArg (a k • ·) (killCompl_X x)
    exact fun k' _ hk' ↦ by simp [killCompl_X_eq_zero, Prod.ext_iff, hk'.symm]
  ext d
  -- Both coefficients are sums over the monomials of `F`; compare them term by term.
  rw [coeff_killCompl, copySubst_apply, coeff_subst (hasSubst_sum_smul_X a), rescale_eq_subst,
    coeff_subst (HasSubst.smul_X _)]
  refine finsum_congr fun n ↦ ?_
  simp only [← coeff_killCompl, map_finsuppProd, map_pow, h_form, Pi.smul_apply']

/-- Scaling all variables by `r` commutes with the substitution of copies: both composites send
`F` to `F (∑ r a_k z_k)`. -/
lemma rescale_copySubst (a : K → R) (r : R) (F : MvPowerSeries X R) :
    rescale (fun _ : X × K ↦ r) (copySubst a F) = copySubst a (rescale (fun _ : X ↦ r) F) := by
  rw [copySubst_apply, copySubst_apply, rescale_eq_subst, rescale_eq_subst,
    subst_comp_subst_apply (hasSubst_sum_smul_X a) (HasSubst.smul_X _),
    subst_comp_subst_apply (HasSubst.smul_X _) (hasSubst_sum_smul_X a)]
  congr 1
  funext x
  -- both sides are the linear form `∑ r a_k z_k`
  trans ∑ k : K, r • a k • (MvPowerSeries.X (x, k) : MvPowerSeries (X × K) R)
  · simp only [← coe_substAlgHom (HasSubst.smul_X _), map_sum, map_smul, substAlgHom_X,
      Pi.smul_apply', smul_comm r]
  · simp [← coe_substAlgHom (hasSubst_sum_smul_X a), smul_sum,
      hasSubst_of_constantCoeff_zero]

/-- The exponent `γ.mapDomain Prod.fst` adds up the copies of each variable in `γ`. -/
lemma mapDomain_fst_apply (γ : X × K →₀ ℕ) (x : X) :
    γ.mapDomain Prod.fst x = ∑ k : K, γ (x, k) := by
  classical simp [Finsupp.mapDomain, Finsupp.sum_fintype, Finsupp.single_apply,
    Fintype.sum_prod_type]

/-- For `γ : X × K →₀ ℕ`, let `γ.mapDomain Prod.fst` be the exponent on `X` that adds up `γ (x, k)`
over `k`. Then `∏ x, (γ.mapDomain Prod.fst x)!` is `∏ y, (γ y)!` times the product over `x` of the
multinomial coefficients of the exponents `γ (x, k)`, `k : K`. -/
lemma prod_factorial_mapDomain_fst (γ : X × K →₀ ℕ) :
    ∏ x : X, (γ.mapDomain Prod.fst x)! =
      (∏ y : X × K, (γ y)!) * ∏ x : X, multinomial univ fun k : K ↦ γ (x, k) := by
  simp only [mapDomain_fst_apply, ← multinomial_spec, Fintype.prod_prod_type, prod_mul_distrib]

/-- Let `δ` be the exponent that adds up the copies of each variable in `γ`. Then `γ!` times the
coefficient of `z ^ γ` in `F (∑ a_k z_k)` is `a ^ γ` times `δ!` times the coefficient of `z ^ δ`
in `F`. -/
lemma prod_factorial_mul_coeff_copySubst (a : K → R) (F : MvPowerSeries X R) (γ : X × K →₀ ℕ) :
    (∏ y : X × K, ((γ y)! : R)) * coeff γ (copySubst a F) =
      (∏ y : X × K, a y.2 ^ γ y) * (∏ x : X, ((γ.mapDomain Prod.fst x)! : R)) *
        coeff (γ.mapDomain Prod.fst) F := by
  classical
  -- Apply the chain rule along `z ^ γ`.
  -- `jet R P F` is `P(∂)F(0)`, and `linSubst M` substitutes `∑ M x y • z_x` for the variable `y`.
  set δ : X →₀ ℕ := γ.mapDomain Prod.fst with hδ
  let M : Matrix X (X × K) R := fun x y ↦ if y.1 = x then a y.2 else 0
  have h_subst : copySubst a F = F.subst fun x : X ↦ linearSeries (M x) := by
    simp [copySubst, linearSeries, M, Fintype.sum_prod_type, ite_smul]
  have h_monomial : linSubst M (.monomial γ 1) = .monomial δ (∏ y : X × K, a y.2 ^ γ y) := by
    simp [linSubst, M, MvPolynomial.monomial_eq, Finsupp.prod_fintype, ite_smul, hδ,
      mapDomain_fst_apply, MvPolynomial.smul_eq_C_mul, mul_pow, prod_mul_distrib,
      Fintype.prod_prod_type, prod_pow_eq_pow_sum]
  calc _ = jet R (.monomial γ 1) (copySubst a F) := by simp [jet_monomial, Finsupp.prod_fintype]
    _ = jet R (.monomial δ (∏ y : X × K, a y.2 ^ γ y)) F := by
      rw [h_subst, jet_subst_linearSeries, h_monomial]
    _ = (∏ y : X × K, a y.2 ^ γ y) * (∏ x : X, ((δ x)! : R)) * coeff δ F := by
      simp [jet_monomial, Finsupp.prod_fintype, mul_assoc]

/-- Over a domain of characteristic zero, the coefficient of `z ^ γ` in `F (∑ a_k z_k)` is `a ^ γ`
times a product of multinomial coefficients times the coefficient of `F` whose exponent adds up the
copies of each variable in `γ`. -/
lemma coeff_copySubst [IsDomain R] [CharZero R] (a : K → R) (F : MvPowerSeries X R)
    (γ : X × K →₀ ℕ) :
    coeff γ (copySubst a F) = (∏ y : X × K, a y.2 ^ γ y) *
      (∏ x : X, multinomial univ fun k : K ↦ γ (x, k) : ℕ) * coeff (γ.mapDomain Prod.fst) F := by
  have h_factorial : (∏ x : X, ((γ.mapDomain Prod.fst x)! : R)) = (∏ y : X × K, ((γ y)! : R)) *
      (∏ x : X, multinomial univ fun k : K ↦ γ (x, k) : ℕ) :=
    mod_cast congrArg (Nat.cast (R := R)) (prod_factorial_mapDomain_fst γ)
  refine mul_left_cancel₀ (a := ∏ y : X × K, ((γ y)! : R))
    (by simp [prod_ne_zero_iff, factorial_ne_zero]) ?_
  rw [prod_factorial_mul_coeff_copySubst, h_factorial]
  ring

/-- A coefficient of `F (∑ a_k z_k)` with integral `a_k` is at most as large as the coefficient of
`F` of the same degree, of which it is an integral multiple. The degree of the exponent `γ` adds up
the copies of each variable. -/
lemma norm_coeff_copySubst_le {p : ℕ} [Fact p.Prime] {a : K → ℂ_[p]} (ha : ∀ k : K, ‖a k‖ ≤ 1)
    (F : MvPowerSeries X ℂ_[p]) (γ : X × K →₀ ℕ) :
    ‖coeff γ (copySubst a F)‖ ≤ ‖coeff (γ.mapDomain Prod.fst) F‖ := by
  rw [coeff_copySubst, norm_mul, norm_mul, norm_prod]
  refine mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) ?_).trans (IsUltrametricDist.norm_natCast_le_one _ _))
  exact prod_le_one₀ (by simp) fun y _ ↦ by simpa using pow_le_one₀ (norm_nonneg _) (ha y.2)

end copySubst

/-- Every `p`-adic integer is a sum of four squares, by Lagrange's theorem and compactness. -/
lemma padicInt_sum_four_squares {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    ∃ a : Fin 4 → ℤ_[p], ∑ i : Fin 4, a i ^ 2 = x := by
  -- The range of the sum of four squares is closed and contains the dense set of naturals.
  change x ∈ Set.range fun a : Fin 4 → ℤ_[p] ↦ ∑ i : Fin 4, a i ^ 2
  refine PadicInt.denseRange_natCast.induction_on x
    (isCompact_range (by fun_prop)).isClosed fun k : ℕ ↦ ?_
  obtain ⟨a, b, c, e, h_sum⟩ := k.sum_four_squares
  exact ⟨![a, b, c, e], by simp [Fin.sum_univ_four, ← h_sum]⟩

namespace CMLattice

variable {d : ℕ} {p : ℕ} [Fact p.Prime] [PadicPlace p]
  {J X : Type} [Fintype J] [Fintype X]

/-- The relation `val_n(ν) ≤ r`: some coefficient of degree `ν` in some product `∏ (H_c Θ)(z_c)`
over `n` copies `z_c` of the variables has valuation at most `r`. Here `C : CMLattice d` is a
lattice in `ℂ` with a marked point `t` of order two, which is stable under the integers of
`ℚ(√-d)` if `d ≠ 0`. The series `Θ = ∏ θ(μ_j z) ^ m j` is `C.thetaProd μ m`, the
`H_c` are integral series in the `y(μ_j z)`, and `θ`, `y` are the Taylor series of `C.θ` (the
normalized sigma function translated by `t`) and `C.translatedY` (a combination of the Weierstrass
functions at `z + t`), read in `ℂ_p` through the place `ιₚ` of `PadicPlace p`. A coefficient of the
product is the product of one coefficient of each factor. -/
def LeastValLE (C : CMLattice d) (μ : J → X → ℂ_[p]) (m : J → ℕ) (n : ℕ) (ν : X →₀ ℕ) (r : ℝ) :
    Prop :=
  ∃ H : Fin n → MvPowerSeries X ℂ_[p], (∀ c : Fin n, H c ∈ C.multiSeriesRing μ) ∧
    ∃ α : Fin n → X →₀ ℕ, ∑ c : Fin n, α c = ν ∧
      (p : ℝ) ^ (-r) ≤ ∏ c : Fin n, ‖coeff (α c) (H c * C.thetaProd μ m)‖

/-- The series `Θ = ∏ θ(μ_j z) ^ m j` has constant term `1`, because `θ(0) = 1`. -/
lemma constantCoeff_thetaProd {C : CMLattice d} {μ : J → X → ℂ_[p]} {m : J → ℕ} :
    constantCoeff (C.thetaProd μ m) = 1 := by
  simp [thetaProd]

/-- The series `Θ = ∏ θ(μ_j z) ^ m j` has lowest term `1` for the total degree. -/
lemma isLowestTerm_thetaProd (C : CMLattice d) (μ : J → X → ℂ_[p]) (m : J → ℕ) :
    IsLowestTerm (fun _ : X ↦ 1) (C.thetaProd μ m) 0 1 := by
  intro β hβ
  obtain rfl : β = 0 := by
    simpa [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_zero_iff] using hβ
  simpa using constantCoeff_thetaProd

/-- If `val_n(ν) ≤ r` and `r ≤ r'`, then `val_n(ν) ≤ r'`, where `val_n(ν)` is the least valuation
of a coefficient of degree `ν` in a product `∏ (H_c Θ)(z_c)` over `n` copies of the variables. -/
lemma LeastValLE.mono {C : CMLattice d} {μ : J → X → ℂ_[p]} {m : J → ℕ} {n : ℕ} {ν : X →₀ ℕ}
    {r r' : ℝ} (hν : C.LeastValLE μ m n ν r) (hr : r ≤ r') : C.LeastValLE μ m n ν r' := by
  obtain ⟨H, hH, α, hα, h_le⟩ := hν
  refine ⟨H, hH, α, hα, le_trans ?_ h_le⟩
  gcongr
  exact mod_cast (Fact.out : p.Prime).one_le

/-- `C.LeastValLE μ m n 0 0`: in degree `0`, some product `∏ (H_c Θ)(z_c)` over `n` copies `z_c` of
the variables, with `Θ = C.thetaProd μ m`, has a coefficient of valuation at most `0`: take all
`H_c = 1`. -/
lemma leastValLE_zero {C : CMLattice d} {μ : J → X → ℂ_[p]} {m : J → ℕ} {n : ℕ} :
    C.LeastValLE μ m n 0 0 :=
  ⟨fun _ ↦ 1, fun _ ↦ one_mem _, fun _ ↦ 0, sum_const_zero, by simp [constantCoeff_thetaProd]⟩

/-- Least valuations are subadditive: if `val_n(ν) ≤ r` and `val_n'(ν') ≤ r'`, then
`val_(n+n')(ν + ν') ≤ r + r'`. -/
lemma LeastValLE.add {C : CMLattice d} {μ : J → X → ℂ_[p]} {m : J → ℕ} {n n' : ℕ}
    {ν ν' : X →₀ ℕ} {r r' : ℝ} (hν : C.LeastValLE μ m n ν r)
    (hν' : C.LeastValLE μ m n' ν' r') : C.LeastValLE μ m (n + n') (ν + ν') (r + r') := by
  obtain ⟨H, hH, α, rfl, h_le⟩ := hν
  obtain ⟨H', hH', α', rfl, h_le'⟩ := hν'
  have hp : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  refine ⟨Fin.append H H', fun c ↦ ?_, Fin.append α α', by simp [Fin.sum_univ_add], ?_⟩
  · induction c using Fin.addCases <;> simp [hH, hH']
  · -- multiply the two bounds
    simp only [neg_add, Real.rpow_add hp, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
    gcongr

/-- Let `Θ = C.thetaProd μ m = ∏ θ(μ_j z) ^ m j` and `H_c ∈ C.multiSeriesRing μ` for `c < n`.
Substitute `z_c = ∑ A c k z'_k` in `∏ (H_c Θ)(z_c)`, with the `A c k` integers of `ℂ_p`. If the
coefficient of `z' ^ γ` in the result has `p`-adic valuation at most `r`, then
`C.LeastValLE μ m n ν r` holds for the degree `ν` that adds up the copies of each variable in `γ`:
some coefficient of degree `ν` in some product `∏ (H'_c Θ)(z_c)` over `n` copies `z_c` of the
variables, with `H'_c ∈ C.multiSeriesRing μ`, has valuation at most `r`. -/
lemma leastValLE_of_copySubst {C : CMLattice d} {μ : J → X → ℂ_[p]} {m : J → ℕ} {n : ℕ} {r : ℝ}
    {K : Type} [Fintype K] {A : Fin n → K → ℂ_[p]} (hA : ∀ (c : Fin n) (k : K), ‖A c k‖ ≤ 1)
    {H : Fin n → MvPowerSeries X ℂ_[p]} (hH : ∀ c : Fin n, H c ∈ C.multiSeriesRing μ)
    {γ : X × K →₀ ℕ}
    (hγ : (p : ℝ) ^ (-r) ≤ ‖coeff γ (∏ c : Fin n, copySubst (A c) (H c * C.thetaProd μ m))‖) :
    C.LeastValLE μ m n (γ.mapDomain Prod.fst) r := by
  classical
  have hp : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  let term (β : Fin n → X × K →₀ ℕ) : ℂ_[p] :=
    ∏ c, coeff (β c) (copySubst (A c) (H c * C.thetaProd μ m))
  -- one term of the sum that gives the coefficient of the product is as large as the sum
  obtain ⟨β, hβ, h_term⟩ : ∃ β ∈ finsuppAntidiag univ γ, (p : ℝ) ^ (-r) ≤ ‖term β‖ := by
    rw [coeff_prod] at hγ
    obtain h_empty | h_nonempty := (finsuppAntidiag (univ : Finset (Fin n)) γ).eq_empty_or_nonempty
    · simp [h_empty, (Real.rpow_pos_of_pos hp _).not_ge] at hγ
    obtain ⟨β, hβ, h_max⟩ :=
      IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h_nonempty fun b ↦ term b
    exact ⟨β, hβ, hγ.trans h_max⟩
  refine ⟨H, hH, fun c ↦ (β c).mapDomain Prod.fst, ?_, h_term.trans ?_⟩
  · obtain ⟨rfl, -⟩ := mem_finsuppAntidiag.1 hβ
    exact (Finsupp.mapDomain_finsetSum ..).symm
  · simp only [term, norm_prod]
    exact prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun c _ ↦ norm_coeff_copySubst_le (hA c) _ _

/-- Let `Θ = C.thetaProd μ m = ∏ θ(μ_j z) ^ m j` and `H_c ∈ C.multiSeriesRing μ` for `c < n`. If,
for integers `δ_c` of `ℂ_p`, the coefficient of `z ^ ν` in `∏ (H_c Θ)(δ_c z)` has `p`-adic valuation
at most `r`, then `C.LeastValLE μ m n ν r` holds: some coefficient of degree `ν` in some product
`∏ (H'_c Θ)(z_c)` over `n` copies `z_c` of the variables, with `H'_c ∈ C.multiSeriesRing μ`, has
valuation at most `r`. -/
lemma leastValLE_of_rescale {C : CMLattice d} {μ : J → X → ℂ_[p]} {m : J → ℕ} {n : ℕ}
    {ν : X →₀ ℕ} {r : ℝ} {δ : Fin n → ℂ_[p]} (hδ : ∀ c : Fin n, ‖δ c‖ ≤ 1)
    {H : Fin n → MvPowerSeries X ℂ_[p]} (hH : ∀ c : Fin n, H c ∈ C.multiSeriesRing μ)
    (hν : (p : ℝ) ^ (-r) ≤
      ‖coeff ν (∏ c : Fin n, (H c * C.thetaProd μ m).rescale fun _ : X ↦ δ c)‖) :
    C.LeastValLE μ m n ν r := by
  have h_deg : (ν.embDomain (Function.Embedding.sectL X ())).mapDomain Prod.fst = ν := by
    ext
    simp [mapDomain_fst_apply, ← Function.Embedding.sectL_apply]
  rw [← h_deg]
  -- substitute `z_c = δ_c z`, with a single new copy `z` of the variables
  refine leastValLE_of_copySubst (A := fun c _ ↦ δ c) (fun c _ ↦ hδ c) hH ?_
  simpa only [← coeff_killCompl, map_prod, killCompl_copySubst] using hν

/-- Let `Θ = C.thetaProd μ m = ∏ θ(μ_j z) ^ m j`. Assume `C.LeastValLE μ m n ν r`: some coefficient
of degree `ν` in some product `∏ (H_c Θ)(z_c)` over `n` copies `z_c` of the variables, for some
`H_c ∈ C.multiSeriesRing μ`, has `p`-adic valuation at most `r`. Then the same holds with each `H_c`
a monomial `∏ y(μ_j z) ^ e c j` of degree at most `|ν|`; the coefficient is the product of the
coefficients of `z ^ α c` in `H_c Θ`, and `linearSeries (μ j)` is the form `μ_j z`. -/
lemma LeastValLE.exists_monomial {C : CMLattice d} {μ : J → X → ℂ_[p]} {m : J → ℕ} {n : ℕ}
    {ν : X →₀ ℕ} {r : ℝ} (hν : C.LeastValLE μ m n ν r) :
    ∃ (α : Fin n → X →₀ ℕ) (e : Fin n → J →₀ ℕ),
      ∑ c : Fin n, α c = ν ∧
      (∀ c : Fin n, (e c).degree ≤ ν.degree) ∧
      (p : ℝ) ^ (-r) ≤ ∏ c : Fin n, ‖coeff (α c)
        ((∏ i : J, (taylorVia ιₚ C.translatedY).subst (linearSeries (μ i)) ^ e c i) *
          C.thetaProd μ m)‖ := by
  obtain ⟨H, hH, α, rfl, h_le⟩ := hν
  -- the monomial with exponents `e β` in the `y(μ_j z)`, times `Θ`, has the largest coefficient
  -- at `β`
  let y (i : J) : MvPowerSeries X ℂ_[p] := (taylorVia ιₚ C.translatedY).subst (linearSeries (μ i))
  have h_exists : ∀ β : X →₀ ℕ, ∃ e : J →₀ ℕ, e.degree ≤ β.degree ∧
      ∀ G : MvPowerSeries J (valRingCp p), ‖coeff β ((seriesToCp G).subst y * C.thetaProd μ m)‖ ≤
        ‖coeff β ((∏ i : J, y i ^ e i) * C.thetaProd μ m)‖ :=
    exists_monomial_max_norm_coeff (C.hasSubst_translatedY_subst μ) (C.thetaProd μ m)
  choose e he_deg he_max using h_exists
  refine ⟨α, fun c ↦ e (α c), rfl, fun c ↦ (he_deg _).trans ?_, h_le.trans ?_⟩
  · exact Finsupp.degree_mono (single_le_sum (f := α) (fun _ _ ↦ zero_le) (mem_univ c))
  · refine prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun c _ ↦ ?_
    obtain ⟨G, hG⟩ : ∃ G : MvPowerSeries J (valRingCp p), (seriesToCp G).subst y = H c :=
      C.mem_multiSeriesRing_iff.1 (hH c)
    simpa only [hG] using he_max (α c) G

/-- Let `θ` and `y` be the Taylor series of `C.θ` and `C.translatedY`, read in `ℂ_p` through the
place `ιₚ`, for a lattice `C` with multiplication by the integers of `ℚ(√-d)`: `C.θ` is its
normalized sigma function translated by the marked point `t` of order two, and `C.translatedY` a
combination of its Weierstrass functions at `z + t`. If `∑ δ_c ^ 2 = 0` in `ℤ_p`, then `∏ θ(δ_c z)`
is an integral series in `y`. -/
lemma prod_rescale_theta_mem [PrimeSevenModEight d] (C : CMLattice d) {n : ℕ} {δ : Fin n → ℤ_[p]}
    (hδ : ∑ c : Fin n, δ c ^ 2 = 0) :
    ∏ c : Fin n, (taylorVia ιₚ C.θ).rescale (algebraMap ℚ_[p] ℂ_[p] (δ c)) ∈
      C.integralSeriesRing := by
  -- With `θ = exp (-g)` the product is `∏ exp (δ_c ^ 2 g(z) - g(δ_c z))`.
  let η : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have hη (x : ℤ_[p]) : η x = algebraMap ℚ_[p] ℂ_[p] x := rfl
  let g : PowerSeries ℂ_[p] := C.negLogTheta
  have hg : PowerSeries.constantCoeff g = 0 := C.constantCoeff_negLogTheta
  have h_cont : Continuous fun x : ℤ_[p] ↦ (η x, η x ^ 2) := by
    simp only [hη]
    fun_prop
  -- `(x, x ^ 2)` is a limit of pairs `(k, k * k)` with `k` natural
  have h_pair (x : ℤ_[p]) : (η x, η x ^ 2) ∈ normPairClosure d :=
    PadicInt.denseRange_natCast.induction_on (p := fun x ↦ (η x, η x ^ 2) ∈ normPairClosure d) x
      (isClosed_closure.preimage h_cont) fun k ↦ subset_closure ⟨k, by simp [sq]⟩
  have h_sum : ∑ c, η (δ c) ^ 2 = 0 := by simp only [← map_pow, ← map_sum, hδ, map_zero]
  have h_prod : ∏ c, (taylorVia ιₚ C.θ).rescale (η (δ c)) =
      ∏ c, expSubst (η (δ c) ^ 2 • g - g.rescale (η (δ c))) := calc
    _ = ∏ c, expSubst (-g.rescale (η (δ c))) := by
      simp only [taylorVia_theta_eq_expSubst, ← map_neg, g,
        ← rescale_subst (show PowerSeries.constantCoeff (-g) = 0 by simp [hg])]
    _ = expSubst (∑ c, -g.rescale (η (δ c))) := (expSubst_sum fun c ↦ by simpa using hg).symm
    _ = expSubst (∑ c, (η (δ c) ^ 2 • g - g.rescale (η (δ c)))) := by
      simp [sum_sub_distrib, ← sum_smul, h_sum]
    _ = ∏ c, expSubst (η (δ c) ^ 2 • g - g.rescale (η (δ c))) := expSubst_sum fun c ↦ by simp [hg]
  simp only [← hη, h_prod]
  exact prod_mem fun c _ ↦ C.expSubst_sub_rescale_mem (h_pair (δ c))

/-- The product `∏ Θ(δ_c z)` of copies of `Θ = C.thetaProd μ m = ∏ θ(μ_j z) ^ m j` scaled by
`p`-adic integers `δ_c`, where `θ` is the Taylor series of the theta function `C.θ`, read in `ℂ_p`,
and the `μ_j z` are linear forms. -/
noncomputable def scaledThetaProd (C : CMLattice d) (μ : J → X → ℂ_[p]) (m : J → ℕ) {n : ℕ}
    (δ : Fin n → ℤ_[p]) : MvPowerSeries X ℂ_[p] :=
  ∏ c : Fin n, (C.thetaProd μ m).rescale fun _ : X ↦ algebraMap ℚ_[p] ℂ_[p] (δ c)

/-- The product `∏ Θ(δ_c z)` of the scaled copies of `Θ = ∏ θ(μ_j z) ^ m j` has constant term
`1`. -/
lemma constantCoeff_scaledThetaProd (C : CMLattice d) (μ : J → X → ℂ_[p]) (m : J → ℕ) {n : ℕ}
    (δ : Fin n → ℤ_[p]) :
    constantCoeff (C.scaledThetaProd μ m δ) = 1 := by
  rw [scaledThetaProd, map_prod]
  refine prod_eq_one fun c _ ↦ ?_
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp [constantCoeff_thetaProd]

/-- With `u(z) = ∏ θ(δ_c z)`, the product `∏ Θ(δ_c z)` of the scaled copies of
`Θ = ∏ θ(μ_j z) ^ m j` is `∏ u(μ_j z) ^ m j`. -/
lemma scaledThetaProd_eq_prod_subst (C : CMLattice d) (μ : J → X → ℂ_[p]) (m : J → ℕ) {n : ℕ}
    (δ : Fin n → ℤ_[p]) :
    C.scaledThetaProd μ m δ = ∏ i : J, PowerSeries.subst (linearSeries (μ i))
      (∏ c : Fin n, (taylorVia ιₚ C.θ).rescale (algebraMap ℚ_[p] ℂ_[p] (δ c))) ^ m i := by
  simp only [scaledThetaProd, thetaProd, map_prod, map_pow, rescale_subst_linearSeries]
  -- substitution is multiplicative; exchange the products over `c` and `j`
  simp only [← PowerSeries.coe_substAlgHom (hasSubst_linearSeries _), map_prod, ← prod_pow]
  exact prod_comm

variable [PrimeSevenModEight d]

/-- If `∑ δ_c ^ 2 = 0` in `ℤ_p`, then the product `C.scaledThetaProd μ m δ = ∏ Θ(δ_c z)` of the
scaled copies of `Θ = ∏ θ(μ_j z) ^ m j` lies in `C.multiSeriesRing μ`.

Here `C` is a lattice in `ℂ` with multiplication by the integers of `ℚ(√-d)`, for a prime
`d ≡ 7 (mod 8)`, and with a marked point `t` of order two. The series `θ` and `y` are the Taylor
series at `0`, read in `ℂ_p` through the embedding `ιₚ` of `ℂ`, of `C.θ` (the twisted translate by
`t` of the sigma function, with value `1` at `0`) and of `C.translatedY` (the function
`(℘'(z + t) - a₁ (℘(z + t) - ℘(t))) / 2`, where `a₁² = 12 ℘(t)`). The `μ_j z = ∑ μ j x * z_x`, for
`j : J`, are linear forms in the variables `z_x`, for `x : X`, and `C.multiSeriesRing μ` is the ring
of power series in the `y(μ_j z)` with coefficients in the integers of `ℂ_p`. -/
lemma scaledThetaProd_mem (C : CMLattice d) (μ : J → X → ℂ_[p]) (m : J → ℕ) {n : ℕ}
    {δ : Fin n → ℤ_[p]} (hδ : ∑ c : Fin n, δ c ^ 2 = 0) :
    C.scaledThetaProd μ m δ ∈ C.multiSeriesRing μ := by
  rw [scaledThetaProd_eq_prod_subst]
  exact prod_mem fun i _ ↦ pow_mem (subst_mem_multiSeriesRing μ (C.prod_rescale_theta_mem hδ) i) _

/-- If `∑ δ_c ^ 2 = 0` in `ℤ_p`, then the product `C.scaledThetaProd μ m δ = ∏ Θ(δ_c z)` of the
scaled copies of `Θ = ∏ θ(μ_j z) ^ m j` has an inverse in `C.multiSeriesRing μ`. -/
lemma exists_scaledThetaProd_mul_eq_one (C : CMLattice d) (μ : J → X → ℂ_[p]) (m : J → ℕ) {n : ℕ}
    {δ : Fin n → ℤ_[p]} (hδ : ∑ c : Fin n, δ c ^ 2 = 0) :
    ∃ V ∈ C.multiSeriesRing μ, C.scaledThetaProd μ m δ * V = 1 := by
  -- invert `u(z) = ∏ θ(δ_c z)` in one variable, put `μ_j z` for `z` and multiply over `j`
  rw [scaledThetaProd_eq_prod_subst]
  set u : PowerSeries ℂ_[p] :=
    ∏ c : Fin n, (taylorVia ιₚ C.θ).rescale (algebraMap ℚ_[p] ℂ_[p] (δ c)) with hu_def
  have hu : u ∈ C.integralSeriesRing := C.prod_rescale_theta_mem hδ
  have hu₀ : PowerSeries.constantCoeff u = 1 := by simp [hu_def]
  obtain ⟨v, hv, huv⟩ : ∃ v ∈ C.integralSeriesRing, u * v = 1 :=
    C.isSeriesGenerator_translatedY.exists_mul_eq_one hu (by simp [hu₀])
  have h_mul (i : J) : u.subst (linearSeries (μ i)) * v.subst (linearSeries (μ i)) = 1 := by
    rw [← PowerSeries.coe_substAlgHom (hasSubst_linearSeries _), ← map_mul, huv, map_one]
  refine ⟨∏ i : J, v.subst (linearSeries (μ i)) ^ m i,
    prod_mem fun i _ ↦ pow_mem (subst_mem_multiSeriesRing μ hv i) _, ?_⟩
  simp only [← prod_mul_distrib, ← mul_pow, h_mul, one_pow, prod_const_one]

/-- There are six `p`-adic integers `δ 0 = 1, δ 1, …, δ 5` such that the product
`C.scaledThetaProd μ m δ` of the scaled copies `Θ(δ_c z)` of `Θ = ∏ θ(μ_j z) ^ m j` is a unit of
`C.multiSeriesRing μ` with constant term `1`. -/
lemma exists_scaledThetaProd_mem_mul_eq_one (C : CMLattice d) (μ : J → X → ℂ_[p]) (m : J → ℕ) :
    ∃ δ : Fin 6 → ℤ_[p], δ 0 = 1 ∧
    C.scaledThetaProd μ m δ ∈ C.multiSeriesRing μ ∧
    (∃ V ∈ C.multiSeriesRing μ, C.scaledThetaProd μ m δ * V = 1) ∧
    constantCoeff (C.scaledThetaProd μ m δ) = 1 := by
  -- the squares of `1`, four numbers with square sum `-1`, and `0` add up to zero
  obtain ⟨a, ha⟩ : ∃ a : Fin 4 → ℤ_[p], ∑ i : Fin 4, a i ^ 2 = -1 := padicInt_sum_four_squares _
  let δ : Fin 6 → ℤ_[p] := ![1, a 0, a 1, a 2, a 3, 0]
  have hδ : ∑ c : Fin 6, δ c ^ 2 = 0 := by
    rw [Fin.sum_univ_four] at ha
    simp only [δ, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    linear_combination ha
  exact ⟨δ, rfl, C.scaledThetaProd_mem μ m hδ, C.exists_scaledThetaProd_mul_eq_one μ m hδ,
    C.constantCoeff_scaledThetaProd μ m δ⟩

/-- If one of the forms `μ_j` has unit coefficients, then `val₆(ν) ≤ γ_p |ν| - v(ν!)`: some
coefficient of degree `ν` in some product `∏ (H_c Θ)(z_c)` over six copies `z_c` of the variables,
with `Θ = C.thetaProd μ m = ∏ θ(μ_j z) ^ m j` and `H_c ∈ C.multiSeriesRing μ`, has valuation at most
`γ_p |ν| - v(ν!)`. The letter `v` is the `p`-adic valuation, `ν! = ∏ (ν x)!`, and
`γ_p = gammaPrime d p` is `0`, `p / (p² - 1)`, `1 / (2 p - 2)` when `p` is split, inert, ramified in
`ℚ(√-d)`. -/
lemma leastValLE_of_unit_coefficients (C : CMLattice d) {μ : J → X → ℂ_[p]} (m : J → ℕ) {i₀ : J}
    (h_unit : ∀ x : X, ‖μ i₀ x‖ = 1) (ν : X →₀ ℕ) :
    C.LeastValLE μ m 6 ν
      (gammaPrime d p * ν.degree - ∑ x : X, (padicValNat p (ν x)! : ℝ)) := by
  have hp : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  obtain ⟨g, hg, hg_deriv⟩ := C.katz_divisibility_limit (p := p) ν.degree
  -- `δ 0 = 1`, and `V` is an inverse of `∏ Θ(δ_c z)` in `C.multiSeriesRing μ`
  obtain ⟨δ, hδ₀, -, ⟨V, hV, hV_inv⟩, -⟩ := C.exists_scaledThetaProd_mem_mul_eq_one μ m
  let G : MvPowerSeries X ℂ_[p] := g.subst (linearSeries (μ i₀))
  -- `H 0` is `G = g(μ_(i₀) z)` divided by the unit `∏ Θ(δ_c z)`, and `H c = 1` for `c ≠ 0`
  let H : Fin 6 → MvPowerSeries X ℂ_[p] := Fin.cons (G * V) 1
  have hH (c : Fin 6) : H c ∈ C.multiSeriesRing μ :=
    c.cases (mul_mem (subst_mem_multiSeriesRing μ hg i₀) hV) fun _ ↦ one_mem _
  have h_prod :
      ∏ c, (H c * C.thetaProd μ m).rescale (fun _ ↦ algebraMap ℚ_[p] ℂ_[p] (δ c)) = G := by
    simp only [map_mul, prod_mul_distrib]
    rw [← scaledThetaProd]
    -- only `H 0` contributes, as `G * V`
    simp [H, Fin.prod_univ_succ, hδ₀, ← Pi.one_def, mul_assoc, mul_comm V, hV_inv]
  refine leastValLE_of_rescale (δ := fun c ↦ algebraMap ℚ_[p] ℂ_[p] (δ c))
    (fun c ↦ by simpa using (δ c).norm_le_one) hH ?_
  rw [h_prod]
  set vFactorial : ℝ := ∑ x : X, (padicValNat p (ν x)! : ℝ) with hv_factorial
  calc (p : ℝ) ^ (-(gammaPrime d p * ν.degree - vFactorial))
      = ((p : ℝ) ^ (-gammaPrime d p)) ^ ν.degree * p ^ vFactorial := by
        rw [← Real.rpow_mul_natCast hp.le, ← Real.rpow_add hp]
        ring_nf
    _ ≤ ‖(ν.degree ! * g.coeff ν.degree : ℂ_[p])‖ * p ^ vFactorial := by grw [hg_deriv]
    _ = ‖coeff ν G‖ := by
        -- the coefficient is a unit times the `|ν|`-th derivative of `g` at `0`, divided by `ν!`
        simp [G, hv_factorial, coeff_subst_linearSeries, h_unit,
          norm_natCast_eq_inv_pow_padicValNat, factorial_ne_zero, prod_pow_eq_pow_sum, ← cast_sum,
          div_eq_mul_inv]

/-- If each coordinate `z_x`, up to a unit `s`, is a combination `∑ a x j • μ_j z` with coefficients
in the ring `valRingCp p` of integers of `ℂ_p`, then `val₆(ν) ≤ 0` in every degree `ν`: some
coefficient of degree `ν` in some product `∏ (H_c Θ)(z_c)` over six copies `z_c` of the variables,
with `Θ = C.thetaProd μ m = ∏ θ(μ_j z) ^ m j` and `H_c ∈ C.multiSeriesRing μ`, has `p`-adic
valuation at most `0`. -/
lemma leastValLE_zero_of_span [DecidableEq X] (C : CMLattice d) {μ : J → X → ℂ_[p]}
    (m : J → ℕ) {a : X → J → valRingCp p} {s : ℂ_[p]} (hs : ‖s‖ = 1)
    (ha : ∀ x x' : X, ∑ i : J, (a x i : ℂ_[p]) * μ i x' = if x = x' then s else 0) (ν : X →₀ ℕ) :
    C.LeastValLE μ m 6 ν 0 := by
  let y : PowerSeries ℂ_[p] := taylorVia ιₚ C.translatedY
  have hy_const : y.constantCoeff = 0 := C.isSeriesGenerator_translatedY.constantCoeff_eq_zero
  have hy_linear : y.coeff 1 = 1 := C.isSeriesGenerator_translatedY.coeff_one
  -- the series `G x = ∑ a x i • y(μ_i z)` begins with `∑ a x i • μ_i z = s z_x`
  let G (x : X) : MvPowerSeries X ℂ_[p] := ∑ i, (a x i : ℂ_[p]) • y.subst (linearSeries (μ i))
  have hG_mem (x : X) : G x ∈ C.multiSeriesRing μ := sum_mem fun i _ ↦ by
    -- by definition, the ring contains the constants of the valuation ring
    have h_const : MvPowerSeries.C (a x i : ℂ_[p]) ∈ C.multiSeriesRing μ := ⟨.C (a x i), by simp⟩
    rw [smul_eq_C_mul]
    exact mul_mem h_const
      (subst_mem_multiSeriesRing μ C.isSeriesGenerator_translatedY.generator_mem i)
  have hG_low (x : X) : IsLowestTerm (fun _ ↦ 1) (G x) (.single x 1) s := by
    intro β hβ
    obtain h_zero | h_one := le_one_iff_eq_zero_or_eq_one.1
      (by simpa [← Finsupp.degree_eq_weight_one] using hβ : β.degree ≤ 1)
    · obtain rfl : β = 0 := β.degree_eq_zero_iff.1 h_zero
      simp [G, hy_const, coeff_monomial, eq_comm]
    · obtain ⟨x', rfl⟩ : ∃ x', β = .single x' 1 := (Finsupp.sum_eq_one_iff β).1 h_one
      -- by `ha`, the linear term of `G x` is `s z_x`
      simp [G, coeff_subst_linearSeries, hy_linear, coeff_monomial, Finsupp.single_apply, ha,
        Finsupp.single_left_inj, eq_comm, apply_ite factorial]
  have h_low : IsLowestTerm (fun _ ↦ 1) ((∏ x, G x ^ ν x) * C.thetaProd μ m) ν (∏ x, s ^ ν x) := by
    simpa using (IsLowestTerm.prod (s := univ) fun x _ ↦ (hG_low x).pow (ν x)).mul
      (C.isLowestTerm_thetaProd μ m)
  -- one copy has a unit coefficient at `ν`; the other five are taken in degree `0`
  have h_one_copy : C.LeastValLE μ m 1 ν 0 := ⟨fun _ ↦ ∏ x, G x ^ ν x,
    fun _ ↦ prod_mem fun x _ ↦ pow_mem (hG_mem x) _, fun _ ↦ ν, by simp,
    by simp [h_low ν le_rfl, hs]⟩
  simpa using h_one_copy.add (leastValLE_zero (n := 5))

/-- If the coefficients of the forms `μ_j` are integers of `ℂ_p` and `ϖ` has `p`-adic valuation at
least `ρ_p = varpiValuation d p`, then a series `H ∈ C.multiSeriesRing μ` has integral coefficients
after the scaling `z ↦ ϖ z`: the result is in the range of `seriesToCp`, the inclusion of series
over the integers of `ℂ_p`. -/
lemma rescale_mem_range_seriesToCp_of_mem_multiSeriesRing (C : CMLattice d) {μ : J → X → ℂ_[p]}
    (hμ : ∀ (i : J) (x : X), ‖μ i x‖ ≤ 1) {ϖ : ℂ_[p]} (hϖ : ‖ϖ‖ ≤ p ^ (-varpiValuation d p))
    {H : MvPowerSeries X ℂ_[p]} (hH : H ∈ C.multiSeriesRing μ) :
    H.rescale (fun _ : X ↦ ϖ) ∈ seriesToCp.range := by
  obtain ⟨g, rfl⟩ := hH
  obtain ⟨y₀, hy₀⟩ :=
    C.rescale_mem_range_seriesToCp hϖ C.isSeriesGenerator_translatedY.generator_mem
  -- `y₀` is the integral series `y(ϖ z)`, so `y(μ_i ϖ z)` is the integral series `Y i`
  let Y (i : J) : MvPowerSeries X (valRingCp p) :=
    PowerSeries.subst (linearSeries fun x ↦ (⟨μ i x, hμ i x⟩ : valRingCp p)) y₀
  have hY (i : J) : seriesToCp (Y i) =
      ((taylorVia ιₚ C.translatedY).subst (linearSeries (μ i))).rescale fun _ ↦ ϖ := by
    rw [rescale_subst_linearSeries, ← hy₀, PowerSeries.map_subst (hasSubst_linearSeries _)]
    simp [linearSeries, smul_eq_C_mul, PowerSeries.map]
  have hY₀ (i : J) : constantCoeff (Y i) = 0 := Subtype.ext <|
    show constantCoeff (seriesToCp (Y i)) = 0 by simp [hY, rescale_subst_linearSeries]
  refine ⟨g.subst Y, ?_⟩
  -- both sides substitute the series `y(μ_i ϖ z)` into `g`
  rw [map_subst (hasSubst_of_constantCoeff_zero hY₀), RingHom.comp_apply]
  simp only [hY, rescale_eq_subst, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom]
  -- the two substituted families agree by definition of composition
  exact (subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun i ↦ by simp) (.smul_X _) _).symm

end CMLattice

end New

end LeastValuation
