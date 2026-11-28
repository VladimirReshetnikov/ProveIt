import Lib.CM.Sigma.Basic
import Lib.GLn.SchurModule.Basic
import Lib.General.Algebra.AdicCompletion

/-!
# Integral power series over ℂ_p: jets, the chain rule and the exponential

A power series over `ℂ_[p]` is called integral if it comes, through `New.seriesToCp`, from a series
with coefficients in the ring of integers of `ℂ_[p]`.

## Main definitions and results

* `New.mem_range_seriesToCp`: a series in one variable is integral iff all its coefficients have
  norm at most one.
* `New.pderiv_subst`: the chain rule for partial derivatives of a substitution of power series.
* `New.jet_subst_linearSeries`: for a linear substitution `M`, the jet `P(∂) (F ∘ M) (0)` is the jet
  of `F` along the polynomial `New.linSubst M P` obtained from `P` by the transposed substitution.
* `New.expSubst`: the exponential `exp a` of a power series `a` in several variables without
  constant term; it turns finite sums into products (`New.expSubst_add`, `New.expSubst_sum`).
* `New.padicValNat_factorial_mem_Icc`: `n / (p - 1) - v_p(n!)` lies in `[0, K]` for `n < p ^ K`.
* `New.rpow_le_norm_factorial`: the lower bound `p ^ (-n / (p - 1)) ≤ ‖n!‖` for the `p`-adic norm.

Notions from other files:
* `New.jet`: the bilinear pairing `P(∂)F(0)` of a polynomial `P` with a power series `F`, the sum
  over exponents `d` of `d!` times the product of the `d`-th coefficients of `P` and `F`.
* `New.linearSeries`: the linear form `∑ c_i z_i`, as a power series in the variables `z_i`.
* `New.linSubst`: for a matrix `M` over `R`, the `R`-algebra map of polynomial rings that sends
  `X_b` to `∑_t M_(t b) X_t`.

## Relation to the literature

Known results: the chain rule and the functional equation of the exponential for formal power
series, and Legendre's formula for the valuation of a factorial.
-/

/-! ## The inclusion of integral power series -/

section PadicSeriesDefs

variable {p : ℕ} [Fact p.Prime] {σ : Type}

/-- The inclusion of power series over the integers `valRingCp p` into power series over `ℂ_[p]`, as
a ring homomorphism. -/
noncomputable abbrev New.seriesToCp : MvPowerSeries σ (valRingCp p) →+* MvPowerSeries σ ℂ_[p] :=
  MvPowerSeries.map (σ := σ) (valRingCp p).subtype

@[simp]
lemma New.seriesToCp_smul (k : valRingCp p) (f : MvPowerSeries σ (valRingCp p)) :
    seriesToCp (p := p) (σ := σ) (k • f) = (k : ℂ_[p]) • seriesToCp f :=
  rfl

end PadicSeriesDefs

/-! ## Integral series, units, partial derivatives and linear forms -/

section IntegralSeries

open MvPowerSeries PowerSeries

namespace New

variable {σ : Type*} {R S : Type*} [CommRing R] [CommRing S] {p : ℕ} [Fact p.Prime]

/-- A power series `f` in one variable over `ℂ_[p]` comes from a series over the ring of integers
`valRingCp p` if and only if all its coefficients have norm at most one. -/
lemma mem_range_seriesToCp {f : ℂ_[p]⟦X⟧} :
    f ∈ seriesToCp.range ↔ ∀ n : ℕ, ‖f.coeff n‖ ≤ 1 := by
  constructor
  · rintro ⟨g, rfl⟩ n
    exact (g.coeff (Finsupp.single () n)).property
  · intro hf
    have h_mem (d : Unit →₀ ℕ) : f d ∈ valRingCp p := by
      rw [d.unique_single]
      exact hf (d ())
    exact ⟨fun d ↦ ⟨f d, h_mem d⟩, rfl⟩

lemma map_pderiv (Ψ : R →+* S) (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map Ψ (pderiv i f) = pderiv i (MvPowerSeries.map Ψ f) := by
  ext
  simp [coeff_pderiv]

@[simp]
lemma isUnit_integer_iff_norm_eq_one {c : valRingCp p} : IsUnit c ↔ ‖(c : ℂ_[p])‖ = 1 :=
  Valued.integer.isUnit_iff_norm_eq_one

@[simp]
lemma constantCoeff_linearSeries [Fintype σ] (c : σ → R) :
    MvPowerSeries.constantCoeff (linearSeries c) = 0 := by
  simp [linearSeries]

end New

end IntegralSeries

/-! ## The chain rule and jets of linear substitutions -/

section JetChainRule

open MvPowerSeries Finset WithPiTopology


/-- Partial derivatives of power series are continuous for the coefficientwise topology. -/
lemma New.continuous_pderiv_of_continuousMul {σ R : Type*} [CommRing R] [TopologicalSpace R]
    [ContinuousMul R] (i : σ) : Continuous (pderiv (R := R) i) := by
  refine continuous_pi fun d ↦ ?_
  change Continuous fun F : MvPowerSeries σ R ↦ coeff d (pderiv i F)
  simp only [coeff_pderiv]
  exact (continuous_coeff R _).mul continuous_const

variable {ι : Type _} {κ : Type _} {R : Type _} [CommRing R] [Fintype ι] in
/-- The chain rule for power series: if the family `a` can be substituted into series in the
variables `ι`, then `∂_k F(a) = ∑_i (∂_i F)(a) * ∂_k a_i`. -/
@[simp]
lemma New.pderiv_subst {a : ι → MvPowerSeries κ R} (ha : HasSubst a) (k : κ)
    (F : MvPowerSeries ι R) :
    pderiv k (subst a F) = ∑ i : ι, (pderiv i F).subst a * pderiv k (a i) := by
  classical
  -- With the discrete topology on `R` both sides are continuous in `F` and polynomials are dense,
  -- so it suffices to prove the chain rule for polynomials.
  let : UniformSpace R := ⊥
  have h_cont : Continuous (subst (R := R) a) := continuous_subst ha
  refine denseRange_toMvPowerSeries.induction_on F ?_ fun Q ↦ ?_
  · have h_pderiv (i : ι) : Continuous (pderiv (R := R) i) := continuous_pderiv_of_continuousMul i
    exact isClosed_eq ((continuous_pderiv_of_continuousMul k).comp h_cont) (by fun_prop)
  · simp only [subst_coe, pderiv_coe]
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp [hP, hQ, add_mul, sum_add_distrib]
    | mul_X P i hP =>
      -- the Leibniz rule on both sides
      simp [hP, add_mul, sum_add_distrib, mul_sum, apply_ite, mul_assoc, Pi.single_apply]

/-- Jets of a linear substitution. Let `M` be a matrix and substitute the linear forms
`(M z)_i = ∑_k M_(i k) z_k` into the series `F`. The jet `P(∂) F(M z) (0)` equals the jet of `F`
along `linSubst M P`, the polynomial `P(Mᵀ x)`. -/
lemma New.jet_subst_linearSeries {ι κ R : Type} [CommRing R] [Fintype ι] [Fintype κ]
    (M : Matrix ι κ R) (P : MvPolynomial κ R) :
    ∀ F : MvPowerSeries ι R,
      jet R P (subst (fun i : ι ↦ linearSeries (M i)) F) = jet R (linSubst M P) F := by
  classical
  have hM : HasSubst fun i : ι ↦ linearSeries (M i) :=
    hasSubst_of_constantCoeff_zero fun i ↦ constantCoeff_linearSeries (M i)
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro F
    have h_const : constantCoeff (subst (fun i : ι ↦ linearSeries (M i)) F) = constantCoeff F := by
      rw [constantCoeff_subst hM, finsum_eq_single _ 0 fun d hd ↦ ?_]
      · simp
      obtain ⟨i, hi⟩ : ∃ i : ι, d i ≠ 0 := Finsupp.ne_iff.1 hd
      simp [Finsupp.prod_fintype, prod_eq_zero (mem_univ i), hi]
    simp [jet_eq_sum, h_const]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P k hP =>
    intro F
    -- A factor `X k` acts on the series as `∂_k`, and the chain rule moves the derivative inside.
    have h_chain : pderiv k (subst (fun i : ι ↦ linearSeries (M i)) F) =
        ∑ i : ι, M i k • subst (fun i : ι ↦ linearSeries (M i)) (pderiv i F) := by
      rw [pderiv_subst hM]
      simp [linearSeries, pderiv_X, Pi.single_apply]
    have h_lin : linSubst M (P * .X k) = ∑ i : ι, M i k • (linSubst M P * .X i) := by
      simp [linSubst, mul_sum]
    simp only [h_lin, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, jet_mul_X,
      h_chain, hP]

end JetChainRule

/-! ## The exponential of a series and p-adic norms of factorials -/

section PadicExp

open PowerSeries Nat List

namespace New

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type*}

/-- The series `exp a`, obtained by substituting `a` into the exponential series over `ℂ_[p]`. It is
meaningful when `a` has no constant term. -/
noncomputable abbrev expSubst (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  (exp ℂ_[p]).subst a

/-- Substituting a series `a` without constant term into `f` keeps the constant term of `f`. -/
@[simp]
lemma constantCoeff_subst_of_constantCoeff_eq_zero (a : MvPowerSeries σ ℂ_[p])
    (ha : a.constantCoeff = 0) (f : ℂ_[p]⟦X⟧) :
    (subst a f).constantCoeff = constantCoeff f := by
  rw [constantCoeff_subst (.of_constantCoeff_zero ha),
    finsum_eq_single _ 0 fun d hd ↦ by simp [ha, hd]]
  simp

/-- The functional equation `exp (a + b) = exp a * exp b` for series `a`, `b` without constant
term. -/
lemma expSubst_add (a : MvPowerSeries σ ℂ_[p]) {b : MvPowerSeries σ ℂ_[p]}
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) :
    expSubst (a + b) = expSubst a * expSubst b := by
  -- The universal case in two variables: `exp (X 0 + X 1) = exp (X 0) * exp (X 1)`.
  have h_univ : expSubst (.X 0 + .X 1 : MvPowerSeries (Fin 2) ℂ_[p]) =
      expSubst (.X 0) * expSubst (.X 1) := by
    ext e
    -- The coefficients agree: `(m + n).choose m / (m + n)! = 1 / m! * (1 / n!)`.
    rw [coeff_subst_X_zero_add_X_one, coeff_subst_X_zero_subst_mul_X_one]
    simp [cast_add_choose]
    field [factorial_ne_zero]
  -- Substituting `a` for `X 0` and `b` for `X 1` commutes with the exponential.
  have hab : MvPowerSeries.HasSubst ![a, b] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp [ha, hb])
  have h_comm (F : MvPowerSeries (Fin 2) ℂ_[p]) (hF : F.constantCoeff = 0) :
      (expSubst F).subst ![a, b] = expSubst (F.subst ![a, b]) :=
    -- `PowerSeries.subst` is `MvPowerSeries.subst` for a family indexed by `Unit`
    MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero hF).const hab _
  simpa [MvPowerSeries.subst_add hab, MvPowerSeries.subst_mul hab, h_comm,
    MvPowerSeries.subst_X hab] using congrArg (MvPowerSeries.subst ![a, b]) h_univ

/-- The exponential of a finite sum of series without constant term is the product of their
exponentials. -/
lemma expSubst_sum {I : Type*} {t : Finset I} {a : I → MvPowerSeries σ ℂ_[p]}
    (h_const : ∀ i : I, (a i).constantCoeff = 0) :
    expSubst (t.sum a) = ∏ i ∈ t, expSubst (a i) := by
  induction t using Finset.cons_induction with
  | empty => simp [subst_zero_eq_C_constantCoeff]
  | cons i t hi ih => simp [expSubst_add _ (h_const i), h_const, ih]

/-- The norm of a nonzero natural number `n` in `ℂ_[p]` is `p ^ (-v_p(n))`. -/
lemma norm_natCast_eq_inv_pow_padicValNat {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℂ_[p])‖ = (p : ℝ)⁻¹ ^ padicValNat p n := by
  simpa [Padic.norm_eq_zpow_neg_valuation, hn] using PadicComplex.norm_extends' p n

/-- For `p` prime and `n < p ^ K` one has `n / (p - 1) - K ≤ v_p(n!) ≤ n / (p - 1)`, a consequence
of Legendre's formula. -/
lemma padicValNat_factorial_mem_Icc {n K : ℕ} (hn : n < p ^ K) :
    (padicValNat p n ! : ℝ) ∈ Set.Icc ((n : ℝ) / (p - 1) - K) (n / (p - 1)) := by
  -- By Legendre's formula `n - (p - 1) * v_p(n!)` is the sum of the base `p` digits of `n`. There
  -- are at most `K` digits, each at most `p - 1`.
  have hp1 : 1 < p := hp.out.one_lt
  have legendre : (p - 1) * padicValNat p n ! + (p.digits n).sum = n := by
    rw [sub_one_mul_padicValNat_factorial, Nat.sub_add_cancel (digit_sum_le p n)]
  have digit_le : ∀ d ∈ p.digits n, d ≤ p - 1 :=
    fun d hd ↦ le_sub_one_of_lt (digits_lt_base hp1 hd)
  have sum_le : (p.digits n).sum ≤ K * (p - 1) :=
    calc (p.digits n).sum ≤ (p.digits n).length * (p - 1) := sum_le_length_nsmul _ _ digit_le
      _ ≤ K * (p - 1) := Nat.mul_le_mul_right _ ((digits_length_le_iff hp1 n).2 hn)
  have lower : n ≤ (p - 1) * (padicValNat p n ! + K) := by grind
  have upper : (p - 1) * padicValNat p n ! ≤ n := by omega
  have h_pos : (0 : ℝ) < (p - 1 : ℕ) := cast_pos.2 (Nat.sub_pos_of_lt hp1)
  rw [Set.mem_Icc, sub_le_iff_le_add, ← cast_pred hp.out.pos, div_le_iff₀' h_pos,
    le_div_iff₀' h_pos]
  exact_mod_cast And.intro lower upper

/-- For a prime `p` and a natural number `n`, the norm of `n !` in the `p`-adic complex numbers
`ℂ_[p]` is at least `p ^ (-(n / (p - 1)))`, where the exponent is a real number. -/
lemma rpow_le_norm_factorial {n : ℕ} : p ^ (-(n / (p - 1)) : ℝ) ≤ ‖(n ! : ℂ_[p])‖ := by
  have h_val : (padicValNat p n ! : ℝ) ≤ n / (p - 1) :=
    (padicValNat_factorial_mem_Icc (n.lt_pow_self hp.out.one_lt)).2
  calc (p : ℝ) ^ (-(n / (p - 1)) : ℝ) ≤ p ^ (-(padicValNat p n ! : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (mod_cast hp.out.one_le) (neg_le_neg h_val)
    _ = ‖(n ! : ℂ_[p])‖ := by simp [norm_natCast_eq_inv_pow_padicValNat n.factorial_ne_zero]

/-- Substituting `a` into the rescaled series `f(c X)` is substituting `c • a` into `f`. -/
@[simp]
lemma subst_rescale_eq_subst_smul {c : ℂ_[p]} (a : MvPowerSeries σ ℂ_[p]) (ha : HasSubst a)
    (f : ℂ_[p]⟦X⟧) :
    (rescale c f).subst a = f.subst (c • a) := by
  rw [rescale_eq_subst, subst_comp_subst_apply (.smul_X' c) ha, subst_smul ha, subst_X ha]

end New

end PadicExp

/-! ## Renaming the variables of a jet -/

section JetRename

open MvPolynomial Finsupp

/-- The jet pairing `P(∂)F(0)` of a polynomial `P` with a power series `F` is unchanged when both
are renamed along an injective map `e` of variables; `Q` is the renamed polynomial. -/
lemma New.jet_rename {σ τ R : Type} (e : σ ↪ τ) [CommRing R] {P : MvPolynomial σ R}
    {Q : MvPolynomial τ R} (h : rename e P = Q) (F : MvPowerSeries σ R) :
    jet R Q (F.rename e) = jet R P F := by
  subst h
  induction P using MvPolynomial.induction_on' with
  | monomial d r => simp [rename_monomial, ← embDomain_eq_mapDomain, prod, jet_monomial]
  | add P Q hP hQ => simp [hP, hQ]

end JetRename
