import Lib.Weil.DualPair.WeilAction

/-!
# The jet matrix of a definite pair is a kernel for algebraic forms

An abstract theta kernel is an action of `G × G'` on a space of data, with a jet matrix for each
datum that is equivariant for the rational points. Such a kernel lifts algebraic forms from rank `n`
to rank `n'`.

* `New.IsLiftWeight`: the condition on ranks and weights under which the lift exists.
* `New.Kernel`: the abstract theta kernel.
* `New.Kernel.lift`, `New.Kernel.lift_equivariant`: the theta lift of a kernel and its equivariance
  under `G × G'`.
* `New.schurCoeffPoly`: the polynomial `Aᵀ S(z) ξ`, with `S = schur κ`.
  `New.dotProduct_schurJet_mulVec` writes the entries of the jet matrix as jets along it.
  `New.realPairWeil_schurCoeffPoly` gives the action of the real points on it, and
  `New.theta_pairWeil_schurCoeffPoly` its theta function as a coefficient of the jet matrix.
* `New.thetaKernel`: the kernel of the definite pair, which sends `f` to
  `schurJet κ (jetSeries _ c f)`.

Notions from other files:
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.Space.finitePart`: The finite part 𝒮_f: the subspace of 𝒮(V) spanned by the translates of the
  vacuum under the finite Heisenberg operators `New.Space.finHeisenbergOp`.
* `New.rightStabilizer`: The subgroup of k in G with f(gk) = f(g) for all g.
* `New.AlgForm`: Smooth algebraic forms of weight (κ, e): functions φ on G_f with values in vectors
  indexed by `New.WeylIndex n κ`, with φ(γg) = ρ(γ)φ(g) for rational γ and an open stabiliser.
* `New.schurJet`: The matrix of jets of a power series along the entries of `schur κ`.

## Relation to the literature

Known; see `Lib.Weil.CompactLift.DefiniteThetaLift` for sources.
-/

noncomputable section

namespace New

open NumberField Matrix MvPolynomial Space Fock Finset GeneralLinearGroup G Fintype Subgroup

/-- Scaling the variables of a complex polynomial by `t` scales the coefficient of a monomial
by `t` to the power of its degree. -/
lemma coeff_aeval_smul_X {σ : Type*} (Q : MvPolynomial σ ℂ) (t : ℂ) (m : σ →₀ ℕ) :
    (Q.aeval fun x : σ ↦ t • X x : MvPolynomial σ ℂ).coeff m = t ^ m.degree * Q.coeff m := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u r =>
    have h_mon : (monomial u r).aeval (fun x ↦ t • X x) = t ^ u.degree • monomial u r := by
      rw [aeval_monomial, monomial_eq]
      simp [Finsupp.prod, smul_pow, prod_smul, prod_pow_eq_pow_sum, Finsupp.degree_apply,
        -prod_X_pow_eq_monomial]
    classical
    rw [h_mon]
    by_cases h : u = m <;> simp [h]
  | add p q hp hq => simp [hp, hq, mul_add, -aeval_eq_bind₁]

/-- A complex polynomial is homogeneous of degree `d` exactly when multiplying the variables by
any `t ≠ 0` multiplies it by `t ^ d`. -/
lemma isHomogeneous_iff_aeval_smul_X {σ : Type*} {Q : MvPolynomial σ ℂ} {d : ℕ} :
    Q.IsHomogeneous d ↔ ∀ t : ℂ, t ≠ 0 → Q.aeval (fun x : σ ↦ t • X x) = t ^ d • Q := by
  refine ⟨fun hQ t _ ↦ ?_, fun hQ m hm ↦ ?_⟩
  · ext m
    rw [coeff_aeval_smul_X, coeff_smul, smul_eq_mul]
    by_cases h : m.degree = d
    · rw [h]
    · simp [hQ.coeff_eq_zero h]
  · -- Compare the coefficients at `m` for `t = 2`.
    have h_pow : (2 : ℂ) ^ m.degree = 2 ^ d := mul_right_cancel₀ hm <| by
      rw [← coeff_aeval_smul_X, hQ 2 two_ne_zero, coeff_smul, smul_eq_mul]
    rw [Finsupp.degree_eq_weight_one] at h_pow
    exact Nat.pow_right_injective le_rfl (mod_cast h_pow)

/-- The weight `(κ, e)` of rank `n` goes up to rank `n'` along the exponent `eb`. Here `κ τ h` is
the number of columns of height `h` at the place `τ`. There are three conditions: no column has
height strictly between `card n` and `card n'`, and `card n ≤ card n'` (`New.FitsRanks`); the
rank grows, `card n < card n'`; and `e τ = eb τ + κ τ (card n)`, since in rank `n` the columns of
height `card n` give a power of the determinant, whose exponent is added to `eb τ`. -/
def IsLiftWeight {Φ : Type} (n n' : Type) [Fintype n] [Fintype n'] (κ : Φ → ℕ → ℕ) (eb e : Φ → ℤ) :
    Prop :=
  -- `FitsRanks`: no column has a height strictly between the two ranks, and `card n ≤ card n'`.
  FitsRanks (fun _ ↦ n) (fun _ ↦ n') κ ∧
  Fintype.card n < Fintype.card n' ∧
  -- The columns of height `card n` are added to the exponent of the determinant.
  e = fun τ ↦ eb τ + κ τ (Fintype.card n)

section

variable {E n n' : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {κ : InfinitePlace E → ℕ → ℕ} {eb e : InfinitePlace E → ℤ}
  (V : Space E n s) (T : Space E n' s') (a b : AutChar E) (ea : InfinitePlace E → ℤ)
  (A : WeylIndex n' κ → ℂ) (ξ : WeylIndex n κ → ℂ)

/-! ### The Fock polynomial and the finite Weil representation -/

/-- For a covector A and a vector ξ, the polynomial Aᵀ S_κ(z) ξ in the entries of the n′ × n
matrices z_τ, one for each infinite place τ, where S_κ = `schur κ`. S_κ(z) has rows indexed by
`WeylIndex n' κ` and columns by `WeylIndex n κ`, and its entries are polynomials in the z_τ. -/
def schurCoeffPoly {E : Type} [Field E] [NumberField E] {κ : InfinitePlace E → ℕ → ℕ}
    (A : WeylIndex n' κ → ℂ) (ξ : WeylIndex n κ → ℂ) : MvPolynomial (InfinitePlace E × n' × n) ℂ :=
  C ∘ A ⬝ᵥ schur κ (fun τ : InfinitePlace E ↦ of fun (b : n') (c : n) ↦ X (τ, b, c)) *ᵥ C ∘ ξ

/-- The finite Heisenberg operator `New.Space.finHeisenbergOp` of a vector x over the finite adeles,
restricted to the finite part 𝒮_f of 𝒮(V). -/
@[simps! apply_coe]
def Space.heisenbergFinPart (x : n → 𝔸f E) : Module.End ℂ V.finitePart :=
  LinearMap.restrict (V.finHeisenbergOp x) fun _ ↦ finHeisenbergOp_mem_finitePart x

/-- The Weil representation `pairWeil V T a b` at the finite points, restricted to the finite part
of 𝒮(Hom(V, T)). -/
@[simps! apply_apply_coe]
def pairWeilFinite : Gf E n × Gf E n' →* Module.End ℂ (V.hom T).finitePart where
  toFun p :=
    LinearMap.restrict (pairWeil V T a b ((1, p.1), 1, p.2)).1 fun f hf ↦ by
      -- Up to a scalar, `pairWeil` is `ω` at a point whose infinite part is trivial (`onHom_fin`).
      refine (finitePart _).smul_mem _ ?_
      erw [onHom_fin]
      exact omega_mem_finitePart _ hf
  map_one' := by
    ext
    simp [Prod.mk_one_one]
  map_mul' p q := by
    ext f : 2
    change _ = pairWeil V T a b _ (pairWeil V T a b _ f)
    simp [rep_apply_apply]

variable (n n' κ e) in
/-- An abstract theta kernel with data in S. It consists of a representation ω of G_f × G'_f on S,
and a linear map `jetMap` from S to linear maps from functions on `WeylIndex n κ` to functions on
`WeylIndex n' κ`, equivariant for the rational points Γ × Γ' in weight e on the source and ea on
the target; every datum has an open stabiliser. The subgroup K does not enter the fields: it is the
level at which `New.Kernel.lift` integrates. -/
structure Kernel (K : Subgroup (Gf E n)) (S : Type*) [AddCommGroup S] [Module ℂ S] where
  /-- The action of the finite points `G_f × G'_f` on the data. -/
  ω : Representation ℂ (Gf E n × Gf E n') S
  /-- The jet map of a datum, a linear map from vectors of rank `n` to vectors of rank `n'`. -/
  jetMap : S →ₗ[ℂ] (WeylIndex n κ → ℂ) →ₗ[ℂ] WeylIndex n' κ → ℂ
  /-- The jet map is equivariant for the rational points `Γ × Γ'`:
  `jetMap (ω (γ, δ) Φ) (weightRep κ e γ v) = weightRep κ ea δ (jetMap Φ v)`. -/
  equivariant (γ : U (stdSpace E n).J) (δ : U (stdSpace E n').J) (Φ : S) (v : WeylIndex n κ → ℂ) :
      jetMap (ω (stdEmbFin γ, stdEmbFin δ) Φ) ((stdSpace E n).weightRep κ e γ v) =
        (stdSpace E n').weightRep κ ea δ (jetMap Φ v)
  /-- Every datum Φ has an open stabiliser: `g ↦ ω g Φ` is invariant under an open subgroup. -/
  isOpen_stabilizer (Φ : S) : (rightStabilizer (ω · Φ)).IsOpen

end

variable {E n n' : Type} [Field E] [CMType E] [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] {κ : InfinitePlace E → ℕ → ℕ}
  {eb e ea : InfinitePlace E → ℤ} {K : Subgroup (Gf E n)} {S : Type*} [AddCommGroup S] [Module ℂ S]
  (k : Kernel n n' κ e ea K S)

@[local simp]
lemma Kernel.omega_omega (p q : Gf E n × Gf E n') (Φ : S) : k.ω p (k.ω q Φ) = k.ω (p * q) Φ := by
  simp

/-- Let `k` be an abstract theta kernel (`New.Kernel`) over a CM field `E`, with a representation
`ω` of `G_f × G'_f` on the data `S` and a jet map `jetMap` from data to linear maps from functions
on `WeylIndex n κ` to functions on `WeylIndex n' κ`. For a datum `Φ`, an algebraic form `φ` of
weight `(κ, e)` and `h ∈ G'_f`, the integrand `g ↦ jetMap(ω(g, h)Φ)(φ(g))` of the theta lift lies in
`New.smoothInvariants stdRatPoints`. In words, it is left invariant under the rational points
`U_n(E)`, and its stabiliser under right translation is open. -/
@[simp]
lemma Kernel.integrand_mem_smoothInvariants (Φ : S) (φ : AlgForm n κ e) (h : Gf E n') :
    (fun g : Gf E n ↦ k.jetMap (k.ω (g, h) Φ) (φ.val g)) ∈ smoothInvariants stdRatPoints := by
  obtain ⟨hφ_smooth, hφ_equiv⟩ := φ.property
  constructor
  · -- Left invariance: `φ` is equivariant, and `equivariant` at `(γ, 1)` absorbs `γ`.
    rintro _ ⟨γ, rfl⟩ g
    simpa [hφ_equiv γ] using k.equivariant γ 1 (k.ω (g, h) Φ) (φ.val g)
  · -- The stabiliser contains the open subgroup of the `a` that fix `φ` and for which `(a, 1)`
    -- fixes `Φ`.
    let L : Subgroup (Gf E n) :=
      rightStabilizer φ.val ⊓ comap (.inl _ _) (rightStabilizer fun g ↦ k.ω g Φ)
    have hL_open : IsOpen (L : Set (Gf E n)) :=
      .inter hφ_smooth ((k.isOpen_stabilizer Φ).preimage (.prodMk_left 1))
    refine L.isOpen_mono (fun a ha ↦ ?_) hL_open
    obtain ⟨ha_φ, ha_Φ⟩ := Subgroup.mem_inf.1 ha
    refine mem_rightStabilizer.2 fun g ↦ ?_
    have h_ω_eq : k.ω (g * a, h) Φ = k.ω (g, h) Φ := by
      simpa using mem_rightStabilizer.1 (Subgroup.mem_comap.1 ha_Φ) (g, h)
    rw [h_ω_eq, mem_rightStabilizer.1 ha_φ g]

variable [IsLevel K]

/-- The theta lift with datum Φ. An algebraic form φ of weight (κ, e) goes to the algebraic form
h ↦ ∫ jetMap(ω(g,h)Φ)(φ(g)) dg of weight (κ, ea). The integral is over Γ\G_f, Γ the rational
points, for the Haar measure with vol K = 1 (`New.classIntegral`). -/
def Kernel.lift : S →ₗ[ℂ] AlgForm n κ e →ₗ[ℂ] AlgForm n' κ ea := by
  refine LinearMap.mk₂ ℂ
    (fun Φ φ ↦
      ⟨fun h ↦ classIntegral stdRatPoints K fun g ↦ k.jetMap (k.ω (g, h) Φ) (φ.1 g), ?_,
        fun γ h ↦ ?_⟩)
    (fun Φ Φ' φ ↦ ?_) (fun c Φ φ ↦ ?_) (fun Φ φ φ' ↦ ?_) fun c Φ φ ↦ ?_
  · -- Smoothness: the lift is fixed by the open subgroup of the `a` with `(1, a)` fixing `Φ`.
    refine (comap (.inr _ _) (rightStabilizer fun g ↦ k.ω g Φ)).isOpen_mono (fun a ha h ↦ ?_)
      ((k.isOpen_stabilizer Φ).preimage (.prodMk_right 1))
    simp [← (ha ⟨·, h⟩)]
  · -- Equivariance: the action of `γ` commutes with the integral, and `equivariant` at `(1, γ)`
    -- moves it into `k.ω`.
    exact classIntegral_map_mul_right (weightRep κ ea _ γ).toAddMonoidHom 1
      (k.integrand_mem_smoothInvariants Φ φ h) (by simp [← k.equivariant 1])
  -- Bilinearity: the integral is additive and commutes with scalars.
  · ext : 2
    simp [classIntegral_add, ← Pi.add_def]
  · ext h : 2
    exact classIntegral_map_mul_right (DistribSMul.toAddMonoidHom _ c) 1
      (k.integrand_mem_smoothInvariants Φ φ h) (by simp)
  · ext : 2
    simp [classIntegral_add, ← Pi.add_def]
  · ext h : 2
    exact classIntegral_map_mul_right (DistribSMul.toAddMonoidHom _ c) 1
      (k.integrand_mem_smoothInvariants Φ φ h) (by simp)

/-- Equivariance of the theta lift: the lift with datum ω(a,b)Φ of the right translate of φ by a
is the right translate by b of the lift of φ with datum Φ. -/
lemma Kernel.lift_equivariant (a : Gf E n) (b : Gf E n') (Φ : S) (φ : AlgForm n κ e) :
    k.lift (k.ω (a, b) Φ) (algFormRep κ e a φ) = algFormRep κ ea b (k.lift Φ φ) := by
  -- The integral over `g` is invariant under the right translation `g ↦ g * a`.
  ext h : 2
  have h_shift (g : Gf E n) : k.jetMap (k.ω (g, h) (k.ω (a, b) Φ))
      ((algFormRep κ e a φ).val g) = k.jetMap (k.ω (g * a, h * b) Φ) (φ.val (g * a)) := by simp
  exact classIntegral_map_mul_right (.id _) a (k.integrand_mem_smoothInvariants Φ φ (h * b)) h_shift

lemma coe_map_conj_inv_eq_transpose (u : USign (1 : n → ℤˣ)) :
    (u.val⁻¹.map (starRingEnd ℂ)).val = uᵀ := by
  -- For the identity form the inverse of `u` is its conjugate transpose.
  have h_inv : ((u.val⁻¹ : GL n ℂ) : Matrix n n ℂ) = ((u.val : GL n ℂ) : Matrix n n ℂ)ᴴ := by
    simpa [signMatrix_one] using U.coe_inv (signMatrix_mul_self (ε := (1 : n → ℤˣ))) u
  change ((u.val⁻¹ : GL n ℂ) : Matrix n n ℂ).map (starRingEnd ℂ) = uᵀ
  ext i j
  simp [h_inv]

/-- For a covector A, a vector ξ and a power series F, A paired with the Schur jet matrix of F
applied to ξ is the jet of F along the polynomial Aᵀ S_κ(z) ξ. -/
lemma dotProduct_schurJet_mulVec (A : WeylIndex n' κ → ℂ) (ξ : WeylIndex n κ → ℂ)
    (F : MvPowerSeries (InfinitePlace E × n' × n) ℂ) :
    A ⬝ᵥ schurJet κ F *ᵥ ξ = jet ℂ (schurCoeffPoly A ξ) F := by
  simp [schurCoeffPoly, schurJet, dotProduct, mulVec, C_mul', mul_comm]

/-- Assume `IsLiftWeight n n' κ eb e`, i.e. the weight `(κ, e)` of rank `n` goes up to rank `n'`
along `eb`. Then applying a ring homomorphism `φ` to an entry of the Schur jet matrix of a power
series `F` gives the same entry of the Schur jet matrix of the power series obtained by applying `φ`
to the coefficients of `F`. -/
lemma map_schurJet (hκ : IsLiftWeight n n' κ eb e) {R S : Type} [CommRing R] [CommRing S]
    (i' : WeylIndex n' κ) (i : WeylIndex n κ) (φ : R →+* S)
    (F : MvPowerSeries (InfinitePlace E × n' × n) R) :
    φ (schurJet κ F i' i) = schurJet κ (F.map φ) i' i := by
  simp [schurJet, map_jet, map_schur hκ.1]

/-- Under `IsLiftWeight n n' κ eb e`, evaluating `schurCoeffPoly A ξ` at z gives Aᵀ S_κ(z) ξ, for
the matrices z_τ with entries z(τ, b, c). -/
lemma eval_schurCoeffPoly (hκ : IsLiftWeight n n' κ eb e) (z : InfinitePlace E × n' × n → ℂ)
    (A : WeylIndex n' κ → ℂ) (ξ : WeylIndex n κ → ℂ) :
    eval z (schurCoeffPoly A ξ) =
      A ⬝ᵥ schur κ (fun τ : InfinitePlace E ↦ of fun (b : n') (c : n) ↦ z ⟨τ, b, c⟩) *ᵥ ξ := by
  simp [schurCoeffPoly, dotProduct, mulVec, map_schur hκ.1]

/-- Let `E` be a CM field, and assume `IsLiftWeight n n' κ eb e`: `card n < card n'`,
no column has height strictly between them, and `e τ = eb τ + κ τ (card n)`. For real points `x` of
U(n) and `y` of U(n') (signs `1`), the real Weil representation `realPairWeil ea eb` acts by
`∏_w (det y_w)^{ea_w} (det x_w)^{−eb_w}` times the Fock operator of `z ↦ y z x⁻¹`, and it sends
`schurCoeffPoly A ξ = Aᵀ S_κ(z) ξ` to `schurCoeffPoly (A ᵥ* conjWeylMatrix κ ea y⁻¹) (conjWeylRep κ
e x ξ)`. That is, `y⁻¹` acts on the covector `A` and `x` acts on the vector `ξ` by the conjugate
Weyl representations of weights `(κ, ea)` and `(κ, e)`. -/
lemma realPairWeil_schurCoeffPoly (hκ : IsLiftWeight n n' κ eb e) {ea : InfinitePlace E → ℤ}
    (x : GInf E (1 : n → ℤˣ)) (y : GInf E (1 : n' → ℤˣ)) (A : WeylIndex n' κ → ℂ)
    (ξ : WeylIndex n κ → ℂ) :
    realPairWeil (s := 1) (s' := 1) ea eb (x, y) (schurCoeffPoly A ξ) =
      schurCoeffPoly (A ᵥ* conjWeylMatrix κ ea y⁻¹) (conjWeylRep κ e x ξ) := by
  -- By `realPairWeil_polyVector`, `(x⁻¹, y)` substitutes `yᵀ z xᵀ` for `z`, times powers of `det x`
  -- and `det y`; `schur κ` turns this product into the actions on `A` and on `ξ`.
  obtain ⟨x, rfl⟩ := inv_surjective x
  have h_parts : FitsRanks (fun _ ↦ n) (fun _ ↦ n') κ ∧ card n < card n' ∧
      e = fun τ ↦ eb τ + κ τ (card n) := hκ
  obtain ⟨h_fits, h_lt, rfl⟩ := h_parts
  -- `schur_mul_right`, with its exponent of `det (g τ)` computed from `card n < card n'`.
  have h_schur_mul (z : InfinitePlace E → Matrix n' n ℂ) (g : InfinitePlace E → Matrix n n ℂ) :
      schur κ (fun τ ↦ z τ * g τ) = (∏ τ, (g τ).det ^ κ τ (card n)) • (schur κ z * schur κ g) := by
    simpa [schurDetExp, h_lt] using schur_mul_right h_fits z g
  -- The double sums that the substitution produces are the entries of `yᵀ w xᵀ`.
  have h_entry (w : InfinitePlace E × n' × n → ℂ) (τ : InfinitePlace E) :
      (of fun (b : n') (c : n) ↦ ∑ i : n', ∑ j : n, ((y τ : GL n' ℂ) : Matrix n' n' ℂ) i b *
          (((x τ : GL n ℂ) : Matrix n n ℂ) c j * w (τ, i, j))) =
        ((y τ : GL n' ℂ) : Matrix n' n' ℂ)ᵀ *
          ((of fun (b : n') (c : n) ↦ w (τ, b, c)) * ((x τ : GL n ℂ) : Matrix n n ℂ)ᵀ) := by
    ext b c
    simp only [of_apply, mul_apply, transpose_apply, Finset.mul_sum]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  ext w
  -- Evaluate both polynomials at `w` and collect the Schur matrices on the right into one;
  -- determinants of transposes are left for the next step. `aeval_def` must act first (`↓`):
  -- otherwise the substitution stays unexpanded. Without `-map_inv` and `-val_map_apply` the
  -- conjugated inverses leave the form that `coe_map_conj_inv_eq_transpose` rewrites.
  simp [realPairWeil_polyVector, ↓aeval_def, ← eval_assoc, eval_schurCoeffPoly hκ,
    conjWeylRep, weylRep, -map_inv, mul_smul, coe_map_conj_inv_eq_transpose, Units.smul_def,
    -val_map_apply, _root_.zpow_add, -det_transpose, -map_smul, dotProduct_mulVec,
    ← h_schur_mul, prod_mul_distrib, principalMinor_of_forall,
    DiscreteSeries.principalMinor_of_forall_not]
  -- Both sides are now the same multiple of `Aᵀ S_κ(yᵀ w xᵀ) ξ`.
  simp [h_entry, vecMul_smul, field, ← schur_mul_left h_fits, mul_right_comm]

variable [WeilData E]

/-- If the ranks fit `κ` (`New.FitsRanks`), scaling the entries of the variable matrices `z τ` by
`c` multiplies each entry of `schur κ z` by `c` to the number of boxes in the columns of height
below `card n'`. -/
lemma aeval_smul_X_schur {Φ : Type} [Fintype Φ] [DecidableEq Φ] {κ : Φ → ℕ → ℕ}
    (h_fits : FitsRanks (fun _ ↦ n) (fun _ ↦ n') κ) (c : ℂ) (i' : WeylIndex n' κ)
    (i : WeylIndex n κ) :
    aeval (R := ℂ) (fun x : Φ × n' × n ↦ c • X (R := ℂ) x)
        (schur κ (fun τ : Φ ↦ of fun (b : n') (a : n) ↦ X (τ, b, a)) i' i) =
      c ^ boxes κ (card n') •
        schur κ (fun τ : Φ ↦ of fun (b : n') (a : n) ↦ X (τ, b, a)) i' i := by
  let R : Type := MvPolynomial (Φ × n' × n) ℂ
  have h_smul : schur κ (fun τ ↦ (C c : R) • of fun (b : n') (a : n) ↦ (X (τ, b, a) : R)) =
      (C c : R) ^ boxes κ (card n') • schur κ fun τ ↦ of fun b a ↦ (X (τ, b, a) : R) := by
    rw [schur_smul h_fits, prod_pow_eq_pow_sum]
  simpa [map_schur h_fits, ← C_mul', smul_of, Pi.smul_def] using congrFun₂ h_smul i' i

/-- If the ranks fit `κ` (`New.FitsRanks`), the entries of `schur κ z` are homogeneous polynomials
in the entries of the variable matrices `z τ`. The degree is the number of boxes in the columns of
height below `card n'`. -/
lemma isHomogeneous_schur {Φ : Type} [Fintype Φ] [DecidableEq Φ] {κ : Φ → ℕ → ℕ}
    (h_fits : FitsRanks (fun _ ↦ n) (fun _ ↦ n') κ) (i' : WeylIndex n' κ) (i : WeylIndex n κ) :
    (schur κ (fun τ : Φ ↦ of fun (b : n') (a : n) ↦ X (τ, b, a)) i' i :
      MvPolynomial (Φ × n' × n) ℂ).IsHomogeneous (boxes κ (card n')) :=
  isHomogeneous_iff_aeval_smul_X.2 fun c _ ↦ aeval_smul_X_schur h_fits c i' i

/-- Assume `IsLiftWeight n n' κ eb e`. Scaling the variables of the Taylor series of f by `c`
multiplies its Schur jet matrix by `c` to the number of boxes in the columns of height below
`card n'`. -/
lemma schurJet_jetSeries_eq_smul (hκ : IsLiftWeight n n' κ eb e) (c : ℂ)
    (f : 𝒮 ((stdSpace E n).hom (stdSpace E n'))) :
    schurJet κ (jetSeries ((stdSpace E n).hom (stdSpace E n')) c f) =
      c ^ boxes κ (Fintype.card n') •
        schurJet κ (jetSeries ((stdSpace E n).hom (stdSpace E n')) 1 f) := by
  -- An entry of the jet matrix is the theta functional at the Fock vector of an entry of
  -- `schur κ (c • z)`, and `c` comes out of that entry.
  ext i' i
  simp [schurJet, -aeval_eq_bind₁, aeval_smul_X_schur hκ.1 c, aeval_X_left_apply]

/-- The theta function of a Schur coefficient is a matrix coefficient of the jet matrix. Assume
`IsLiftWeight n n' κ eb e`, and let the characters `a`, `b` have weights `ea`, `eb`, with ψ, ψ' the
attached characters of the residue fields at the finite places. Let `v` be the Fock vector of
`schurCoeffPoly A ξ`, and move `v ⊗ f` by the adelic points `(x, g)` and `(y, h)`. The theta
functional of the result, times `c` to the number of boxes, is `Aᵀ y⁻¹ k x ξ`. Here `k` is the jet
matrix at the scale `c` of the translate of `f` by the finite parts `(g, h)`, and the real parts
`x`, `y` act in the weights `(κ, e)`, `(κ, ea)`. -/
lemma theta_pairWeil_schurCoeffPoly (hκ : IsLiftWeight n n' κ eb e) (c : ℂ) {a b : AutChar E}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} (ha : a.HasWeight ea ψ)
    (hb : b.HasWeight eb ψ') (x : GInf E (1 : n → ℤˣ)) (g : Gf E n) (y : GInf E (1 : n' → ℤˣ))
    (h : Gf E n') (A : WeylIndex n' κ → ℂ) (ξ : WeylIndex n κ → ℂ)
    (f : 𝒮 ((stdSpace E n).hom (stdSpace E n'))) :
    c ^ boxes κ (card n') * ((stdSpace E n).hom (stdSpace E n')).θ
        (pairWeil (stdSpace E n) (stdSpace E n') a b ((x, g), y, h)
          (integrated ((stdSpace E n).hom (stdSpace E n'))
            (polyVector (realSigns E (homSigns 1 1)) (schurCoeffPoly A ξ)) f)) =
      A ⬝ᵥ conjWeylRep κ ea y⁻¹
        (schurJet κ (jetSeries ((stdSpace E n).hom (stdSpace E n')) c
          (pairWeil (stdSpace E n) (stdSpace E n') a b ((1, g), 1, h) f)) *ᵥ
            conjWeylRep κ e x ξ) := by
  -- The real parts act on the polynomial through `A` and `ξ`, the finite parts act on `f`, and the
  -- theta functional of a polynomial tensored with a datum is a jet of its Taylor series.
  rw [pairWeil_integrated_all, realPairWeil_schurCoeffPoly hκ, schurJet_jetSeries_eq_smul hκ c]
  simp [conjWeylRep, dotProduct_mulVec, ↓dotProduct_schurJet_mulVec, -mulVec_mulVec, smul_mulVec]

/-- The theta kernel of the definite pair `stdSpace E n`, `stdSpace E n'`, for characters `a`, `b`
of weights `ea`, `eb` and a subgroup `K` of the finite points. The data are the finite part of
𝒮(Hom), with the action `pairWeilFinite (stdSpace E n) (stdSpace E n') a b` of the finite points. A
datum `f` gives a linear map from vectors of weight `(κ, e)` in rank `n` to those of weight
`(κ, ea)` in rank `n'`. Its matrix is `schurJet κ (jetSeries _ c f)`: the jets along `schur κ` of
the Taylor series of the theta function of `f`, with derivatives scaled by `c`. -/
def thetaKernel (hκ : IsLiftWeight n n' κ eb e) (c : ℂ) {a b : AutChar E} {ea : InfinitePlace E → ℤ}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} (ha : a.HasWeight ea ψ)
    (hb : b.HasWeight eb ψ') (K : Subgroup (Gf E n)) :
    Kernel n n' κ e ea K ((stdSpace E n).hom (stdSpace E n')).finitePart where
  ω := pairWeilFinite (stdSpace E n) (stdSpace E n') a b
  jetMap := Matrix.toLin'.1 ∘ₗ schurJet κ ∘ₗ jetSeries ((stdSpace E n).hom (stdSpace E n')) c ∘ₗ
    (finitePart ((stdSpace E n).hom (stdSpace E n'))).subtype
  equivariant γ γ' f v := by
    -- Pair both sides with a covector `A`. By `theta_pairWeil_schurCoeffPoly` the theta function
    -- of `schurCoeffPoly A v` tensored with `f` is a coefficient of the jet matrix at `(γ, γ')`
    -- and at `(1, 1)`, and the two values agree because `γ` and `γ'` are rational.
    let V : Space E (n' × n) (homSigns 1 1) := (stdSpace E n).hom (stdSpace E n')
    have h_inv (F : 𝒮 V) :
        V.θ (pairWeil (stdSpace E n) (stdSpace E n') a b
          ((stdSpace E n).ratEmbed γ, (stdSpace E n').ratEmbed γ') F) = V.θ F := by
      simpa using pairWeil_of_mem_Gamma _ _ a b ⟨γ, rfl⟩ ⟨γ', rfl⟩ F 0
    let x : GInf E (1 : n → ℤˣ) := ((stdSpace E n).ratEmbed γ).1
    let y : GInf E (1 : n' → ℤˣ) := ((stdSpace E n').ratEmbed γ').1
    let f' : 𝒮 V :=
      pairWeil (stdSpace E n) (stdSpace E n') a b ((1, stdEmbFin γ), 1, stdEmbFin γ') f.val
    have h_coeff (A : WeylIndex n' κ → ℂ) :
        A ⬝ᵥ conjWeylRep κ ea y⁻¹ (schurJet κ (V.jetSeries c f') *ᵥ conjWeylRep κ e x v) =
          A ⬝ᵥ schurJet κ (V.jetSeries c f.val) *ᵥ v := by
      let F : 𝒮 V := V.integrated (polyVector (realSigns E (homSigns 1 1)) (schurCoeffPoly A v)) f
      calc
        _ = c ^ boxes κ (card n') * V.θ (pairWeil (stdSpace E n) (stdSpace E n') a b
              ((stdSpace E n).ratEmbed γ, (stdSpace E n').ratEmbed γ') F) :=
          (theta_pairWeil_schurCoeffPoly hκ c ha hb x (stdEmbFin γ) y (stdEmbFin γ') A v f).symm
        _ = c ^ boxes κ (card n') * V.θ F := by rw [h_inv]
        _ = _ := by
          simpa only [Prod.mk_one_one, map_one, inv_one, Module.End.one_apply,
            one_apply_eq_self]
            using theta_pairWeil_schurCoeffPoly hκ c ha hb 1 1 1 1 A v f
    change schurJet κ (V.jetSeries c f') *ᵥ conjWeylRep κ e x v =
      conjWeylRep κ ea y (schurJet κ (V.jetSeries c f.val) *ᵥ v)
    have h_eq : conjWeylRep κ ea y⁻¹ (schurJet κ (V.jetSeries c f') *ᵥ conjWeylRep κ e x v) =
        schurJet κ (V.jetSeries c f.val) *ᵥ v :=
      dotProduct_eq _ _ fun A ↦ by rw [dotProduct_comm, h_coeff, dotProduct_comm]
    rw [← h_eq, Representation.self_inv_apply]
  isOpen_stabilizer f := by
    -- The stabiliser of `f` contains an open subgroup `L × L'`.
    obtain ⟨L, L', h_fix⟩ := exists_level_pairWeil a b f.2
    refine isOpen_mono ?_ (L.prod L').2
    simp_all [LE.le, mem_prod, Subtype.ext_iff]

end New

end
