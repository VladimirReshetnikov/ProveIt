import Lib.Adelic.QuotientMeasure.UnfoldingInStages
import Lib.SiegelWeil.SingularForms.UnimodularCoefficients
import Lib.Weil.DualPair.ThetaIntegrals

/-!
# Vanishing theta descents for unitary groups: Fourier coefficients and periods

This file defines the predicate `New.SiegelWeil.DescentsVanish`, the vanishing of all theta descents
of a function on `U(V)(𝔸)` to `U(W)(𝔸)` for data that are vacua above given places. It studies the
Fourier coefficients of theta lifts between unitary groups along the centre of the unipotent
radical. These coefficients are written as sums over rational frames. Then, for an invertible Gram
matrix, Witt's theorem writes them as integrals modulo a stabiliser.

## Main definitions and results

* `New.SiegelWeil.DescentsVanish`: the descents of `Y` vanish for all data that are vacua above the
  places of `S`.
* `New.Space.Splitting.centreCoeff_integral_eq_tsum`: the coefficient at `j β` keeps the frames `x`
  with Gram matrix `β`.
* `New.SiegelWeil.integral_blockEmb_eq_zero_of_descentsVanish`: split `V = V″ ⊕ V°` into blocks of
  ranks `n₁` and `n₂`. Let `o₁` be the frame of `V″` and `I(h)` the period over `[U(V°)]` of the
  right translate by `h`. The vanishing of a Fourier coefficient of the descents makes `I`, times a
  weight, orthogonal to every additive character of the frame `h⁻¹ o₁` that ignores its components
  at the places of `T` and their conjugates, hence, by Stone–Weierstrass, to every continuous
  function of these characters. On the support of the weight `I` is such a function, so it vanishes
  there.

Notions from other files:
* `New.𝒮`: the Banach space of data on which the Weil representation of a hermitian space acts;
  `New.Space.projOn` projects it on the vectors that are vacua above a set of finite places and
  their conjugates.
* `New.pairTheta W V a b f`: the theta kernel on `U(W)(𝔸) × U(V)(𝔸)` of a datum `f` on `Hom(W, V)`,
  twisted by the characters `a`, `b` of `U(1)`. `New.pairThetaKer` bundles it, and `New.Space.lift`
  for `(pairThetaKer W V a b).swap` integrates a function on `U(V)(𝔸)` against it.
* `New.Space.Splitting.radicalCentre`: the parametrisation of the centre of the unipotent radical by
  adelic `p × p` matrices; `centreCoeff T F g` is the mean of `ψ (tr (T M)) * F (z M * g)` over the
  `M` modulo rational matrices, `z` being this parametrisation.
* `New.WeilData.upsilonU1`: the restriction of the splitting character υ to the norm-one ideles.

## Relation to the literature

Known result: Fourier coefficients of theta lifts as periods over stabilisers. Here a single
non-degenerate coefficient of a theta lift to a split unitary group is unfolded once by Witt's
theorem. Hence a form on the definite U(n) orthogonal to the theta kernels of the split space has
zero period over the complementary unitary group. Source: P. Walls, The theta correspondence,
periods of automorphic forms and special values of standard automorphic L-functions, arXiv
1501.01565 (2015), Prop. 2.1.1; S. Rallis, On the Howe duality conjecture, Compositio Math. 51
(1984) 333–399.
-/

/-! ## Vanishing of descents -/

namespace New.SiegelWeil

open Space Fock

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ}

/-- All descents of `Y` from `U(V)` to `U(W)` vanish, for the data that are vacua above the places
of `S` and their conjugates: for every datum `f` on `Hom(W, V)` fixed by the projection `projOn S`,
the function `g ↦ ∫ θ_f(g, h) Y(h) dh` on `U(W)(𝔸)` is zero. The integral is over the adelic
quotient `[U(V)]`, and `θ_f` is the theta kernel of the pair twisted by `a (det h)`, for the
character `a` of `U(1)`. No twist in `g` is taken: it would only multiply a descent by a character
of `det g`. -/
def DescentsVanish (W : Space E n s) (V : Space E m t) (a : AutChar E) (S : Set (FinPlace E))
    (Y : G E t → ℂ) : Prop :=
  ∀ f : 𝒮 (W.hom V), projOn (W.hom V) S f = f → lift (pairThetaKer W V a 1).swap f Y = 0

variable {W : Space E n s} {a : AutChar E}

/-- Translations: let `Y` be an automorphic function on `U(V)(𝔸)` whose descents to `U(W)` vanish
for data that are vacua above `S`. If `h₀` is integral (lies in `localIntGL m w`) at every place `w`
of `S`, then the descents of the right translate of `Y` by `h₀` vanish as well. -/
lemma DescentsVanish.comp_mul_right {V : Space E m t} {S : Set (FinPlace E)} {Y : G E t → ℂ}
    (h_vanish : DescentsVanish W V a S Y) (hY : V.IsAutomorphic Y) {h₀ : G E t}
    (hh₀ : ∀ w ∈ S, h₀.2.atPlace w ∈ localIntGL m w) :
    DescentsVanish W V a S fun h : G E t ↦ Y (h * h₀) := by
  intro f hf
  -- The descent of the translate by `f` is the descent of `Y` by `ω(1, h₀⁻¹) f`.
  have h_move : lift (pairThetaKer W V a 1).swap f (fun h ↦ Y (h * h₀)) =
      lift (pairThetaKer W V a 1).swap (pairWeil W V a 1 (1, h₀⁻¹) f) Y := by
    simpa using ((pairThetaKer W V a 1).swap.lift_omega_left hY h₀⁻¹ (φ := f)).symm
  -- The datum `ω(1, h₀⁻¹) f` is again vacuum above `S`, as `h₀` is integral there.
  rw [h_move]
  exact h_vanish _ (projOn_pairWeil hf (1, h₀⁻¹) fun w hw ↦
    G.onHom_atPlace_mem (by simp) (by simpa using inv_mem (hh₀ w hw)))

/-- To show that all descents of `Y` by data that are vacua off a set `Σ` of places vanish, it is
enough to test special data. Here `V` is definite, `A` is a set of finite places disjoint from its
conjugate, and `Σ = A.conjClosure` consists of the places of `A` and their conjugates. For a
Schwartz–Bruhat function `Ψ` above `A`, the operator `schrodingerOp A Ψ` is the combination of
finite Heisenberg operators with which `Ψ` acts on the data. The special datum of `(P, Ψ)` applies
it to the vacuum `vacElem` of `Hom(W, V)`, and then integrates (`integrated`) the real Heisenberg
operators against the Fock vector `polyVector _ P` of the polynomial `P`, with the signs
`realSigns E (homSigns s 1)` of the coordinates at infinity. -/
lemma DescentsVanish.of_schrodingerOp {V : Space E m 1} {A : Set (FinPlace E)}
    (hA : A.IsConjDisjoint) {Y : G E 1 → ℂ} (hY : V.IsAutomorphic Y)
    (h_special : ∀ (P : MvPolynomial (NumberField.InfinitePlace E × m × n) ℂ)
      (Ψ : (m × n → 𝔸f E) → ℂ) [IsSchwartzBruhat A Ψ],
      lift (pairThetaKer W V a 1).swap
        (integrated (W.hom V) (polyVector (realSigns E (homSigns s 1)) P)
          (schrodingerOp (W.hom V) A Ψ (vacElem (W.hom V)))) Y = 0) :
    DescentsVanish W V a A.conjClosureᶜ Y := by
  intro f hf
  funext g
  -- The descent at `g` is a bounded functional `L g` of the datum, so it suffices to test the data
  -- `v_P ⊗ ρ(x) vacElem` with `x` finite and supported on `Σ`.
  obtain ⟨L, hL⟩ : ∃ L : G E s → 𝒮 (W.hom V) →L[ℂ] ℂ, ∀ (φ : 𝒮 (W.hom V)) (k : G E s),
      lift (pairThetaKer W V a 1).swap φ Y k = L k φ :=
    (pairThetaKer W V a 1).swap.exists_clm_lift (hY.mem_rapidFunctions fun _ _ ↦ rfl)
  rw [hL, Pi.zero_apply]
  refine map_eq_zero_of_map_integrated_eq_zero (W.hom V) hf fun P x hx ↦ ?_
  -- `ρ(x) vacElem` is a multiple of the image of `vacElem` under an operator `schrodingerOp A Ψ`.
  have hx_idem : idem A.conjClosure • x = x := by aesop (add simp idem_apply)
  have h_multiple : (W.hom V).finHeisenbergOp x (vacElem (W.hom V)) = stdLattice.semichar x •
      schrodingerOp (W.hom V) A (schrodingerAct A x (boxIndicator (m × n) A))
        (vacElem (W.hom V)) := by
    simp [schrodingerOp_schrodingerAct_boxIndicator hA, hx_idem, finHeisenbergOp]
  rw [h_multiple, map_smul, map_smul, ← hL, h_special, Pi.zero_apply, smul_zero]

end New.SiegelWeil

/-!
## Fourier coefficients of a theta integral via rational frames

Fourier coefficients of the theta lift of `y` from `U(V)` to `U(W)`, where `W` has the splitting `D`
(`New.Space.Splitting`) with isotropic frames of rank `p`. The element `j` of `E` is the imaginary
element of `New.WeilData`.
-/

namespace New.Space.Splitting

open Matrix MeasureTheory

/-- A monoid that acts on columns acts on matrices, column by column. -/
instance (priority := low) {m p M R : Type*} [Monoid M] [MulAction M (m → R)] :
    MulAction M (Matrix m p R) :=
  (Equiv.piComm _).mulAction M

/-- The unitary group acts on frames by matrix multiplication. -/
lemma _root_.New.U.smul_matrix_eq_mul {m p E : Type*} [CommRing E] [StarRing E] [Fintype m]
    [DecidableEq m] {J : Matrix m m E} (γ : U J) (x : Matrix m p E) :
    γ • x = (γ : Matrix m m E) * x :=
  rfl

section Stabilizer

variable {E m p : Type} [Field E] [CMType E] [Fintype m] [DecidableEq m]
  {t : m → ℤˣ} {V : Space E m t}

/-- The rational stabiliser of a rational frame `x`: the image in `U(V)(𝔸)` of the group of the
rational points `γ` of `U(V)` with `γ x = x`. -/
noncomputable def _root_.New.Space.ratStabilizer (V : Space E m t) (x : Matrix m p E) :
    Subgroup (G E t) :=
  (MulAction.stabilizer (U V.J) x).map V.ratEmbed

/-- The elements of the rational stabiliser of `x` are the images of the rational points of the
unitary group that fix `x`. -/
lemma _root_.New.Space.mem_ratStabilizer {x : Matrix m p E} {k : G E t} :
    k ∈ V.ratStabilizer x ↔ ∃ γ : U V.J, (γ : Matrix m m E) * x = x ∧ V.ratEmbed γ = k :=
  Subgroup.mem_map

instance (x : Matrix m p E) : DiscreteTopology (V.ratStabilizer x) :=
  inferInstanceAs (DiscreteTopology ((MulAction.stabilizer (U V.J) x).map V.ratEmbed))

end Stabilizer

/-- Witt's theorem for frames: if the rational frame `x` has invertible Gram matrix for the form
`V.J`, the rational frames with the same Gram matrix are those whose orbit under the rational
unitary group `U V.J` contains `x`. -/
lemma _root_.New.Space.gram_eq_iff_mem_orbit {E m p : Type} [Field E] [CMType E] [Fintype m]
    [DecidableEq m] [Fintype p] [DecidableEq p] {t : m → ℤˣ} {V : Space E m t} {x : Matrix m p E}
    (h_gram : IsUnit (xᴴ * V.J * x)) (z : Matrix m p E) :
    zᴴ * V.J * z = xᴴ * V.J * x ↔ x ∈ MulAction.orbit (U V.J) z := by
  simp only [MulAction.mem_orbit_iff, U.smul_matrix_eq_mul]
  constructor
  · exact fun hz ↦ V.witt (.of_isUnit_gram (by rwa [hz])) (.of_isUnit_gram h_gram) hz
  · rintro ⟨γ, rfl⟩
    exact (U.gram_invariant γ z z).symm

variable {E n n₀ m p : Type} [Field E] [CMType E] [H : WeilData E] [Fintype n] [DecidableEq n]
  [Fintype n₀] [DecidableEq n₀] [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] {s : n → ℤˣ}
  {s₀ : n₀ → ℤˣ} {t : m → ℤˣ} {W : Space E n s} {W₀ : Space E n₀ s₀} (D : W.Splitting W₀ p)
  {V : Space E m t} {a b : AutChar E} {f : 𝒮 (W.hom V)} {g : G E s} {y : G E t → ℂ}

/-- By definition `radicalCentre z` is the element `radicalElement` of the unipotent radical with
zero vector and central part `-2 j z`. -/
lemma radicalCentre_apply (z : Matrix p p (𝔸 E)) :
    D.radicalCentre z = D.radicalElement 0 (-toAdele (H.j * 2 : E) • z) :=
  rfl

/-- The theta kernel of the datum `f` at `(g, h)` is the sum of its terms `D.thetaTerm` over the
rational frames `x`, where `D` is the splitting of `W`. -/
lemma hasSum_thetaTerm (h : G E t) :
    HasSum (fun x : Matrix m p E ↦ D.thetaTerm V a b f g x h) (pairTheta W V a b f (g, h)) :=
  D.hasSum_theta_homSlice V (pairWeil W V a b (g, h) f)

/-- Multiplying `g` on the left by the central unipotent element `radicalCentre z` multiplies the
term of the frame `x` in the theta kernel by `ψ (tr (-j β z))`, where `β` is the Gram matrix of `x`
and `ψ` the standard additive character of the adeles. -/
lemma thetaTerm_radicalCentre_mul (z : Matrix p p (𝔸 E)) (x : Matrix m p E) (h : G E t) :
    D.thetaTerm V a b f (D.radicalCentre z * g) x h =
      stdAddChar E ((-H.j • (xᴴ * V.J * x)).map toAdele * z).trace * D.thetaTerm V a b f g x h := by
  have h_scalar : toAdele (2⁻¹ : E) * -toAdele (H.j * 2 : E) = toAdele (-H.j) := by
    simp [← map_neg, ← map_mul, mul_comm H.j]
  have h_phase :
      toAdele (2⁻¹ : E) * (-toAdele (H.j * 2 : E) • z * (xᴴ * V.J * x).map toAdele).trace =
        ((-H.j • (xᴴ * V.J * x)).map toAdele * z).trace := by
    rw [Matrix.map_smul' _ _ _ (map_mul toAdele), Matrix.smul_mul, Matrix.smul_mul, trace_smul,
      trace_smul, trace_mul_comm z, smul_eq_mul, smul_eq_mul, ← mul_assoc, h_scalar]
  have h_split : pairWeil W V a b (D.radicalCentre z * g, h) f =
      pairWeil W V a b (D.radicalCentre z, 1) (pairWeil W V a b (g, h) f) := by
    simp [rep_apply_apply]
  rw [thetaTerm, h_split, radicalCentre_apply, homSlice_radicalElement, gram_at_point_eq_map,
    h_phase]
  -- The Heisenberg translation in `homSlice_radicalElement` is by the zero vector.
  simp [thetaTerm]

/-- For `y` left invariant under the rational points `V.Γ`, the term of the frame `x` in the theta
kernel at `(g, h)`, times `y h`, does not change when `(x, h)` is replaced by `(γ x, γ h)` with `γ`
rational. -/
lemma thetaTerm_mul_ratEmbed_mul (hΓ : V.Γ.FixesLeft y) (γ : U V.J) (x : Matrix m p E) (h : G E t) :
    D.thetaTerm V a b f g ((γ : Matrix m m E) * x) (V.ratEmbed γ * h) * y (V.ratEmbed γ * h) =
      D.thetaTerm V a b f g x h * y h := by
  rw [thetaTerm_ratEmbed_mul, hΓ (V.ratEmbed γ) ⟨γ, rfl⟩]

/-- For `y` left invariant under the rational points `V.Γ`, the term of the frame `x` in the theta
kernel, times `y`, is left invariant under the rational stabiliser of `x`. -/
lemma fixesLeft_thetaTerm_mul (hΓ : V.Γ.FixesLeft y) (x : Matrix m p E) :
    (V.ratStabilizer x).FixesLeft fun h : G E t ↦ D.thetaTerm V a b f g x h * y h := by
  intro k hk h
  obtain ⟨γ, hγ, rfl⟩ := mem_ratStabilizer.mp hk
  simpa only [hγ] using D.thetaTerm_mul_ratEmbed_mul hΓ γ x h

/-- Let `y` be continuous on `U(V)(𝔸)`, and let the terms of the theta kernel at `g` be absolutely
integrable against `y`. Then the theta lift of `y` at `radicalCentre z * g` is the sum over all
rational frames `x` of `ψ (tr (-j β(x) z))` times the integral over `[U(V)]` of the term of `x` at
`g` against `y`, where `β(x)` is the Gram matrix of `x`. -/
lemma integral_pairTheta_radicalCentre_mul (h_int : D.HasIntegrableTerms V a b f g y)
    (hy : Continuous y) (z : Matrix p p (𝔸 E)) :
    ∫ h : G E t, pairTheta W V a b f (D.radicalCentre z * g, h) * y h ∂V.quotMeasure =
      ∑' x : Matrix m p E, stdAddChar E ((-H.j • (xᴴ * V.J * x)).map toAdele * z).trace *
        ∫ h : G E t, D.thetaTerm V a b f g x h * y h ∂V.quotMeasure := by
  -- Expand the kernel into its terms, each the term at `g` times a number `χ x` of modulus one,
  -- and exchange sum and integral.
  let χ (x : Matrix m p E) : ℂ := stdAddChar E ((-H.j • (xᴴ * V.J * x)).map toAdele * z).trace
  have h_expand (h : G E t) : pairTheta W V a b f (D.radicalCentre z * g, h) * y h =
      ∑' x : Matrix m p E, χ x * (D.thetaTerm V a b f g x h * y h) := by
    simp_rw [← (D.hasSum_thetaTerm h).tsum_eq, D.thetaTerm_radicalCentre_mul, ← tsum_mul_right,
      mul_assoc, χ]
  have h_swap : ∑' x : Matrix m p E, ∫ h, χ x * (D.thetaTerm V a b f g x h * y h) ∂V.quotMeasure =
      ∫ h, ∑' x : Matrix m p E, χ x * (D.thetaTerm V a b f g x h * y h) ∂V.quotMeasure :=
    (hasSum_integral_of_lintegral_tsum_lt_top
      (by simpa [← ofReal_norm, χ, Circle.norm_coe] using h_int) -- since `|χ x| = 1`
      fun x ↦ .const_mul (by fun_prop [thetaTerm]) (χ x)).tsum_eq
  simp_rw [h_expand, ← h_swap, integral_const_mul, χ]

/-- Let `D` split `W`, and take the theta kernel of the datum `f` twisted by the characters `a`,
`b`. Let `y` be continuous on `U(V)(𝔸)`, and let the terms of the kernel at `g` be absolutely
integrable against `y` (`HasIntegrableTerms`). Then the Fourier coefficient along the centre of the
unipotent radical, at `j β` and `g`, of the theta lift of `y` is the sum, over the rational frames
`x` with Gram matrix `β`, of the integrals over `[U(V)]` of the term of `x` times `y`. Here `j` is
the imaginary element of `E` given by `WeilData`. -/
lemma centreCoeff_integral_eq_tsum (h_int : D.HasIntegrableTerms V a b f g y)
    (hy : Continuous y) (β : Matrix p p E) :
    D.centreCoeff (H.j • β)
        (fun k : G E s ↦ ∫ h : G E t, pairTheta W V a b f (k, h) * y h ∂V.quotMeasure) g =
      ∑' x : {x : Matrix m p E | xᴴ * V.J * x = β},
        ∫ h : G E t, D.thetaTerm V a b f g (x : Matrix m p E) h * y h ∂V.quotMeasure := by
  have h_summable :
      Summable fun x : Matrix m p E ↦ ∫ h, D.thetaTerm V a b f g x h * y h ∂V.quotMeasure :=
    (hasSum_integral_of_lintegral_tsum_lt_top h_int (by fun_prop [thetaTerm])).summable
  -- With the character of `j • β` from `centreCoeff`, the frequency of `x` is zero exactly when
  -- `x` has Gram matrix `β`. So the right side is the mean over `z` of a sum over all `x`.
  have h_freq (x : Matrix m p E) : -H.j • (xᴴ * V.J * x) + H.j • β = 0 ↔
      x ∈ {x : Matrix m p E | xᴴ * V.J * x = β} := by
    simp [neg_add_eq_zero, WeilData.j_ne_zero]
  rw [isDualFamily_ratMatrices.tsum_coeff_eq_quotMean _ h_freq h_summable, centreCoeff]
  congr with z
  -- The means over `z` have the same integrand: the characters of `j β` and of `x` multiply.
  simp_rw [D.integral_pairTheta_radicalCentre_mul h_int hy, ← tsum_mul_left,
    isDualFamily_ratMatrices.add_left, mul_assoc, mul_left_comm]

/-- Unfolding. Let `y` be continuous on `U(V)(𝔸)` and left invariant under the rational points, and
let the terms of the theta kernel at `g` be absolutely integrable against `y`. Let `x` be a rational
frame with invertible Gram matrix `β`. Then the term of `x` times `y` is integrable modulo the
rational stabiliser of `x`, and its integral is the Fourier coefficient along the centre of the
unipotent radical, at `j β` and `g`, of the theta lift of `y`. -/
lemma centreCoeff_eq_integral_ratStabilizer (h_int : D.HasIntegrableTerms V a b f g y)
    (hy : Continuous y) (hΓ : V.Γ.FixesLeft y) {x : Matrix m p E}
    (h_gram : IsUnit (xᴴ * V.J * x)) :
    Integrable (fun h : G E t ↦ D.thetaTerm V a b f g x h * y h) (V.ratStabilizer x).quotMeasure ∧
    D.centreCoeff (H.j • (xᴴ * V.J * x))
        (fun k : G E s ↦ ∫ h : G E t, pairTheta W V a b f (k, h) * y h ∂V.quotMeasure) g =
      ∫ h : G E t, D.thetaTerm V a b f g x h * y h ∂(V.ratStabilizer x).quotMeasure := by
  -- By Witt's theorem the frames with the Gram matrix of `x` form one orbit of `U V.J`, and the
  -- sum of `centreCoeff_integral_eq_tsum` over it unfolds.
  rw [D.centreCoeff_integral_eq_tsum h_int hy]
  obtain ⟨h_integrable, -, h_sum⟩ := integral_tsum_orbit_of_lt_top_or_integrable (Γ := V.Γ)
    (μ := volume)
    (S := V.ratStabilizer x) (D := {z : Matrix m p E | zᴴ * V.J * z = xᴴ * V.J * x})
    V.ratEmbed_injective rfl (fun z ↦ by fun_prop [thetaTerm]) (D.thetaTerm_mul_ratEmbed_mul hΓ)
    rfl (gram_eq_iff_mem_orbit h_gram) (.inl h_int)
  exact ⟨h_integrable, h_sum⟩

/-- Unfolding, for a subgroup `S` of `U(V)(𝔸)` that consists of the rational points fixing the
rational frame `x₀`. Let `x₀` have invertible Gram matrix `β`, let `y` be continuous and left
invariant under the rational points, and let the terms of the theta kernel at `g` be absolutely
integrable against `y`. Then the term of `x₀` times `y` is left invariant under `S` and integrable
modulo `S`, and its integral is the Fourier coefficient at `j β` and `g` of the theta lift of
`y`. -/
lemma centreCoeff_eq_integral_stabilizer (h_int : D.HasIntegrableTerms V a b f g y)
    (hy : Continuous y) (hΓ : V.Γ.FixesLeft y) {x₀ : Matrix m p E}
    (h_gram : IsUnit (x₀ᴴ * V.J * x₀)) {S : Subgroup (G E t)}
    (hS : ∀ k : G E t, k ∈ S ↔ ∃ γ : U V.J, (γ : Matrix m m E) * x₀ = x₀ ∧ V.ratEmbed γ = k) :
    (S.FixesLeft fun h : G E t ↦ D.thetaTerm V a b f g x₀ h * y h) ∧
    Integrable (fun h : G E t ↦ D.thetaTerm V a b f g x₀ h * y h) S.quotMeasure ∧
    D.centreCoeff (H.j • (x₀ᴴ * V.J * x₀))
        (fun k : G E s ↦ ∫ h : G E t, pairTheta W V a b f (k, h) * y h ∂V.quotMeasure) g =
      ∫ h : G E t, D.thetaTerm V a b f g x₀ h * y h ∂S.quotMeasure := by
  obtain rfl : S = V.ratStabilizer x₀ := S.ext fun k ↦ (hS k).trans mem_ratStabilizer.symm
  exact ⟨D.fixesLeft_thetaTerm_mul hΓ x₀,
    D.centreCoeff_eq_integral_ratStabilizer h_int hy hΓ h_gram⟩

end New.Space.Splitting

/-!
## Vanishing of periods over a block subgroup

`stdSpace E n` is the definite space with Gram matrix `1`, and `(stdSpace E n).Γ` is its group of
rational points. `(stdSpace ..).quotMeasure` is the measure on the quotient by it. `New.G.blockEmb`
is the block-diagonal embedding of `U(n₁) × U(n₂)` in `U(n)`. The three groups are those of `V″`,
`V°` and `V = V″ ⊕ V°`.

The Fourier coefficient at the unit matrix is unfolded and integrated over `[U(n₂)]`
(`DescentsVanish.integral_frameChar_mul_blockPeriod_eq_zero`). Then the datum is varied, and the
Stone–Weierstrass theorem replaces the characters `ψ_u` by a continuous function `χ` of them that
equals the complex conjugate of the period wherever `frameWeight` is nonzero, so
`frameWeight · |I|²` has integral zero.
-/

namespace New.SiegelWeil

open Matrix MeasureTheory Measure WeilData Space Gf Exchange G Splitting Subgroup
  ContinuousMap AddChar

/-- A continuous function `f` on a compact space that depends only on the image under a continuous
map `p` to a normal Hausdorff space is a continuous function of `p`. -/
lemma exists_continuousMap_comp_eq {K X : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace X] [T4Space X] (p : C(K, X)) (f : C(K, ℂ))
    (h_fibre : ∀ a b : K, p a = p b → f a = f b) :
    ∃ χ : C(X, ℂ), ∀ a : K, χ (p a) = f a := by
  -- `f` descends to the compact image of `p`, and Tietze's theorem extends it to `X`.
  let q : C(K, Set.range p) := ⟨Set.rangeFactorization p, p.continuous.subtype_mk _⟩
  have hq : Topology.IsQuotientMap q :=
    q.continuous.isClosedMap.isQuotientMap q.continuous Set.rangeFactorization_surjective
  have h_factors : Function.FactorsThrough f q :=
    fun a b hab ↦ h_fibre a b (congrArg Subtype.val hab)
  obtain ⟨χ, hχ⟩ := (hq.lift f h_factors).exists_restrict_eq (isCompact_range p.continuous).isClosed
  refine ⟨χ, fun a ↦ ?_⟩
  calc χ (p a) = χ.restrict (Set.range p) (q a) := rfl
    _ = f a := by rw [hχ, ← ContinuousMap.comp_apply, hq.lift_comp]

variable {E n n₁ n₂ : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (o : n₁ ⊕ n₂ ≃ n)
  (hs : (1 : n → ℤˣ) ∘ o = (1 : n₁ → ℤˣ) ⊕ᵥ (1 : n₂ → ℤˣ))

variable (E) in
/-- The matrix whose columns are the basis vectors of the first block of the splitting
`n₁ ⊕ n₂ ≃ n`. In the comments below this frame is written `o₁`. -/
noncomputable def firstFrame : Matrix n n₁ (𝔸 E) := (inclMatrix E (o ∘ .inl)).map toAdele

/-- The frame `h⁻¹ o₁`, where `o₁` stands for `firstFrame E o`. -/
noncomputable def movedFrame (h : G E (1 : n → ℤˣ)) : Matrix n n₁ (𝔸 E) :=
  h⁻¹.adeleMatrix * firstFrame E o

/-- The embedding `h₂ ↦ diag(1, h₂)` of the unitary group of the second block of the splitting
`n₁ ⊕ n₂ ≃ n` in that of the whole space. -/
noncomputable def secondBlock : G E (1 : n₂ → ℤˣ) →* G E (1 : n → ℤˣ) :=
  (blockEmb hs).comp (.inr (G E (1 : n₁ → ℤˣ)) (G E (1 : n₂ → ℤˣ)))

/-- The period `I(h) = ∫ Y(diag(h₁, h₂) h) dh₂` over the adelic quotient `[U(n₂)]`, for a fixed
`h₁`. -/
noncomputable def blockPeriod (Y : G E (1 : n → ℤˣ) → ℂ) (h₁ : G E (1 : n₁ → ℤˣ))
    (h : G E (1 : n → ℤˣ)) : ℂ :=
  ∫ h₂ : G E (1 : n₂ → ℤˣ), Y (blockEmb hs (h₁, h₂) * h) ∂(stdSpace E n₂).quotMeasure

/-- The value `ψ_u(x) = ψ(δ ∑ u_{ij} x_{ij})` at a frame `x`, with `ψ` the standard additive
character, `δ = invDifferentIdele E` an idele whose finite part generates the inverse different, and
the components of the sum at the places of `T` and their conjugates replaced by zero. -/
noncomputable def frameChar [WeilData E]
    (T : Set (FinPlace E)) (x : Matrix n n₁ (𝔸 E)) (u : n × n₁ → 𝔸 E) :
    Circle :=
  stdAddChar E (invDifferentIdele E * ((1 - idemAdele T.conjClosure) * u ⬝ᵥ matrixToVec x : 𝔸 E))

/-- The weight `vac[α₀ x] = |e(α₀ x)|²` of a frame `x`, with `e = vacuumFn` the vacuum function on
adelic vectors and `α₀ = scaleIdele E`. It is called the slice of the vacuum below: up to a nonzero
constant, it is what the vacuum datum contributes to the term of a frame in the theta kernel. -/
noncomputable def frameWeight [WeilData E] (x : Matrix n n₁ (𝔸 E)) : ℝ :=
  ‖vacuumFn ((scaleIdele E : 𝔸 E) • matrixToVec x)‖ ^ 2

/-- The block-diagonal element `diag(g₁, g₂)` acts on the frame `o₁` of the first block through
`g₁`. -/
lemma blockEmb_mul_firstFrame (g : G E (1 : n₁ → ℤˣ) × G E (1 : n₂ → ℤˣ)) :
    (blockEmb hs g).adeleMatrix * firstFrame E o = firstFrame E o * g.1.adeleMatrix := by
  simp [reindex_equiv o, blockEmb, firstFrame, inclMatrix, Matrix.mul_apply, ← ext_iff,
    Matrix.one_apply]

/-- The stabiliser of the frame `o₁` is the second block: `g` fixes the first `n₁` basis vectors if
and only if it is `diag(1, v)` for some `v` in `U(n₂)(𝔸)`. -/
lemma mem_range_secondBlock {g : G E (1 : n → ℤˣ)} :
    g ∈ (secondBlock o hs).range ↔ g.adeleMatrix * firstFrame E o = firstFrame E o := by
  constructor
  · rintro ⟨v, rfl⟩
    simp [secondBlock, blockEmb_mul_firstFrame]
  · intro hg
    -- In the basis indexed by `n₁ ⊕ n₂` the first block of columns of `g` is that of `1`.
    let g' : G E ((1 : n₁ → ℤˣ) ⊕ᵥ (1 : n₂ → ℤˣ)) := reindex o.symm hs g
    have h_entry (i : n) (j : n₁) :
        g.adeleMatrix i (o (.inl j)) = (1 : Matrix n n (𝔸 E)) i (o (.inl j)) := by
      simpa [firstFrame, inclMatrix, Matrix.mul_apply, Matrix.one_apply] using congrFun₂ hg i j
    have h_cols : g'.adeleMatrix.toCols₁ = fromRows 1 0 := by
      ext i j : 1
      change g.adeleMatrix (o i) (o (.inl j)) = _
      cases i <;> simp [h_entry, Matrix.one_apply]
    obtain ⟨a, ha⟩ : ∃ a : U (stdForm E (1 : n₂ → ℤˣ)),
        U.sum stdForm_sum (1, a) = g'.toUnitary :=
      ((U.exists_sum_eq_iff_toCols_eq stdForm_sum).right (by simp)).mpr h_cols
    have ha_mat : g'.adeleMatrix = fromBlocks 1 0 0 (a : Matrix n₂ n₂ (𝔸 E)) :=
      (congrArg (fun k : U (stdForm E _) ↦ k.val.val) ha).symm
    have h_sum : G.sum (1, toUnitary.symm a) = g' := by
      apply ext_adeleMatrix
      rw [adeleMatrix_sum, ha_mat]
      simp [adeleMatrix]
    refine ⟨toUnitary.symm a, ?_⟩
    change (reindex o.symm hs).symm (G.sum (1, toUnitary.symm a)) = g
    rw [h_sum, MulEquiv.symm_apply_apply]

/-- The frame `h⁻¹ o₁` does not change when `h` is multiplied on the left by the second block. -/
lemma movedFrame_secondBlock_mul (v : G E (1 : n₂ → ℤˣ)) (h : G E (1 : n → ℤˣ)) :
    movedFrame o (secondBlock o hs v * h) = movedFrame o h := by
  have h_fix : (secondBlock o hs v⁻¹).adeleMatrix * firstFrame E o = firstFrame E o :=
    (mem_range_secondBlock o hs).1 ⟨v⁻¹, rfl⟩
  rw [movedFrame, _root_.mul_inv_rev, adeleMatrix_mul, Matrix.mul_assoc, ← map_inv, h_fix,
    movedFrame]

/-- An element of `U(n₂)(𝔸)` is rational if and only if its image in `U(n)(𝔸)` is rational. -/
lemma comap_Gamma_secondBlock : (stdSpace E n).Γ.comap (secondBlock o hs) = (stdSpace E n₂).Γ :=
  ext (by simp [secondBlock])

/-- `diag(h₁, h₂) = diag(1, h₂) diag(h₁, 1)`. -/
lemma blockEmb_eq_secondBlock_mul (h₁ : G E (1 : n₁ → ℤˣ)) (h₂ : G E (1 : n₂ → ℤˣ)) :
    blockEmb hs (h₁, h₂) = secondBlock o hs h₂ * blockEmb hs (h₁, 1) := by
  simp [secondBlock, ← map_mul]

/-- The second block commutes with `diag(h₁, 1)⁻¹`. -/
lemma inv_blockEmb_mul_secondBlock_mul (h₁ : G E (1 : n₁ → ℤˣ)) (v : G E (1 : n₂ → ℤˣ))
    (g : G E (1 : n → ℤˣ)) :
    (blockEmb hs (h₁, 1))⁻¹ * (secondBlock o hs v * g) =
      secondBlock o hs v * ((blockEmb hs (h₁, 1))⁻¹ * g) := by
  simp [secondBlock, ← mul_assoc, ← map_inv, ← map_mul]

omit [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] in
@[fun_prop] lemma continuous_movedFrame : Continuous (movedFrame (E := E) o) := by
  unfold movedFrame
  fun_prop

omit [DecidableEq n] [DecidableEq n₁] in
@[fun_prop] lemma continuous_frameChar [WeilData E] (T : Set (FinPlace E)) :
    Continuous (frameChar (n := n) (n₁ := n₁) T) := by
  unfold frameChar
  fun_prop [matrixToVec]

@[fun_prop] lemma continuous_frameWeight [WeilData E] :
    Continuous (frameWeight (E := E) (n := n) (n₁ := n₁)) :=
  (isVacuum_vacuumFn (s := 1).cont.comp (by fun_prop [matrixToVec])).norm.pow 2

omit [DecidableEq n] [DecidableEq n₁] in
/-- The slice `frameWeight x = vac[α₀ x]` of the vacuum is not zero exactly when all entries of `x`
have integral finite part. -/
lemma frameWeight_ne_zero_iff [WeilData E] {x : Matrix n n₁ (𝔸 E)} :
    frameWeight x ≠ 0 ↔ ∀ (a : n) (b : n₁), (x a b).2 ∈ Ô E := by
  classical
  simp [frameWeight, vacuumFn, matrixToVec, val_scaleIdele_snd]

omit [Fintype n₂] [DecidableEq n₂] in
/-- If the slice `frameWeight` of the vacuum is not zero at the frame `h⁻¹ o₁`, then this frame is
`γ⁻¹ o₁` for some `γ` whose finite part lies in `stdLevel E n`, the group of integral points. -/
lemma exists_movedFrame_eq [WeilData E] {h : G E (1 : n → ℤˣ)}
    (h_weight : frameWeight (movedFrame o h) ≠ 0) :
    ∃ γ : G E (1 : n → ℤˣ), γ.2 ∈ stdLevel E n ∧ movedFrame o γ = movedFrame o h := by
  -- The finite parts `X` of `o₁` and `X'` of `h⁻¹ o₁` are integral orthonormal frames, so Witt's
  -- theorem over `Ô` gives an integral `d` with `d X = X'`.
  let X : Matrix n n₁ (𝔸f E) := inclMatrix (𝔸f E) (o ∘ .inl)
  let X' : Matrix n n₁ (𝔸f E) := h⁻¹.2.val.val * X
  have hX_gram : Xᴴ * (1 : Matrix n n (𝔸f E)) * X = 1 := by
    simp [X, inclMatrix, Matrix.mul_apply, ← ext_iff, Matrix.one_apply]
  have hX'_gram : X'ᴴ * (1 : Matrix n n (𝔸f E)) * X' = 1 :=
    (U.gram_invariant h⁻¹.2 X X).trans hX_gram
  have hX_int : IsIntMatrix (Ô E) X := by
    simp [X, IsIntMatrix, inclMatrix, ite_mem, Matrix.one_apply]
  have hX'_int : IsIntMatrix (Ô E) X' := by
    simpa [movedFrame, firstFrame, X, X', IsIntMatrix, inclMatrix, Matrix.mul_apply,
      Matrix.one_apply] using frameWeight_ne_zero_iff.1 h_weight
  obtain ⟨d, hd_mem, hdX⟩ := witt_Ô_of_orthonormal hX_gram hX'_gram hX_int hX'_int
  -- Take `γ⁻¹` with the infinite part of `h⁻¹` and the finite part `d`.
  let γInv : G E (1 : n → ℤˣ) := (h⁻¹.1, d)
  have h_frame : γInv.adeleMatrix * firstFrame E o = h⁻¹.adeleMatrix * firstFrame E o := by
    ext i j : 1
    suffices γInv.adeleMatrix i (o (.inl j)) = h⁻¹.adeleMatrix i (o (.inl j)) by
      simpa [firstFrame, inclMatrix, Matrix.mul_apply, Matrix.one_apply]
    refine Prod.ext rfl ?_
    simpa [γInv, X, X', inclMatrix, Matrix.mul_apply, Matrix.one_apply] using congrFun₂ hdX i j
  exact ⟨γInv⁻¹, inv_mem hd_mem, by rw [movedFrame, inv_inv, h_frame, movedFrame]⟩

/-- The characters `ψ_u` separate frames away from `T` and its conjugates: two frames with the same
values `frameChar T` agree once their components at these places are removed, that is, after
multiplying by `1 - idemAdele T.conjClosure`, where `idemAdele T.conjClosure` is `1` at these places
and `0` elsewhere. -/
lemma smul_eq_of_frameChar_eq [WeilData E] {T : Set (FinPlace E)} {x x' : Matrix n n₁ (𝔸 E)}
    (h_char_eq : frameChar T x = frameChar T x') :
    (1 - idemAdele T.conjClosure) • x = (1 - idemAdele T.conjClosure) • x' := by
  ext p q : 1
  set e : 𝔸 E := 1 - idemAdele T.conjClosure with he
  -- Test with the `u` supported at the entry `(p, q)`, and use that `ψ` is non-degenerate.
  have h_char (r : 𝔸 E) : stdAddChar E
      (r * (invDifferentIdele E * (e • x) p q - invDifferentIdele E * (e • x') p q)) = 1 := by
    rw [← div_eq_one.2 (congrFun h_char_eq (Pi.single (p, q) r)), frameChar, frameChar,
      ← map_sub_eq_div]
    congr 1
    simp only [single_dotProduct, matrixToVec, Matrix.smul_apply, smul_eq_mul, ← he]
    ring
  exact (invDifferentIdele E).mul_right_inj.1
    (sub_eq_zero.1 (eq_zero_of_forall_stdAddChar_eq_one h_char))

/-- The invariant measure on `U(n₂)(𝔸) \ U(n)(𝔸)`, carried by `U(n)(𝔸)`. -/
noncomputable abbrev blockQuotMeasure : Measure (G E (1 : n → ℤˣ)) :=
  cosetMeasure volume volume (secondBlock (E := E) o hs)

/-- The embedding of the second block is a closed embedding of `U(n₂)(𝔸)` in `U(n)(𝔸)`. -/
lemma isClosedEmbedding_secondBlock : Topology.IsClosedEmbedding (secondBlock (E := E) o hs) :=
  (isClosedEmbedding_blockEmb hs).comp
    ⟨isEmbedding_prodMkRight 1, (isClosedMap_prodMk_left 1).isClosed_range⟩

/-- The period `I(h) = ∫ Y(diag(h₁, h₂) h) dh₂` of a continuous function `Y` on `[U(n)]` is
continuous in `h`. -/
lemma continuous_blockPeriod {Y : G E (1 : n → ℤˣ) → ℂ} (hY_cont : Continuous Y)
    (hY_inv : (stdSpace E n).Γ.FixesLeft Y) (h₁ : G E (1 : n₁ → ℤˣ)) :
    Continuous (blockPeriod o hs Y h₁) := by
  obtain ⟨C, hC⟩ :=
    (isRapid_of_isCocompact hY_cont hY_inv (stdSpace E n).isCocompact_Gamma).bounded
  exact continuous_of_dominated (by fun_prop) (fun h ↦ .of_forall fun h₂ ↦ hC _)
    (integrable_const C) (.of_forall (by fun_prop))

/-- For a continuous function `Y` on `[U(n)]`, the period `I(h) = ∫ Y(diag(h₁, h₂) h) dh₂` is left
invariant under the second block, so it depends only on the frame `h⁻¹ o₁`. -/
lemma blockPeriod_eq_of_movedFrame_eq {Y : G E (1 : n → ℤˣ) → ℂ} (hY_cont : Continuous Y)
    (hY_inv : (stdSpace E n).Γ.FixesLeft Y) (h₁ : G E (1 : n₁ → ℤˣ)) {a b : G E (1 : n → ℤˣ)}
    (hab : movedFrame o a = movedFrame o b) :
    blockPeriod o hs Y h₁ a = blockPeriod o hs Y h₁ b := by
  have h_fix : (a * b⁻¹).adeleMatrix * firstFrame E o = firstFrame E o := by
    calc (a * b⁻¹).adeleMatrix * firstFrame E o = a.adeleMatrix * movedFrame o b := by
          rw [adeleMatrix_mul, Matrix.mul_assoc, movedFrame]
      _ = (a * a⁻¹).adeleMatrix * firstFrame E o := by
          rw [← hab, adeleMatrix_mul, Matrix.mul_assoc, movedFrame]
      _ = firstFrame E o := by simp
  obtain ⟨v, hv⟩ : ∃ v : G E (1 : n₂ → ℤˣ), secondBlock o hs v = a * b⁻¹ :=
    (mem_range_secondBlock o hs).2 h_fix
  have h_inv : (stdSpace E n₂).Γ.FixesLeft fun h₂ ↦ Y (blockEmb hs (h₁, h₂) * b) := by
    intro γ hγ h₂
    simp only [blockEmb_eq_secondBlock_mul o hs h₁ (γ * h₂), blockEmb_eq_secondBlock_mul o hs h₁ h₂,
      map_mul, mul_assoc]
    exact hY_inv _ ((comap_Gamma_secondBlock o hs).ge hγ) _
  have h_shift (h₂ : G E (1 : n₂ → ℤˣ)) :
      blockEmb hs (h₁, h₂) * a = blockEmb hs (h₁, h₂ * v) * b := by
    rw [← mul_inv_eq_iff_eq_mul, mul_assoc, ← hv]
    simp [secondBlock, ← map_mul]
  -- The measure on `[U(n₂)]` is invariant under right translation by `v`.
  have h_translate : ∫ h₂, Y (blockEmb hs (h₁, h₂ * v) * b) ∂(stdSpace E n₂).quotMeasure =
      ∫ h₂, Y (blockEmb hs (h₁, h₂) * b) ∂(stdSpace E n₂).quotMeasure :=
    ((stdSpace E n₂).integral_comp_mul_right v h_inv (by fun_prop)).1
  simpa only [blockPeriod, h_shift] using h_translate

/-- The rational points of the second block are the rational points of `U(n)` that fix the
frame `o₁`. -/
lemma mem_map_Gamma_secondBlock (k : G E (1 : n → ℤˣ)) :
    k ∈ (stdSpace E n₂).Γ.map (secondBlock o hs) ↔
      ∃ γ : U (stdSpace E n).J,
        (γ : Matrix n n E) * inclMatrix E (o ∘ .inl) = inclMatrix E (o ∘ .inl) ∧
          (stdSpace E n).ratEmbed γ = k := by
  have h_fix (γ : U (stdSpace E n).J) : (stdSpace E n).ratEmbed γ ∈ (secondBlock o hs).range ↔
      (γ : Matrix n n E) * inclMatrix E (o ∘ .inl) = inclMatrix E (o ∘ .inl) := by
    rw [mem_range_secondBlock]
    simp [adeleMatrix_ratEmbed, firstFrame, inclMatrix, Matrix.mul_apply, ← ext_iff,
      ← (toAdele (E := E)).injective.eq_iff]
  rw [← comap_Gamma_secondBlock o hs, map_comap_eq, mem_inf]
  constructor
  · rintro ⟨hk, γ, rfl⟩
    exact ⟨γ, (h_fix γ).1 hk, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨(h_fix γ).2 hγ, γ, rfl⟩

/-- The frame attached to `diag(h₁, 1)⁻¹ g` is `g⁻¹ o₁ h₁`. -/
lemma movedFrame_inv_blockEmb_mul (h₁ : G E (1 : n₁ → ℤˣ)) (g : G E (1 : n → ℤˣ)) :
    movedFrame o ((blockEmb hs (h₁, 1))⁻¹ * g) = g⁻¹.adeleMatrix *
      (firstFrame E o * h₁.adeleMatrix) := by
  rw [movedFrame, _root_.mul_inv_rev, inv_inv, adeleMatrix_mul, Matrix.mul_assoc,
    blockEmb_mul_firstFrame]

variable [WeilData E]

/-- The theta integral of a datum `f` for the split space `hyperbolicSpace E n₁` against a rapidly
decreasing function `Y` on `U(n)(𝔸)` converges absolutely term by term (`HasIntegrableTerms`),
because the sum of the norms of the terms grows at most like a power of the height. -/
lemma hasIntegrableTerms_hyperbolicSplitting_of_isRapid {Y : G E (1 : n → ℤˣ) → ℂ}
    (hY : (stdSpace E n).IsRapid Y) (a : AutChar E)
    (f : 𝒮 ((hyperbolicSpace E n₁).hom (stdSpace E n))) (g : G E (hyperbolicSigns n₁)) :
    (hyperbolicSplitting E n₁).HasIntegrableTerms (stdSpace E n) a 1 f g Y := by
  obtain ⟨C, N, h_growth⟩ :=
    (hyperbolicSplitting E n₁).exists_tsum_thetaTerm_le (stdSpace E n) a 1 g
  obtain ⟨C', h_decay⟩ := hY N
  refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _
    ⟨(|C| * ‖f‖ * C').toNNReal, fun h ↦ ?_⟩
  calc ∑' x : Matrix n n₁ E,
        ‖(hyperbolicSplitting E n₁).thetaTerm (stdSpace E n) a 1 f g x h * Y h‖ₑ
      = (∑' x : Matrix n n₁ E,
          ‖(hyperbolicSplitting E n₁).thetaTerm (stdSpace E n) a 1 f g x h‖ₑ) * ‖Y h‖ₑ := by
        simp_rw [enorm_mul, ENNReal.tsum_mul_right]
    _ ≤ ENNReal.ofReal (|C| * ‖f‖ * (stdSpace E n).height h ^ N) * ‖Y h‖ₑ := by grw [h_growth f h]
    _ = ENNReal.ofReal (|C| * ‖f‖ * (‖Y h‖ * (stdSpace E n).height h ^ N)) := by
        rw [← ofReal_norm, ← ENNReal.ofReal_mul' (norm_nonneg _), mul_right_comm, mul_assoc]
    _ ≤ ENNReal.ofReal (|C| * ‖f‖ * C') := by grw [h_decay]

/-- Let `f` be the Heisenberg translate of the vacuum along the vector of the isotropic subspace of
`A.homSource V` that has coordinates `α₀ ū` in the adapted basis, where `α₀ = scaleIdele E` and the
components of `u` at `T` and its conjugates are removed. The theta value of the mixed model of `f`
at the frame `α₀ x` is `c · ψ_u(x) · vac[α₀ x]`, with `c ≠ 0` independent of `x`. Here `ψ_u` is
`frameChar T · u` and `vac[α₀ ·]` is `frameWeight`. The complement of `A` is the zero space
`stdSpace E Empty`, and `θ` is the theta function of its `hom V`. -/
lemma exists_theta_homSlice_eq_mul_frameChar (T : Set (FinPlace E)) (u : n × n₁ → 𝔸 E) :
    let V : Space E n 1 := stdSpace E n
    let A : (hyperbolicSpace E n₁).Splitting (stdSpace E Empty) n₁ := hyperbolicSplitting E n₁
    let f : 𝒮 ((hyperbolicSpace E n₁).hom V) := ((hyperbolicSpace E n₁).hom V).ϱ
      (((A.homSource V).kAdelic * (adaptedHomBasis n₁ V).val) *ᵥ
        (scaleIdele E).val • star ((1 - idemAdele T.conjClosure) • u))
      ((hyperbolicSpace E n₁).hom V).vacElem
    ∃ c ≠ (0 : ℂ), ∀ x : Matrix n n₁ (𝔸 E),
      ((stdSpace E Empty).hom V).θ (A.homSlice V ((scaleIdele E).val • x) f) =
        c * (frameChar T x u * frameWeight x) := by
  intro V A f
  have h_base : IsBaseAdapted A := by
    refine ⟨isOrthoIntegral_hyperbolicSpace.2.of_eq_submatrix_mul (id ⊕ᵥ Empty.elim) .one ?_⟩
    simp [lAdelic, kAdelic, A, hyperbolicSplitting, Matrix.mul_apply, ← ext_iff, Matrix.one_apply]
  -- In the mixed model the vacuum is a nonzero constant times the square norm of `vacuumFn`.
  obtain ⟨c, hc_ne, h_vac⟩ : ∃ c ≠ (0 : ℂ), ∀ z : n × n₁ → 𝔸 E,
      (A.homSource V).slice z ((hyperbolicSpace E n₁).hom V).vacElem =
        (c * ‖vacuumFn ((adaptedHomBasis n₁ V).valᴴ *ᵥ z)‖ ^ 2) •
          ((stdSpace E Empty).hom V).vacElem := by
    simpa using (isAdapted_homSource A V (h := h_base)).slice_omega_vacElem
  refine ⟨c, hc_ne, fun x ↦ ?_⟩
  have h_slice : A.homSlice V ((scaleIdele E).val • x) ((hyperbolicSpace E n₁).hom V).vacElem =
      (c * frameWeight x) • ((stdSpace E Empty).hom V).vacElem := by
    simp [homSlice_eq_adapted_slice, h_vac, frameWeight, ← conjTranspose_mul]
  -- The Heisenberg translation multiplies the mixed model at `α₀ x` by `ψ_u(x)`.
  have h_half (a r : 𝔸 E) : toAdele (j / 2 : E) * ((a + a) * r) = toAdele (j : E) * (a * r) := by
    conv_rhs => rw [← add_halves (j : E), map_add]
    ring
  have h_shift : A.homSlice V ((scaleIdele E).val • x) f = (frameChar T x u : ℂ) •
      A.homSlice V ((scaleIdele E).val • x) ((hyperbolicSpace E n₁).hom V).vacElem := by
    simp [homSlice_eq_adapted_slice, f, V, adelicHeisenberg, star_mulVec, dotProduct_mulVec,
      ← conjTranspose_mul, ← add_mul, h_half, frameChar, invDifferentIdele, mul_assoc]
  have h_one : ((stdSpace E Empty).hom V).θ ((stdSpace E Empty).hom V).vacElem = 1 := by
    simp [vacElem_apply_eq_prod_lineTheta, Finset.univ_eq_empty, funext_iff]
  simp [h_shift, h_slice, h_one, mul_left_comm]

/-- Let `Y` be a continuous function on `[U(n)]` whose descents to the split space
`hyperbolicSpace E n₁` vanish for all data that are vacuum at `T`. Then `ψ_u(x) · vac[α₀ x] · Y(g)`,
with the frame `x = g⁻¹ o₁ h₁` and `o₁ = firstFrame E o`, is integrable over `U(n)(𝔸)` modulo the
rational points of `U(n₂)`, with integral zero. Here `ψ_u(x) = ψ(δ ∑ u_{ij} x_{ij})`
(`frameChar T`), where `δ` generates the inverse different and the terms at `T` and their conjugates
are dropped. Also `vac[α₀ x] = |e(α₀ x)|²` (`frameWeight`), with `e` the vacuum function and
`α₀ = scaleIdele E`. The character of the split space is that of the zero space, `1`, times
`upsilonU1` for each of the `n₁` hyperbolic planes. -/
lemma DescentsVanish.integral_frameChar_eq_zero {T : Set (FinPlace E)} {Y : G E (1 : n → ℤˣ) → ℂ}
    (hY_cont : Continuous Y) (hY_inv : (stdSpace E n).Γ.FixesLeft Y) (h₁ : G E (1 : n₁ → ℤˣ))
    (hkill : DescentsVanish (hyperbolicSpace E n₁) (stdSpace E n) (1 * upsilonU1 ^ Fintype.card n₁)
      T Y)
    (u : n × n₁ → 𝔸 E) :
    let x (g : G E (1 : n → ℤˣ)) : Matrix n n₁ (𝔸 E) := movedFrame o ((blockEmb hs (h₁, 1))⁻¹ * g)
    let ν : Measure (G E (1 : n → ℤˣ)) :=
      ((stdSpace E n₂).Γ.map (secondBlock o hs)).quotMeasure
    Integrable (fun g : G E (1 : n → ℤˣ) ↦ frameChar T (x g) u * frameWeight (x g) • Y g) ν ∧
      ∫ g : G E (1 : n → ℤˣ), frameChar T (x g) u * frameWeight (x g) • Y g ∂ν = 0 := by
  -- The integral is, up to a nonzero factor, a Fourier coefficient of the descent by a Heisenberg
  -- translate `f` of the vacuum; `f` is vacuum at `T`, so this descent is zero.
  intro x ν
  let V : Space E n 1 := stdSpace E n
  let A : (hyperbolicSpace E n₁).Splitting (stdSpace E Empty) n₁ := hyperbolicSplitting E n₁
  let υ : AutChar E := 1 * upsilonU1 ^ Fintype.card n₁
  let f : 𝒮 ((hyperbolicSpace E n₁).hom V) := ((hyperbolicSpace E n₁).hom V).ϱ
    (((A.homSource V).kAdelic * (adaptedHomBasis n₁ V).val) *ᵥ
      (scaleIdele E).val • star ((1 - idemAdele T.conjClosure) • u))
    ((hyperbolicSpace E n₁).hom V).vacElem
  have hf_vac : projOn ((hyperbolicSpace E n₁).hom V) T f = f := by
    simp +contextual [f, mulVec_smul]
  have h_killed : (fun g : G E (hyperbolicSigns n₁) ↦
      ∫ h, pairTheta (hyperbolicSpace E n₁) V υ 1 f (g, h) * Y h ∂V.quotMeasure) = 0 :=
    hkill f hf_vac
  -- Unfold the coefficient at the rational frame `x₀` and the Levi element `g₀` given by `α₀ h₁`.
  let x₀ : Matrix n n₁ E := inclMatrix E (o ∘ .inl)
  let m : GL n₁ (𝔸 E) := scaleIdele E • h₁.toUnitary
  let g₀ : G E (hyperbolicSigns n₁) := A.levi (m, 1)
  have h_terms : A.HasIntegrableTerms V υ 1 f g₀ Y :=
    hasIntegrableTerms_hyperbolicSplitting_of_isRapid
      (isRapid_of_isCocompact hY_cont hY_inv V.isCocompact_Gamma) υ f g₀
  have h_gram : IsUnit (x₀ᴴ * V.J * x₀) :=
    ⟨1, by simp [x₀, V, inclMatrix, Matrix.mul_apply, ← ext_iff, Matrix.one_apply]⟩
  obtain ⟨h_int, h_coeff⟩ : Integrable (fun g ↦ A.thetaTerm V υ 1 f g₀ x₀ g * Y g) ν ∧
      A.centreCoeff (j (E := E) • (x₀ᴴ * V.J * x₀))
          (fun g ↦ ∫ h, pairTheta (hyperbolicSpace E n₁) V υ 1 f (g, h) * Y h ∂V.quotMeasure) g₀ =
        ∫ g, A.thetaTerm V υ 1 f g₀ x₀ g * Y g ∂ν :=
    (A.centreCoeff_eq_integral_stabilizer h_terms hY_cont hY_inv h_gram
      (mem_map_Gamma_secondBlock o hs)).right
  have h_zero : ∫ g, A.thetaTerm V υ 1 f g₀ x₀ g * Y g ∂ν = 0 := by
    rw [← h_coeff, h_killed]
    simp [centreCoeff]
  -- The term of `x₀` is `c · ψ_u(x) · vac[α₀ x]` with `c = c₁ c₂ ≠ 0`: the Levi element contributes
  -- the factor `c₁` and moves the frame to `α₀ x`.
  obtain ⟨c₂, hc₂_ne, h_theta⟩ : ∃ c₂ ≠ (0 : ℂ), ∀ y : Matrix n n₁ (𝔸 E),
      ((stdSpace E Empty).hom V).θ (A.homSlice V ((scaleIdele E).val • y) f) =
        c₂ * (frameChar T y u * frameWeight y) :=
    exists_theta_homSlice_eq_mul_frameChar T u
  -- `c₁` is the scalar by which the Levi element acts in the mixed model.
  let c₁ : ℂ := ((AutChar.spaceChar (1 : AutChar E) (Fintype.card n)).val m.det : ℂ)⁻¹ *
    (√(ideleAbs m.det) : ℝ) ^ Fintype.card n
  have hc_ne : c₁ * c₂ ≠ 0 := by simp [c₁, hc₂_ne]
  have h_frame (g : G E (1 : n → ℤˣ)) :
      g⁻¹.adeleMatrix * (V.x⁻¹.val * x₀.map toAdele) * m.val = (scaleIdele E).val • x g := by
    simp [x, movedFrame_inv_blockEmb_mul, V, m, x₀, firstFrame, Matrix.mul_assoc, Units.smul_def,
      adeleMatrix]
  have h_trivial (g : G E (1 : n → ℤˣ)) (φ : 𝒮 ((stdSpace E Empty).hom V)) :
      pairWeil (stdSpace E Empty) V 1 1 (1, g) φ = φ := by
    simp [pairWeil_apply, Subsingleton.eq_one (G.onHom (1, g))]
  have h_term (g : G E (1 : n → ℤˣ)) : A.thetaTerm V υ 1 f g₀ x₀ g * Y g =
      c₁ * c₂ * (frameChar T (x g) u * frameWeight (x g) • Y g) := by
    rw [Splitting.thetaTerm, homSlice_levi, h_frame, h_trivial, map_smul, h_theta]
    simp only [c₁, smul_eq_mul, Complex.real_smul, mul_assoc]
  simp only [h_term, integral_const_mul, mul_eq_zero_iff_left hc_ne] at h_int h_zero
  exact ⟨(integrable_const_mul_iff hc_ne.isUnit _).1 h_int, h_zero⟩

/-- Integrating first over `[U(n₂)]`. Let `Y` be a continuous function on `[U(n)]` whose descents to
`hyperbolicSpace E n₁`, with character `upsilonU1 ^ n₁`, vanish for all data that are vacuum at `T`.
Set `h = diag(h₁, 1)⁻¹ g`, the frame `x = h⁻¹ o₁` with `o₁ = firstFrame E o`, and
`I(h) = ∫ Y(diag(h₁, h₂) h) dh₂` over `[U(n₂)]`. Then `ψ_u(x) · vac[α₀ x] · I(h)` is integrable over
`U(n₂)(𝔸) \ U(n)(𝔸)` with integral zero. Here `ψ_u(x) = ψ(δ ∑ u_{ij} x_{ij})` without the terms at
`T` and their conjugates, and `vac[α₀ x] = |e(α₀ x)|²`, with `e` the vacuum function and
`α₀ = scaleIdele E`. -/
lemma DescentsVanish.integral_frameChar_mul_blockPeriod_eq_zero {T : Set (FinPlace E)}
    {Y : G E (1 : n → ℤˣ) → ℂ} (hY_cont : Continuous Y) (hY_inv : (stdSpace E n).Γ.FixesLeft Y)
    (h₁ : G E (1 : n₁ → ℤˣ))
    (hkill : DescentsVanish (hyperbolicSpace E n₁) (stdSpace E n) (1 * upsilonU1 ^ Fintype.card n₁)
      T Y)
    (u : n × n₁ → 𝔸 E) :
    let x (g : G E (1 : n → ℤˣ)) : Matrix n n₁ (𝔸 E) := movedFrame o ((blockEmb hs (h₁, 1))⁻¹ * g)
    let I (g : G E (1 : n → ℤˣ)) : ℂ := blockPeriod o hs Y h₁ ((blockEmb hs (h₁, 1))⁻¹ * g)
    Integrable (fun g : G E (1 : n → ℤˣ) ↦ frameChar T (x g) u * frameWeight (x g) • I g)
        (blockQuotMeasure o hs) ∧
      ∫ g : G E (1 : n → ℤˣ), frameChar T (x g) u * frameWeight (x g) • I g
        ∂blockQuotMeasure o hs = 0 := by
  intro x I
  let F (g : G E (1 : n → ℤˣ)) : ℂ := frameChar T (x g) u * frameWeight (x g) • Y g
  have x_inv (v : G E (1 : n₂ → ℤˣ)) (g : G E (1 : n → ℤˣ)) :
      x (secondBlock o hs v * g) = x g := by
    simp only [x, inv_blockEmb_mul_secondBlock_mul, movedFrame_secondBlock_mul]
  have inner (g : G E (1 : n → ℤˣ)) :
      ∫ h₂, F (secondBlock o hs h₂ * g) ∂(stdSpace E n₂).quotMeasure =
        frameChar T (x g) u * frameWeight (x g) • I g := by
    have I_eq : I g = ∫ h₂, Y (secondBlock o hs h₂ * g) ∂(stdSpace E n₂).quotMeasure := by
      refine integral_congr_ae (.of_forall fun h₂ ↦ ?_)
      simp only [blockEmb_eq_secondBlock_mul o hs h₁ h₂, mul_assoc, mul_inv_cancel_left]
    simp only [F, x_inv, integral_const_mul, integral_smul, I_eq]
  let ν : Measure (G E (1 : n → ℤˣ)) := ((stdSpace E n₂).Γ.map (secondBlock o hs)).quotMeasure
  obtain ⟨F_int, F_zero⟩ : Integrable F ν ∧ ∫ g, F g ∂ν = 0 :=
    hkill.integral_frameChar_eq_zero o hs hY_cont hY_inv h₁ u
  have F_cont : Continuous F :=
    (continuous_subtype_val.comp <| (continuous_apply u).comp <|
      (continuous_frameChar T).comp (by fun_prop)).mul (by fun_prop)
  have F_inv : ((stdSpace E n₂).Γ.map (secondBlock o hs)).FixesLeft F := by
    rintro _ ⟨v, hv, rfl⟩ g
    simp only [F, x_inv, hY_inv _ ((comap_Gamma_secondBlock o hs).ge hv)]
  have stages : Integrable (fun g ↦ ∫ h₂, F (secondBlock o hs h₂ * g) ∂(stdSpace E n₂).quotMeasure)
        (blockQuotMeasure o hs) ∧
      ∫ g, F g ∂ν = ∫ g, ∫ h₂, F (secondBlock o hs h₂ * g) ∂(stdSpace E n₂).quotMeasure
        ∂blockQuotMeasure o hs :=
    integral_quotMeasure_eq_integral_cosetMeasure (stdSpace E n₂).Γ volume volume
      (isClosedEmbedding_secondBlock o hs) F_cont.measurable F_inv F_int
  simp only [inner, F_zero] at stages
  exact ⟨stages.left, stages.right.symm⟩

/-- Let `Y` be a continuous function on `[U(n)]` that is right invariant under the integral points
supported on `T` and its conjugates. At points with finite part in `stdLevel E n`, the group of
integral points, the period `I(a)` depends only on the values `ψ_u(a⁻¹ o₁)` of the characters. -/
lemma blockPeriod_eq_of_frameChar_eq {T : Set (FinPlace E)} {Y : G E (1 : n → ℤˣ) → ℂ}
    (hY_cont : Continuous Y) (hY_inv : (stdSpace E n).Γ.FixesLeft Y) (h₁ : G E (1 : n₁ → ℤˣ))
    (hY_level : HasLevel Y (stdLevel E n ⊓ supportedOn n T)) {a b : G E (1 : n → ℤˣ)}
    (ha : a.2 ∈ stdLevel E n) (hb : b.2 ∈ stdLevel E n)
    (hab : frameChar T (movedFrame o a) = frameChar T (movedFrame o b)) :
    blockPeriod o hs Y h₁ a = blockPeriod o hs Y h₁ b := by
  -- The part `k` of `a⁻¹ b` at `T.conjClosure` fixes `Y`, and `a k` has the frame of `b`.
  let k : G E (1 : n → ℤˣ) := closurePart T (a⁻¹ * b)
  have hk_fix (g : G E (1 : n → ℤˣ)) : Y (g * k) = Y g :=
    hY_level k.2 ⟨componentOn_mem_stdLevel (mul_mem (inv_mem ha) hb), componentOn_mem_supportedOn⟩ g
  let e : 𝔸 E := idemAdele T.conjClosure
  have h_away : (1 - e) • movedFrame o a = (1 - e) • movedFrame o b := smul_eq_of_frameChar_eq hab
  have h_moved : (a⁻¹ * b)⁻¹.adeleMatrix * movedFrame o a = movedFrame o b := by
    simp [movedFrame, ← Matrix.mul_assoc, ← adeleMatrix_mul]
  have h_frame : movedFrame o (a * k) = movedFrame o b :=
    calc movedFrame o (a * k) = k⁻¹.adeleMatrix * movedFrame o a := by
          rw [movedFrame, _root_.mul_inv_rev, adeleMatrix_mul, Matrix.mul_assoc, movedFrame]
      _ = e • ((a⁻¹ * b)⁻¹.adeleMatrix * movedFrame o a) + (1 - e) • movedFrame o a := by
          rw [← map_inv, adeleMatrix_closurePart, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
            Matrix.one_mul]
      _ = movedFrame o b := by rw [h_moved, h_away, ← add_smul, add_sub_cancel, one_smul]
  rw [← blockPeriod_eq_of_movedFrame_eq o hs hY_cont hY_inv h₁ h_frame]
  simp only [blockPeriod, ← mul_assoc, hk_fix]

/-- Split the basis of the definite space of rank `n` by `o : n₁ ⊕ n₂ ≃ n`, and let `o₁` be the
frame of the first `n₁` basis vectors. Let `Y` be a continuous function on `U(n)(𝔸)`. It is left
invariant under the rational points. It is right invariant (`HasLevel`) under the integral points
(`stdLevel`) supported on the places of `T` and their conjugates (`supportedOn`). Fix `h₁` in
`U(n₁)(𝔸)` and let `I(h) = ∫ Y(diag(h₁, h₂) h) dh₂` over `[U(n₂)]` (`blockPeriod`). Then there is a
continuous `χ` on the product of circles indexed by the adelic `n × n₁` frames `u` with
`star I(h) = χ(u ↦ ψ_u(h⁻¹ o₁))` (`frameChar T`). This holds whenever the frame `x = h⁻¹ o₁`
(`movedFrame`) has `frameWeight x = |e(α₀ x)|² ≠ 0`, where `e` is the vacuum function and
`α₀ = scaleIdele E`. Here `ψ_u(x) = ψ(δ ∑ u_{ij} x_{ij})`, with `ψ` the standard additive character,
`δ = invDifferentIdele E`, and the components at the places of `T` and their conjugates set to
zero. -/
lemma exists_continuousMap_eq_conj_blockPeriod (o : n₁ ⊕ n₂ ≃ n)
    (hs : (1 : n → ℤˣ) ∘ o = (1 : n₁ → ℤˣ) ⊕ᵥ (1 : n₂ → ℤˣ))
    {T : Set (FinPlace E)} {Y : G E (1 : n → ℤˣ) → ℂ}
    (hY_cont : Continuous Y) (hY_inv : (stdSpace E n).Γ.FixesLeft Y) (h₁ : G E (1 : n₁ → ℤˣ))
    (hY_level : HasLevel Y (stdLevel E n ⊓ supportedOn n T)) :
    ∃ χ : C((n × n₁ → 𝔸 E) → Circle, ℂ), ∀ h : G E (1 : n → ℤˣ),
      frameWeight (movedFrame o h) ≠ 0 →
        χ (frameChar T (movedFrame o h)) = star (blockPeriod o hs Y h₁ h) := by
  -- On the compact set `K` of points with integral finite part the period depends only on the
  -- values of the characters, and every frame of nonzero weight comes from a point of `K`.
  let K : Set (G E (1 : n → ℤˣ)) := Set.univ ×ˢ (stdLevel E n : Set (Gf E n))
  have mem_K (a : G E (1 : n → ℤˣ)) : a ∈ K ↔ a.2 ∈ stdLevel E n :=
    and_iff_right (Set.mem_univ a.1)
  have K_compact : CompactSpace K :=
    isCompact_iff_compactSpace.1 (isCompact_univ.prod isCompact_stdLevel)
  have I_cont : Continuous (blockPeriod o hs Y h₁) := continuous_blockPeriod o hs hY_cont hY_inv h₁
  let chars : C(K, (n × n₁ → 𝔸 E) → Circle) :=
    ⟨fun a ↦ frameChar T (movedFrame o (a : G E (1 : n → ℤˣ))), by fun_prop⟩
  let conjPeriod : C(K, ℂ) := ⟨fun a ↦ star (blockPeriod o hs Y h₁ a), by fun_prop⟩
  have h_fibre (a b : K) (hab : chars a = chars b) : conjPeriod a = conjPeriod b := by
    have h_period : blockPeriod o hs Y h₁ a = blockPeriod o hs Y h₁ b :=
      blockPeriod_eq_of_frameChar_eq o hs hY_cont hY_inv h₁ hY_level
        ((mem_K a).1 a.property) ((mem_K b).1 b.property) hab
    exact congrArg star h_period
  obtain ⟨χ, hχ⟩ : ∃ χ : C((n × n₁ → 𝔸 E) → Circle, ℂ), ∀ a : K, χ (chars a) = conjPeriod a :=
    exists_continuousMap_comp_eq chars conjPeriod h_fibre
  refine ⟨χ, fun h h_weight ↦ ?_⟩
  obtain ⟨γ, hγ, h_frame⟩ :
      ∃ γ : G E (1 : n → ℤˣ), γ.2 ∈ stdLevel E n ∧ movedFrame o γ = movedFrame o h :=
    exists_movedFrame_eq o h_weight
  calc χ (frameChar T (movedFrame o h)) = χ (frameChar T (movedFrame o γ)) := by rw [h_frame]
    _ = star (blockPeriod o hs Y h₁ γ) := hχ ⟨γ, (mem_K γ).2 hγ⟩
    _ = star (blockPeriod o hs Y h₁ h) := by
        rw [blockPeriod_eq_of_movedFrame_eq o hs hY_cont hY_inv h₁ h_frame]

omit [DecidableEq n] [DecidableEq n₁] in
/-- Stone–Weierstrass: let `x` be a continuous family of frames. Let `ψ_u = frameChar T · u` be
`x ↦ ψ(δ ∑ u_{ij} x_{ij})`, where `ψ` is the standard additive character, `δ` is an idele generating
the inverse different, and the components at the places of `T` and their conjugates are set to zero.
If `ψ_u(x(g)) w(g)` is integrable with integral zero for all `u`, then the same holds with `ψ_u`
replaced by any continuous function `χ` of the values `u ↦ ψ_u(x(g))`. -/
lemma integral_continuousMap_frameChar_eq_zero {T : Set (FinPlace E)} {Z : Type}
    [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] {ν : Measure Z}
    {x : Z → Matrix n n₁ (𝔸 E)} (hx : Continuous x) {w : Z → ℂ}
    (hw_int : ∀ u : n × n₁ → 𝔸 E, Integrable (fun g : Z ↦ frameChar T (x g) u * w g) ν)
    (hw_zero : ∀ u : n × n₁ → 𝔸 E, ∫ g : Z, frameChar T (x g) u * w g ∂ν = 0)
    (χ : C((n × n₁ → 𝔸 E) → Circle, ℂ)) :
    Integrable (fun g : Z ↦ χ (frameChar T (x g)) * w g) ν ∧
      ∫ g : Z, χ (frameChar T (x g)) * w g ∂ν = 0 := by
  have w_int : Integrable w ν := by simpa [frameChar] using hw_int 0
  have integrable (χ : C((n × n₁ → 𝔸 E) → Circle, ℂ)) :
      Integrable (fun g ↦ χ (frameChar T (x g)) * w g) ν :=
    w_int.bdd_mul (by fun_prop) (.of_forall fun g ↦ χ.norm_coe_le_norm _)
  -- The integral is a continuous functional `Λ` of `χ`.
  let Λ : C((n × n₁ → 𝔸 E) → Circle, ℂ) →L[ℂ] ℂ :=
    strongIntegral ν fun g ↦ (evalCLM (M := ℂ) ℂ (frameChar T (x g))).smulRight (w g)
  have Λ_apply (χ : C((n × n₁ → 𝔸 E) → Circle, ℂ)) :
      Λ χ = ∫ g, χ (frameChar T (x g)) * w g ∂ν := strongIntegral_apply _ _ integrable χ
  -- The functions that agree with some `ψ_u` on frames form a monoid that is closed under
  -- conjugation and separates points, and `Λ` vanishes on it.
  let chars : Submonoid C((n × n₁ → 𝔸 E) → Circle, ℂ) :=
    { carrier := {χ | ∃ u : n × n₁ → 𝔸 E, ∀ y : Matrix n n₁ (𝔸 E),
        χ (frameChar T y) = frameChar T y u}
      mul_mem' := fun ⟨u, hu⟩ ⟨v, hv⟩ ↦
        ⟨u + v, by simp [hu, hv, frameChar, mul_add, map_add_eq_mul]⟩
      one_mem' := ⟨0, by simp [frameChar]⟩ }
  have dense : Dense (Submodule.span ℂ (chars : Set C((n × n₁ → 𝔸 E) → Circle, ℂ)) :
      Set C((n × n₁ → 𝔸 E) → Circle, ℂ)) := by
    refine stone_weierstrass_span chars ?_ ?_
    · rintro χ ⟨u, hu⟩
      exact ⟨-u, by simp [frameChar, hu, map_neg_eq_inv, ← Circle.coe_inv_eq_conj]⟩
    · intro z z' hz
      funext u
      exact Circle.ext (hz ⟨fun c ↦ c u, by fun_prop⟩ ⟨u, fun _ ↦ rfl⟩)
  have Λ_zero : Λ = 0 := Λ.ext_on dense fun χ ⟨u, hu⟩ ↦ by simpa [Λ_apply, hu] using hw_zero u
  exact ⟨integrable χ, by simp [← Λ_apply, Λ_zero]⟩

/-- From descents to periods. Let `Y` be a continuous function on `[U(n)]` that is right invariant
(`HasLevel`) under the elements of `stdLevel E n` with component 1 at every place outside `T` and
its conjugate places, and split the basis as `n₁ ⊕ n₂`. Suppose the integrals over `[U(n)]` of `Y`
against the theta kernels of the hyperbolic space of rank `2 n₁`, twisted by `upsilonU1 ^ card n₁`
of the determinant, vanish for all data on `Hom` that are vacua at the places of `T` and their
conjugates. Then `∫ Y(diag(h₁, h₂)) dh₂ = 0` over `[U(n₂)]`, for all `h₁`. -/
lemma integral_blockEmb_eq_zero_of_descentsVanish {T : Set (FinPlace E)} {Y : G E (1 : n → ℤˣ) → ℂ}
    (hY_cont : Continuous Y)
    (hY_inv : (stdSpace E n).Γ.FixesLeft Y) (hY_level : HasLevel Y (stdLevel E n ⊓ supportedOn n T))
    (o : n₁ ⊕ n₂ ≃ n) (hs : (1 : n → ℤˣ) ∘ o = (1 : n₁ → ℤˣ) ⊕ᵥ (1 : n₂ → ℤˣ))
    (hkill : DescentsVanish (hyperbolicSpace E n₁) (stdSpace E n) (1 * upsilonU1 ^ Fintype.card n₁)
      T Y)
    (h₁ : G E (1 : n₁ → ℤˣ)) :
    ∫ h₂ : G E (1 : n₂ → ℤˣ), Y (blockEmb hs (h₁, h₂)) ∂(stdSpace E n₂).quotMeasure = 0 := by
  -- A Fourier coefficient of the descents, integrated first over `[U(n₂)]`, makes `vac[α₀ x] · I`
  -- orthogonal to every character `ψ_u` of the frame `x`, hence to every continuous function of
  -- these characters. Where `vac[α₀ x] ≠ 0` the conjugate of `I` is such a function, so
  -- `vac[α₀ x] · |I|²` has integral zero. Below `I` is shifted by `g₀⁻¹`, and `I g₀` is the period.
  let g₀ : G E (1 : n → ℤˣ) := blockEmb hs (h₁, 1)
  let x (g : G E (1 : n → ℤˣ)) : Matrix n n₁ (𝔸 E) := movedFrame o (g₀⁻¹ * g)
  let I (g : G E (1 : n → ℤˣ)) : ℂ := blockPeriod o hs Y h₁ (g₀⁻¹ * g)
  have I_cont : Continuous I :=
    (continuous_blockPeriod o hs hY_cont hY_inv h₁).comp (continuous_const_mul g₀⁻¹)
  obtain ⟨χ, hχ⟩ : ∃ χ : C((n × n₁ → 𝔸 E) → Circle, ℂ), ∀ h : G E (1 : n → ℤˣ),
      frameWeight (movedFrame o h) ≠ 0 →
        χ (frameChar T (movedFrame o h)) = star (blockPeriod o hs Y h₁ h) :=
    exists_continuousMap_eq_conj_blockPeriod o hs hY_cont hY_inv h₁ hY_level
  have h_orth (u : n × n₁ → 𝔸 E) :
      Integrable (fun g ↦ frameChar T (x g) u * frameWeight (x g) • I g) (blockQuotMeasure o hs) ∧
        ∫ g, frameChar T (x g) u * frameWeight (x g) • I g ∂blockQuotMeasure o hs = 0 :=
    hkill.integral_frameChar_mul_blockPeriod_eq_zero o hs hY_cont hY_inv h₁ u
  let F (g : G E (1 : n → ℤˣ)) : ℂ := χ (frameChar T (x g)) * frameWeight (x g) • I g
  obtain ⟨F_int, F_zero⟩ :
      Integrable F (blockQuotMeasure o hs) ∧ ∫ g, F g ∂blockQuotMeasure o hs = 0 :=
    integral_continuousMap_frameChar_eq_zero (by fun_prop) (fun u ↦ (h_orth u).left)
      (fun u ↦ (h_orth u).right) χ
  let ρ (g : G E (1 : n → ℤˣ)) : ℝ := frameWeight (x g) * ‖I g‖ ^ 2
  have F_eq : F = fun g ↦ (ρ g : ℂ) := by
    funext g
    obtain hg | hg := eq_or_ne (frameWeight (x g)) 0
    · simp [F, ρ, hg]
    · have hχg : χ (frameChar T (x g)) = star (I g) := hχ (g₀⁻¹ * g) hg
      calc F g = frameWeight (x g) • (star (I g) * I g) := by simp only [F, hχg, mul_smul_comm]
        _ = ρ g := by simp [ρ, Complex.conj_mul']
  have ρ_inv (v : G E (1 : n₂ → ℤˣ)) (g : G E (1 : n → ℤˣ)) :
      ρ (secondBlock o hs v * g) = ρ g := by
    have x_inv : x (secondBlock o hs v * g) = x g := by
      simp only [x, g₀, inv_blockEmb_mul_secondBlock_mul, movedFrame_secondBlock_mul]
    simp only [ρ, x_inv, I, blockPeriod_eq_of_movedFrame_eq o hs hY_cont hY_inv h₁ x_inv]
  have ρ_int : Integrable ρ (blockQuotMeasure o hs) := by simpa [F_eq] using F_int.re
  have ρ_integral : ∫ g, ρ g ∂blockQuotMeasure o hs = 0 := by
    simpa [F_eq, integral_complex_ofReal] using F_zero
  have ρ_zero : ρ = 0 := eq_zero_of_integral_cosetMeasure_eq_zero volume volume
    (isClosedEmbedding_secondBlock o hs) (by fun_prop)
    (fun g ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) ρ_inv ρ_int ρ_integral
  -- At `g₀` the frame is `o₁`, which is integral.
  have weight_ne : frameWeight (x g₀) ≠ 0 := by
    simp only [x, inv_mul_cancel]
    exact frameWeight_ne_zero_iff.2
      (by simp [movedFrame, firstFrame, inclMatrix, Matrix.one_apply, apply_ite])
  have I_zero : I g₀ = 0 := by simpa [ρ, weight_ne] using congrFun ρ_zero g₀
  simpa [I, blockPeriod] using I_zero

end New.SiegelWeil
