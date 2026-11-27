import Lib.Shimura.HeckeTower.Model
import Lib.Shimura.Uniformisation.TorusModel

/-!
# Every full complex object is modelled on a point (g, ℓ)

From a complex point of a family of abelian schemes back to linear algebra: an object `x` over `ℂ`
with structure map `Φ v₀` (the complex embedding of `E` at the fixed infinite place `v₀`) on `𝓞 E`
and a full structure `e` (a trivialisation of all torsion, `New.ThetaObject.FullLevelStructure`) is
a complex torus described by an adelic frame `g` and a reflection `ℓ`.

* `New.Variety.exists_torusModel`: a polarised period map on `ℂ^d` for `(g, ℓ)` and a model of `x`
  on it whose torsion points are those of `e`, with `ℓ` a reflection.
* `New.Variety.exists_torusModel_of_isPeriodMap`: the same model on a given period map `Q` whose
  exponential lifts the torsion points of `e`; the frame is found from the Weil pairing of `e`.

`New.ThetaObject.TorusModel` is a model of `x` on a given polarised period map `Q`
(`New.ThetaTori.PeriodMap`). It is a uniformisation of `x.groupScheme` whose kernel is the period
lattice.

Notions from other files:
* `New.ψf`: the additive character of the finite adeles with ψ_f(x) = exp(2πi Tr_{E/ℚ}(a)) for any a
  in E with x − a integral. In the code `𝐞 t` is exp(2πi t).
* `New.ThetaObject.groupScheme`: The group scheme with O_E-action of an object x over S: the
  pull-back of the abelian scheme of the family along x : S → base.
* `New.ThetaObject.baseHom`: For an object x over Spec R, the ring homomorphism O_E → R induced by x
  and the structure morphism of the base of the family to Spec O_E.
* `New.ThetaObject`: An object of the family X over a scheme T: a morphism from T to the base of X.

## Relation to the literature

Known; see `Lib.Shimura.Uniformisation.AppellHumbert` for sources.
-/

open CategoryTheory NumberField Matrix FourierTransform LinearMap BilinForm Complex OrzechProperty
  Submodule ContinuousLinearMap Circle RingOfIntegers Finset

namespace New.Variety

/- `x` is an object over `ℂ` of the family `X` over `Z`, and `e` is a full structure on it. -/
variable {E : Type} [Field E] [CMBase E] {D : PEL E} {Z : AlgebraicGeometry.Scheme}
  {τ : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {x : ThetaObject X (AlgebraicGeometry.Spec ⟨ℂ⟩)} (e : x.FullLevelStructure)

/-- Let `u` uniformise `x.groupScheme`, with theta coordinates `θ` of type `(B, χ)` for
`x.lineBundle`, and let the torsion point of `e` at the class of `m *ᵥ y` be `u.expMap (Q y)` for
each `y` in `Eⁿ`. Then there is a unit `ε` (from the Weil pairing of `e`) such that on vectors of
`Eⁿ`, `𝐞` of the Riemann form of `B` pulled back by `Q` is `ψf` of the form `xiForm D.ξ`,
`(a, b) ↦ D.ξ · bᴴ a` on adelic vectors (`y` enters as `frameCoords 1 y`), with the matrix
`ε mᴴ m`. -/
lemma exists_fourierChar_riemannForm_eq_ψf_xiForm {V : Type} [FinComplexSpace V]
    {m : Matrix D.Index D.Index (𝔸f E)} (u : Uniformisation x.groupScheme V)
    (Q : RealVectors E D.Index ≃L[ℝ] V)
    (h_ev : ∀ y : D.Index → E,
      e.torsionPoint (torsionClass (m *ᵥ frameCoords 1 y)) = u.expMap (Q (toRealVectors y)))
    {B : ThetaTori.LatticeForm u.lattice} {χ : V → ℂ} {θ : V → D.dualTorsion → ℂ}
    (h_theta : HasThetaCoords u.lattice (atGeneric u.expMap) x.lineBundle B χ θ) :
    ∃ ε : (Ô ℚ)ˣ, ∀ y z : D.Index → E,
      𝐞 (LinearMap.BilinForm.congr Q.toLinearEquiv.symm B.riemannForm (toRealVectors y)
          (toRealVectors z)) =
        ψf E (xiForm D.ξ ((finAdeleIncl ℚ E ε • mᴴ * m) *ᵥ frameCoords 1 y) (frameCoords 1 z)) := by
  obtain ⟨ε, h_pair⟩ := e.weil_pairing 1
  refine ⟨ε, fun y z ↦ ?_⟩
  -- Take `N` with `N m y`, `N m z` integral and write `y = N y'`, `z = N z'`; then `N²` kills
  -- the classes of `m y'` and `m z'`.
  obtain ⟨N, hN, h_int⟩ := exists_forall_mul_mem_Ô (m *ᵥ frameCoords 1 y ⊕ᵥ m *ᵥ frameCoords 1 z)
  have hN_int : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  obtain ⟨y', rfl⟩ := DivisibleBy.surjective_smul (D.Index → E) ℤ hN_int y
  obtain ⟨z', rfl⟩ := DivisibleBy.surjective_smul (D.Index → E) ℤ hN_int z
  obtain ⟨hy', hz'⟩ :
      (N * N) • torsionClass (m *ᵥ frameCoords 1 y') = 0 ∧
      (N * N) • torsionClass (m *ᵥ frameCoords 1 z') = 0 := by
    simpa [← nsmul_eq_mul, smul_smul, ← torsionClass_eq_zero (n := D.Index), ← Pi.smul_def,
      mulVec_smul] using h_int
  -- lifts `Ty`, `Tz` of the translations by the two torsion points acting on sections of
  -- `x.lineBundle.pow (N * N)`
  obtain ⟨Ty, hTy⟩ := e.exists_isTranslationLift hy'
  obtain ⟨Tz, hTz⟩ := e.exists_isTranslationLift hz'
  -- the scalar by which `Ty` and `Tz` commute is the Weil pairing of the two classes
  obtain ⟨c, rfl, h_comm⟩ :=
    h_pair (N * N) (m *ᵥ frameCoords 1 y') (m *ᵥ frameCoords 1 z') hy' hz'
  specialize h_comm Ty Tz hTy hTz
  rw [h_ev] at hTy hTz
  -- the same scalar is the Riemann phase, by `lift_commutator_iff_weil_pairing`
  have h_phase : (ψf E (finAdeleIncl ℚ E ε *
        ((N * N : ℕ) * xiForm D.ξ (m *ᵥ frameCoords 1 y') (m *ᵥ frameCoords 1 z'))) : ℂ) =
      𝐞 ((N * N : ℕ) * B.riemannForm (Q (toRealVectors y')) (Q (toRealVectors z'))) := by
    simpa using (lift_commutator_iff_weil_pairing u h_theta hTy hTz).mp h_comm
  -- the factor `N²` is shared between the two arguments, and `mᴴ` moves across the form
  calc _ = 𝐞 ((N * N : ℕ) * B.riemannForm (Q (toRealVectors y')) (Q (toRealVectors z'))) := by
        simp [← nsmul_eq_mul]
    _ = ψf E (finAdeleIncl ℚ E ε * ((N * N : ℕ) *
          xiForm D.ξ (m *ᵥ frameCoords 1 y') (m *ᵥ frameCoords 1 z'))) := Circle.ext h_phase.symm
    _ = _ := by
        simp [star_trivial, xiForm, star_mulVec_dotProduct, ← nsmul_eq_mul, mul_left_comm,
          mulVec_smul, smul_mulVec]

/-- Let `R` be a real bilinear form on `(E ⊗ ℝ)ⁿ` and `M` an `n × n` matrix of finite adeles such
that `𝐞 (R y z) = ψf (ξ · zᴴ M y)` for all `y`, `z` in `Eⁿ`, where `ψf` is the standard additive
character of the finite adeles and `ξ = D.ξ`, with `Φ v₀ ξ` of zero real part and positive imaginary
part. Then `M` is the image of a matrix `β` over `E`, and `R` is the polarisation form of `β`,
namely `(y, z) ↦ Σ_v 2 Re(Φ_v(ξ) z_vᴴ Φ_v(β) y_v)` summed over the infinite places `v`. -/
lemma exists_map_eq_and_eq_polarisationForm_of_fourierChar_eq
    (R : LinearMap.BilinForm ℝ (RealVectors E D.Index)) (M : Matrix D.Index D.Index (𝔸f E))
    (h_weil : ∀ y z : D.Index → E,
      𝐞 (R (toRealVectors y) (toRealVectors z)) =
        ψf E (xiForm D.ξ (M *ᵥ frameCoords 1 y) (frameCoords 1 z))) :
    ∃ β : D.Index → D.Index → E, (of β).map (↑) = M ∧ R = polarisationForm D (of β) := by
  -- Values of `ψf` are `𝐞` of rational numbers, so `R` is rational on `Eⁿ`: `r z y` is the
  -- rational value of `R y z`.
  have h_rat (z y : D.Index → E) : ∃ q : ℚ, q = R (toRealVectors y) (toRealVectors z) := by
    obtain ⟨a, j, hj⟩ : ∃ (a : ℚ) (j : ℤ), R (toRealVectors y) (toRealVectors z) - a = j := by
      simp only [← fourierChar_eq_one_iff, AddChar.map_sub_eq_div, div_eq_one]
      exact ⟨_, h_weil y z⟩
    exact ⟨j + a, mod_cast (eq_add_of_sub_eq hj).symm⟩
  choose r hr using h_rat
  -- Trace duality: the `ℚ`-linear form `t ↦ R (ξ⁻¹ t e_j, e_i)` is `t ↦ tr (β i j * t)`.
  have h_dual (i j : D.Index) : ∃ c : E, ∀ t : E,
      Algebra.trace ℚ E (c * t) = r (Pi.single i 1) (Pi.single j (D.ξ⁻¹ * t)) := by
    let f : E →+ ℚ := AddMonoidHom.mk' (fun t ↦ r (Pi.single i 1) (Pi.single j (D.ξ⁻¹ * t)))
      (by simp [hr, mul_add, Pi.single_add, ← Rat.cast_inj (α := ℝ)])
    obtain ⟨c, hc⟩ := (toDual _ (traceForm_nondegenerate ℚ E)).surjective f.toRatLinearMap
    exact ⟨c, fun t ↦ by simpa [LinearMap.BilinForm.toDual_def, f] using LinearMap.congr_fun hc t⟩
  choose β h_tr using h_dual
  have hξ : D.ξ ≠ 0 := by
    obtain ⟨h_im_pos, -⟩ := D.xi_im_pos_and_re_eq_zero v₀
    exact ne_zero_of_map (ne_of_apply_ne im h_im_pos.ne')
  -- `ψf` separates adeles, and it is enough to test against the dense set of `t` in `E`.
  have hβ : (of β).map (↑) = M := by
    refine ext fun i j ↦ ?_
    have h_dense (t : E) :
        ψf E (algebraMap E (𝔸f E) t * (of β).map (↑) i j) =
          ψf E (algebraMap E (𝔸f E) t * M i j) := by
      simp [ψf_coe, ← map_mul, mul_comm t, xiForm, frameCoords, dotProduct, mulVec, apply_ite,
        mul_comm (M i j), ← mul_assoc, hξ, h_tr, hr, h_weil, Pi.single_apply]
    exact eq_of_forall_ψf_mul_eq (denseRange_algebraMap_finAdele.eq fun t ↦ h_dense t)
  -- By density take `y` in `Eⁿ`. By `h_weil`, `𝐞` of the linear form
  -- `R y - polarisationForm D β y` is `1` on the dense set `Eⁿ`, hence everywhere, so the form
  -- is `0`.
  have hR : R = polarisationForm D (of β) := by
    refine ext (isClosed_property denseRange_toRealVectors
      (R.eqLocus _).closed_of_finiteDimensional fun y ↦ ?_)
    refine sub_eq_zero.mp (eq_zero_of_forall_fourierChar_eq_one _ (denseRange_toRealVectors.eq ?_))
    simp [h_weil, ← hβ, 𝐞.map_sub_eq_div, ← ψf_coe, xiForm, frameCoords, dotProduct, mulVec]
  exact ⟨β, hβ, hR⟩

/-- Let `x` over `ℂ` have structure map `Φ v₀` on `𝓞 E` and full structure `e`, let `u` uniformise
`x.groupScheme` by `V`, and let `Q : (E ⊗ ℝ)ⁿ ≃ V` be a period map for `ℓ` (`i` acts as `i ℓ` at
`v₀`, as `i` elsewhere) with `u.expMap ∘ Q` `𝓞 E`-linear, sending `y` in `Eⁿ` to the torsion point
of `e` at the class of `m *ᵥ y`, and with `u.lattice` in `Q (Eⁿ)`. Then for some adelic frame `g`, a
polarised period map `Y` for `(g, ℓ)` on `V` has a model `M` of `x` with `e`'s torsion points. -/
lemma exists_torusModel_of_isPeriodMap
    (hρ : ∀ c : 𝓞 E, x.baseHom c = Φ v₀ c.val) {V : Type} [FinComplexSpace V]
    {ℓ : Matrix D.Index D.Index ℂ} {m : Matrix D.Index D.Index (𝔸f E)}
    (u : Uniformisation x.groupScheme V) (Q : RealVectors E D.Index ≃L[ℝ] V)
    (h_per : IsPeriodMap ℓ Q)
    (h_smul : ∀ (c : 𝓞 E) (w : RealVectors E D.Index),
      u.expMap (Q (cmEmbedding c.val • w)) = c • u.expMap (Q w))
    (h_ev : ∀ y : D.Index → E,
      e.torsionPoint (torsionClass (m *ᵥ frameCoords 1 y)) = u.expMap (Q (toRealVectors y)))
    (h_lat : ∀ z ∈ u.lattice, ∃ y : D.Index → E, Q (toRealVectors y) = z) :
    ∃ g : GL D.Index (𝔸f E), ∃ᵉ (Y : ThetaTori.PeriodMap D g ℓ V) (M : x.TorusModel Y),
      M.fullStructure.torsionPoint = e.torsionPoint := by
  -- Appell–Humbert: the coordinates of `x.lineBundle` are theta functions `θ` of a type `(B, χ)`
  -- with positive Riemann form; `R` is that form on `(E ⊗ ℝ)ⁿ`. The Weil pairing computes `R` on
  -- vectors of `Eⁿ` and shows that `R` is the polarisation form of a matrix `β` over `E` with
  -- image `M = ε mᴴ m`. Nondegeneracy makes `m` invertible, and `m⁻¹` is the frame.
  -- the parallelogram law, the first of the class laws of `x.lineBundle`
  obtain ⟨h_par, -⟩ := x.hasClassLaws
  obtain ⟨B, χ, θ, h_theta, h_pos⟩ := u.appell_humbert x.isProjEmbedding h_par
  obtain ⟨ε, h_weil⟩ := exists_fourierChar_riemannForm_eq_ψf_xiForm e u Q h_ev h_theta
  let R : LinearMap.BilinForm ℝ (RealVectors E D.Index) := congr Q.toLinearEquiv.symm B.riemannForm
  let M : Matrix D.Index D.Index (𝔸f E) := finAdeleIncl ℚ E ε • mᴴ * m
  obtain ⟨β, hβ, hR⟩ := exists_map_eq_and_eq_polarisationForm_of_fourierChar_eq R M h_weil
  -- The Riemann form is nondegenerate, so `β`, then `M` and its right factor `m`, are invertible.
  have hβ_inj : Function.Injective (of β).mulVec := by
    intro y z h_mulVec
    have h_eq : R (toRealVectors y) = R (toRealVectors z) :=
      ext (denseRange_toRealVectors.eq (by simp [hR, h_mulVec]))
    exact toRealVectors_injective
      (R.ker_eq_bot.mp (h_pos.nondegenerate.congr Q.toLinearEquiv.symm).ker_eq_bot h_eq)
  have hM : IsUnit M := by
    rw [← hβ]
    exact (mulVec_injective_iff_isUnit.mp hβ_inj).map (RingHom.mapMatrix _)
  obtain ⟨m, rfl⟩ : IsUnit m := isUnit_of_mul_isUnit_right hM
  -- `m⁻¹` is a frame for `β`, as `mᴴ (ε • 1) m = β`
  have h_gram : m.valᴴ * (finAdeleIncl ℚ E ε • 1) * m.val = (of β).map (algebraMap E (𝔸f E)) := by
    simp [hβ, M]
  replace h_ev (y : D.Index → E) :
      e.torsionPoint (frameTorsionClass m⁻¹ y) = u.expMap (Q (toRealVectors y)) := by
    simpa [frameCoords, frameTorsionClass] using h_ev y
  refine ⟨m⁻¹,
    { formMatrix := of β, realEquiv := Q, automorphyForm := B, isFrameFor := ⟨ε,
      gram_inv_of_gram_eq h_gram⟩
      isPeriodMap := h_per, re_symm := h_theta.isAppellHumbert.re_symm
      riemannForm_eq := congr_fun₂ hR, isPosRiemann := h_pos },
    { baseHom_eq := hρ, uniformisation := u, χ := χ, θ := θ, hasThetaCoords := h_theta
      equivariant := h_smul, level_eq := ?_, lattice_eq := ?_ }, ?_⟩
  · simp [e.levelPoints_eq, ThetaTori.PeriodMap.torsionLift, ← h_ev]
  · -- a vector of `u.lattice` is a `Q (toRealVectors y)` by `h_lat`, and `e.torsionPoint` is
    -- injective
    ext w
    suffices h_iff : u.expMap w = 0 ↔
        ∃ y : D.Index → E, u.expMap (Q (toRealVectors y)) = 0 ∧ Q (toRealVectors y) = w by
      simpa [mem_classLattice, ← e.injective.eq_iff, h_ev] using h_iff
    refine ⟨fun hw ↦ ?_, fun ⟨y, hy, hyw⟩ ↦ by rwa [← hyw]⟩
    obtain ⟨y, rfl⟩ := h_lat w ((u.eq_zero_iff w).mpr hw)
    exact ⟨y, hw, rfl⟩
  · ext
    simp [ThetaObject.TorusModel.fullStructure, ← h_ev]

/-- Let `u` uniformise `x.groupScheme` and let the real-linear map `P` lift the torsion points of
`e` on the vectors of `½ (𝓞 E)ⁿ`: for `y` in `Eⁿ` with `2 y` integral, `u.expMap (P y)` is the
torsion point of `e` at the class of `y`. Then `P (Eⁿ)` contains the lattice `u.lattice`. -/
lemma lattice_subset_range_of_expMap_eq_torsionPoint {V : Type} [FinComplexSpace V]
    (u : Uniformisation x.groupScheme V) (P : RealVectors E D.Index →ₗ[ℝ] V)
    (hP : ∀ y : D.Index → E,
      2 • y ∈ (frameTorsionClass 1).ker →
      u.expMap (P (toRealVectors y)) = e.torsionPoint (frameTorsionClass 1 y)) :
    ∀ z ∈ u.lattice, ∃ y : D.Index → E, P (toRealVectors y) = z := by
  let _ : Module ℚ V := .compHom V (algebraMap ℚ ℝ)
  -- `N` is the image of the lattice in `V` modulo the `ℚ`-subspace `P (Eⁿ)`
  let p : (D.Index → E) →ₗ[ℚ] V := (P.toAddMonoidHom.comp toRealVectors).toRatLinearMap
  let N : Submodule ℤ (V ⧸ p.range) := u.lattice.map (p.range.mkQ.restrictScalars ℤ)
  -- `N` is stable under `½`: half of a lattice vector maps to a `2`-torsion point
  -- `e.torsionPoint (frameTorsionClass 1 y)`
  have h_half : ∀ w ∈ N, (2⁻¹ : ℚ) • w ∈ N := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨a, rfl⟩ : ∃ a : V, (2 : ℚ) • a = z := MulAction.surjective₀ (two_ne_zero' ℚ) z
    have h_tors : 2 • u.expMap a = 0 := by
      rwa [two_smul, ← map_add, ← two_smul ℚ a, ← u.eq_zero_iff]
    obtain ⟨l, hl⟩ := x.exists_apply_eq_of_torsion e.injective (u.expMap a) ⟨2, two_ne_zero, h_tors⟩
    obtain ⟨y, rfl⟩ : ∃ y : D.Index → E, frameTorsionClass 1 y = l := frameTorsionClass_surjective l
    have h_two_y : 2 • y ∈ (frameTorsionClass 1).ker := by
      simp only [LinearMap.mem_ker, ← e.injective.eq_iff, map_nsmul, hl, h_tors, map_zero]
    -- `a - P y` lies in the lattice: both map to the same point, as `P` lifts it (`hP`)
    refine ⟨a - P (toRealVectors y), ?_, by simp [p]⟩
    exact (u.eq_zero_iff _).mpr (by rw [map_sub, hP y h_two_y, hl, sub_self])
  -- `N` is finitely generated and `½` is not integral over `ℤ`, so `N = 0`
  have hN : N = ⊥ := by
    by_contra hN
    obtain ⟨k, hk⟩ : ∃ k : ℤ, algebraMap ℤ ℚ k = 2⁻¹ := IsIntegrallyClosed.isIntegral_iff.mp
      (isIntegral_of_smul_mem_submodule N hN .of_finite (2⁻¹ : ℚ) h_half)
    simpa using congrArg Rat.den hk
  simpa [N, p, Submodule.eq_bot_iff] using hN

/-- Let `u` uniformise `x.groupScheme` by `Fin (abelianDim E D.Index) → ℂ`, and let `d` be the real
basis of `E ⊗ ℝ` (as `InfinitePlace E → ℂ`) given by an integral basis of `E`. The action of
`𝓞 E` on `x.groupScheme` lifts through `u` to an `ℝ`-linear map `G` from `E ⊗ ℝ` to the
complex-linear maps of that space: `u.expMap (G c z) = c • u.expMap z` for `c` in `𝓞 E`. -/
lemma exists_expMap_apply_cmEmbedding_eq_smul
    (u : Uniformisation x.groupScheme (Fin (abelianDim E D.Index) → ℂ))
    (d : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (InfinitePlace E → ℂ))
    (hd : ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 E), d i = cmEmbedding (basis E i).val) :
    ∃ G : (InfinitePlace E → ℂ) →ₗ[ℝ]
        (Fin (abelianDim E D.Index) → ℂ) →L[ℂ] Fin (abelianDim E D.Index) → ℂ,
      ∀ (c : 𝓞 E) (z : Fin (abelianDim E D.Index) → ℂ),
        u.expMap (G (cmEmbedding c) z) = c • u.expMap z := by
  -- lift each element of the integral basis to a linear map of `Fin (abelianDim E D.Index) → ℂ`,
  -- and extend `ℝ`-linearly
  have h_lift (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
      ∃ F : (Fin (abelianDim E D.Index) → ℂ) →L[ℂ] _, ∀ z : Fin (abelianDim E D.Index) → ℂ,
        u.expMap (F z) = basis E i • u.expMap z := by
    -- `using!`: holomorphy of the composite matches what `u.universal` asks only after unfolding
    -- `IsAddMonHom.addMonoidHom` and `HolomorphicAt`
    simpa using
      u.universal ((IsAddMonHom.addMonoidHom (basis E i • 𝟙 x.groupScheme) _).comp u.expMap)
        (by simpa only [atGeneric_eq] using! (u.immersive 0).1.comp_hom _)
  choose F hF using h_lift
  refine ⟨d.constr ℝ F, fun c z ↦ ?_⟩
  -- expand `c` in the integral basis: both sides are the same `ℤ`-combination over the basis
  rw [← (basis E).sum_repr c]
  -- the `↓` forms and `-zsmul_eq_mul` keep each coefficient a `ℤ`-multiple of `d i`, which
  -- `d.constr` sends to `F i`; with plain `sum_smul` the coefficients become products `↑r * d i`
  simp [← hd, hF, ↓sum_smul, -zsmul_eq_mul, ↓map_sum]

/-- Let `u` uniformise `x.groupScheme` by `V`, and let `Q : (E ⊗ ℝ)ⁿ ≃ V` be such that
`u.expMap ∘ Q` is `𝓞 E`-linear and lifts the torsion points of `e` on the vectors of `½ (𝓞 E)ⁿ`.
Then there is an adelic matrix `m` such that `u.expMap (Q y)` is the torsion point of `e` at the
class of `m *ᵥ y` for every `y` in `Eⁿ`. -/
lemma exists_matrix_torsionPoint_eq_expMap {V : Type} [FinComplexSpace V]
    (u : Uniformisation x.groupScheme V) (Q : RealVectors E D.Index ≃L[ℝ] V)
    (h_half : ∀ y : D.Index → E, 2 • y ∈ (frameTorsionClass 1).ker →
      u.expMap (Q (toRealVectors y)) = e.torsionPoint (frameTorsionClass 1 y))
    (h_smul : ∀ (c : 𝓞 E) (w : RealVectors E D.Index),
      u.expMap (Q (cmEmbedding c.val • w)) = c • u.expMap (Q w)) :
    ∃ m : Matrix D.Index D.Index (𝔸f E), ∀ y : D.Index → E,
      e.torsionPoint (torsionClass (m *ᵥ frameCoords 1 y)) = u.expMap (Q (toRealVectors y)) := by
  -- the points `u.expMap (Q y)` are torsion, so they are `e.torsionPoint (f y)`; `f` is
  -- `𝓞 E`-linear, so `f y` is the class of `m *ᵥ y` for an adelic matrix `m`
  have h_tors_pt (y : D.Index → E) :
      ∃ l : AdelicTorsion E D.Index, e.torsionPoint l = u.expMap (Q (toRealVectors y)) := by
    obtain ⟨k, hk, hky⟩ := exists_nsmul_adelicTorsion_eq_zero (frameTorsionClass 1 y)
    -- `-nsmul_eq_mul` keeps `k • y` a multiple by `k`, so that the linear maps pull `k` out
    exact x.exists_apply_eq_of_torsion e.injective _
      ⟨k, hk, by simpa [hky, -nsmul_eq_mul] using h_half (k • y)⟩
  choose f hf using h_tors_pt
  have hf_add (y y' : D.Index → E) : f (y + y') = f y + f y' := by
    simp [← e.injective.eq_iff, hf]
  have hf_smul (c : 𝓞 E) (y : D.Index → E) : f (c • y) = c • f y := by
    simp [← e.injective.eq_iff, hf, h_smul]
  obtain ⟨m, hm⟩ : ∃ m : Matrix D.Index D.Index (𝔸f E), ∀ y : D.Index → E,
      torsionClass (m *ᵥ frameCoords 1 y) = f y :=
    exists_matrix_torsionClass_eq ⟨⟨f, hf_add⟩, hf_smul⟩
  exact ⟨m, fun y ↦ by rw [hm, hf]⟩

/-- Let `u` uniformise `x.groupScheme` by `Fin (abelianDim E D.Index) → ℂ`, let `G` lift the action
of `𝓞 E` through `u`, and let `l j` lift the torsion point of `e` at the class of `e_j / 2`.
The real-linear map `P = ∑ j, (w ↦ G (w j) (2 l j))` lifts the torsion points of `e` on the
vectors of `½ (𝓞 E)ⁿ`: for `y` in `Eⁿ` with `2 y` integral, `u.expMap (P y)` is the torsion
point of `e` at the class of `y`. -/
lemma expMap_apply_toRealVectors_eq_torsionPoint_of_two_smul_mem_ker
    (u : Uniformisation x.groupScheme (Fin (abelianDim E D.Index) → ℂ))
    (G : (InfinitePlace E → ℂ) →ₗ[ℝ]
      (Fin (abelianDim E D.Index) → ℂ) →L[ℂ] Fin (abelianDim E D.Index) → ℂ)
    (hG : ∀ (c : 𝓞 E) (z : Fin (abelianDim E D.Index) → ℂ),
      u.expMap (G (cmEmbedding c) z) = c • u.expMap z)
    (l : D.Index → Fin (abelianDim E D.Index) → ℂ)
    (hl : ∀ j : D.Index,
      u.expMap (l j) = e.torsionPoint (frameTorsionClass 1 (Pi.single j 2⁻¹)))
    (y : D.Index → E) (hy : 2 • y ∈ (frameTorsionClass 1).ker) :
    u.expMap ((∑ j : D.Index, (coeLM ℝ).flip (2 • l j) ∘ₗ G ∘ₗ .proj j :
        RealVectors E D.Index →ₗ[ℝ] Fin (abelianDim E D.Index) → ℂ) (toRealVectors y)) =
      e.torsionPoint (frameTorsionClass 1 y) := by
  -- write `y = ∑ c j • e_j / 2` with `c j` integral
  have h_int : ∀ i : D.Index, ∃ c : 𝓞 E, (c : E) = 2 * y i := by
    simpa [ker_frameTorsionClass_one] using hy
  choose c hc using h_int
  have h_sum : y = ∑ j, c j • Pi.single j 2⁻¹ := by
    simp [funext_iff, Algebra.smul_def, hc, field, Pi.single_apply]
  simp [toRealVectors, hc, ← hG, ← hl, two_mul, congrArg (frameTorsionClass 1) h_sum]

/-- Let `u` uniformise `x.groupScheme` by `V = Fin (abelianDim E D.Index) → ℂ`. A real-linear map
`P` from `(E ⊗ ℝ)ⁿ` to `V` whose image of `Eⁿ` contains the lattice `u.lattice` is bijective: the
lattice spans `V`, and the two real dimensions agree. -/
lemma bijective_of_lattice_subset_range
    (u : Uniformisation x.groupScheme (Fin (abelianDim E D.Index) → ℂ))
    (P : RealVectors E D.Index →ₗ[ℝ] Fin (abelianDim E D.Index) → ℂ)
    (h_lat : ∀ z ∈ u.lattice, ∃ y : D.Index → E, P (toRealVectors y) = z) :
    Function.Bijective P := by
  have hP_onto : P.range = ⊤ := by
    -- the lattice spans `V` over `ℝ`
    refine eq_top_mono (span_le.mpr fun z hz ↦ ?_) (IsZLattice.span_top (K := ℝ) (L := u.lattice))
    obtain ⟨y, hy⟩ := h_lat z hz
    exact ⟨toRealVectors y, hy⟩
  have h_finrank : Module.finrank ℝ (RealVectors E D.Index) ≤
      Module.finrank ℝ (Fin (abelianDim E D.Index) → ℂ) := by
    simp [abelianDim.eq_1 E, mul_assoc, Module.finrank_pi_fintype]
  exact bijective_of_surjective_of_finrank_le P (range_eq_top.mp hP_onto) h_finrank

/-- Let `Q : (E ⊗ ℝ)ⁿ ≃ V` carry the action of `E ⊗ ℝ` on `(E ⊗ ℝ)ⁿ` to an action `G` on `V`, and
let `Q Y` be an eigenvector of `G` with eigenvalue `c v₀` for each `c`. Suppose that `Im Φ(β) ≠ 0`
for `β = D.β`, and that `G (star β) - Φ(β)` (through `x.baseHom`, which is `Φ v₀` on `𝓞 E`) sends
`Q w` to `(η ⬝ᵥ w_{v₀}) • Q Y` for a vector `η`. Then `Q` is a period map (`i` acts as `i ℓ` at
`v₀`, as `i` elsewhere) for the matrix `ℓ = (Y · v₀) η'ᵀ - 1`, where `η' = (I / Im Φ(β)) η`. -/
lemma isPeriodMap_vecMulVec_sub_one_of_sub_smul_eq
    (hρ : ∀ c : 𝓞 E, x.baseHom c = Φ v₀ c.val)
    {V : Type} [FinComplexSpace V] (G : (InfinitePlace E → ℂ) →ₗ[ℝ] V →L[ℂ] V)
    (Q : RealVectors E D.Index ≃L[ℝ] V)
    (hQ : ∀ (c : InfinitePlace E → ℂ) (w : RealVectors E D.Index), Q (c • w) = G c (Q w))
    (Y : RealVectors E D.Index) (hGY : ∀ c : InfinitePlace E → ℂ, G c (Q Y) = c v₀ • Q Y)
    (hβ : (Φ v₀ D.β.val).im ≠ 0) (η : D.Index → ℂ)
    (h_rank : ∀ w : RealVectors E D.Index,
      G (cmEmbedding (star D.β)) (Q w) - x.baseHom D.β • Q w = (η ⬝ᵥ (w · v₀)) • Q Y) :
    IsPeriodMap (vecMulVec (Y · v₀) ((Complex.I / (Φ v₀ D.β.val).im : ℂ) • η) - 1) Q := by
  refine fun w ↦ Q.eq_symm_apply.mp (ext fun j v ↦ ?_)
  -- Read `h_rank w` in coordinates, with `Φ(β) • Q w` split into real and imaginary parts: the
  -- terms with `Re Φ(β)` cancel, and dividing by `Im Φ(β) ≠ 0` solves for `Q⁻¹ (I • Q w)`.
  have h_single (a : ℂ) : a • Q Y = Q ((Pi.single v₀ a : InfinitePlace E → ℂ) • Y) := by
    simp [hQ, hGY]
  have h_coord :
      Q.symm (G (cmEmbedding (star D.β)) (Q w) - x.baseHom D.β • Q w) j v =
        Q.symm ((η ⬝ᵥ (w · v₀)) • Q Y) j v := by rw [h_rank w]
  by_cases hv : v = v₀
  · -- after `simp`, both sides are pairs of real linear equations in `Q⁻¹ (I • Q w) j v₀`
    simp [← hQ, h_single, hv, hρ, vecMulVec_mulVec, Complex.ext_iff,
      smul_eq_re_smul_add_im_smul (Φ v₀ _),
      sub_mulVec, smul_mulVec] at h_coord ⊢
    grind
  · -- away from `v₀` the same equations say `Q⁻¹ (I • Q w) j v = I • w j v`
    simp [D.emb_beta_eq_of_ne, ← hQ, h_single, hv, hρ, Complex.ext_iff,
      smul_eq_re_smul_add_im_smul (Φ v₀ _), sub_eq_zero] at h_coord ⊢
    grind

/-- Let `x` be an object over `ℂ` whose structure map on `𝓞 E` is `Φ v₀` (`hρ`), with full
structure `e`. Then there are an adelic frame `g`, a complex matrix `ℓ` and a dimension `d` such
that `x` has a model `m` on a polarised period map `Y` for `(g, ℓ)` on `ℂ^d`, whose torsion points
are those of `e`, and `ℓ` is a reflection: `ℓ = u wᵀ - 1` for vectors `u`, `w` with `w ⬝ᵥ u = 2`, so
`ℓ` fixes the line of `u` and is `-1` on the kernel of `w`. -/
lemma exists_torusModel
    (hρ : ∀ c : 𝓞 E, x.baseHom c = Φ v₀ c.val) :
    ∃ (g : GL D.Index (𝔸f E)) (ℓ : Matrix D.Index D.Index ℂ) (d : ℕ),
      ∃ᵉ (Y : ThetaTori.PeriodMap D g ℓ (Fin d → ℂ)) (m : x.TorusModel Y),
      m.fullStructure.torsionPoint = e.torsionPoint ∧ IsReflection ℓ := by
  -- Uniformise `x.groupScheme` by `V = Fin (abelianDim E D.Index) → ℂ` and lift the action of `𝓞 E`
  -- to an action `G` of `E ⊗ ℝ` on `V`. The `2`-torsion points given by `e` define a
  -- `G`-equivariant isomorphism `Q : (E ⊗ ℝ)ⁿ → V`. By `X.signature`, the complex structure pulled
  -- back by `Q` is given by a reflection at `v₀`; then `exists_torusModel_of_isPeriodMap` gives the
  -- model.
  obtain ⟨u⟩ := x.isProjEmbedding.nonempty_uniformisation x.smoothOfRelativeDimension
  -- an integral basis of `E` is a real basis of `E ⊗ ℝ`
  obtain ⟨d, hd⟩ :
      ∃ d : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (InfinitePlace E → ℂ),
        ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 E), d i = cmEmbedding (basis E i).val :=
    exists_mixedEquiv.imp' (mixedEmbedding.latticeBasis E).map (by aesop)
  have hβ : (Φ v₀ D.β.val).im ≠ 0 := by simpa [conj_eq_iff_im] using D.emb_star_beta_ne
  -- a Lie chart of `x.groupScheme` in which the signature condition `h_rk` holds
  obtain ⟨U, z_chart, m_chart, h_jac, h_rk⟩ := X.signature 0 x
  obtain ⟨G, hG⟩ := exists_expMap_apply_cmEmbedding_eq_smul u d hd
  -- `P` sends the `j`-th unit vector to twice a lift `l j` of the point `e.torsionPoint (e_j / 2)`
  choose l hl using fun j : D.Index ↦
    u.surjective (e.torsionPoint (frameTorsionClass 1 (Pi.single j 2⁻¹)))
  let P : RealVectors E D.Index →ₗ[ℝ] Fin (abelianDim E D.Index) → ℂ :=
    ∑ j, (coeLM ℝ).flip (2 • l j) ∘ₗ G ∘ₗ .proj j
  -- on vectors of `½ (𝓞 E)ⁿ`, `P` lifts the torsion points of `e`
  have hP := expMap_apply_toRealVectors_eq_torsionPoint_of_two_smul_mem_ker e u G hG l hl
  -- so `P (Eⁿ)` contains the lattice, and `P` is bijective
  have h_lat : ∀ z ∈ u.lattice, ∃ y : D.Index → E, P (toRealVectors y) = z :=
    lattice_subset_range_of_expMap_eq_torsionPoint e u P hP
  let Q : RealVectors E D.Index ≃L[ℝ] Fin (abelianDim E D.Index) → ℂ := (LinearEquiv.ofBijective P
    (bijective_of_lattice_subset_range u P h_lat)).toContinuousLinearEquiv
  have hG_mul : ∀ c c' : InfinitePlace E → ℂ, G (c * c') = G c * G c' := by
    refine G.map_mul_iff.mpr (ext_basis d d fun i j ↦ u.linear_ext ?_)
    simp [← map_mul, mul_smul, hd, hG]
  have hQ (c : InfinitePlace E → ℂ) (w : RealVectors E D.Index) : Q (c • w) = G c (Q w) := by
    simp [Q, P, hG_mul]
  -- the signature condition: `Q Y ≠ 0` is an eigenvector of `G` on `𝓞 E` (`hY_eigen`), and
  -- `G (star β) w - Φ(β) • w = ξ w • Q Y` for a linear form `ξ` on `V` (`hξ`); here `β = D.β`
  obtain ⟨Y, hY, hY_eigen, ξ, hξ⟩ := Q.surjective.exists.mp
    ((u.hasSignature_iff hG h_jac x.isGroupBaseChange (by simp) (ρ := x.baseHom)).mp h_rk)
  have hGY (c : InfinitePlace E → ℂ) : G c (Q Y) = c v₀ • Q Y := by
    rw [← d.sum_repr c]
    simp [sum_smul, mul_smul, hd, hY_eigen, hρ]
  let η (j : D.Index) : ℂ := ξ (Q (Pi.single j 1))
  -- apply `G (w k)` to `hξ` at the `k`-th unit vector and sum over `k`
  have h_rank (w : RealVectors E D.Index) :
      G (cmEmbedding (star D.β)) (Q w) - x.baseHom D.β • Q w = (η ⬝ᵥ (w · v₀)) • Q Y := by
    have h_sum :
        ∑ k, G (w k) (G (cmEmbedding (star D.β)) (Q (Pi.single k 1)) -
            x.baseHom D.β • Q (Pi.single k 1)) =
          ∑ k, G (w k) (ξ (Q (Pi.single k 1)) • Q Y) :=
      Finset.sum_congr rfl fun k _ ↦ congrArg (G (w k)) (by simpa using hξ (Q (Pi.single k 1)))
    simpa [η, hGY, ← hQ, smul_comm (w _), ← map_sum, ← smul_sum, smul_smul (ξ _),
      ← dotProduct.eq_1, ← pi_eq_sum_univ', ← sum_smul] using h_sum
  have h_smul (c : 𝓞 E) (w : RealVectors E D.Index) :
      u.expMap (Q (cmEmbedding c.val • w)) = c • u.expMap (Q w) := by simp [hQ, hG]
  -- `u.expMap ∘ Q` sends `y` to the torsion point of `e` at the class of `m *ᵥ y`
  obtain ⟨m, h_ev⟩ := exists_matrix_torsionPoint_eq_expMap e u Q hP h_smul
  -- the reflection fixes the line of `Y · v₀`; its linear form is a multiple of `η`
  let η' : D.Index → ℂ := (Complex.I / (Φ v₀ D.β.val).im : ℂ) • η
  have h_two : η' ⬝ᵥ (Y · v₀) = 2 := by
    -- `h_rank` at `Y` gives `η ⬝ᵥ (Y · v₀) = conj Φ(β) - Φ(β) = -2 * I * Im Φ(β)`
    have h_Y : Φ v₀ (star D.β.val) - Φ v₀ D.β.val = η ⬝ᵥ (Y · v₀) := by
      simpa [smul_left_inj, hGY, hρ, hY, ← sub_smul] using h_rank Y
    simp [η', ← h_Y, Complex.ext_iff, ← two_mul, field]
  have h_per : IsPeriodMap (vecMulVec (Y · v₀) η' - 1) Q :=
    isPeriodMap_vecMulVec_sub_one_of_sub_smul_eq hρ G Q hQ Y hGY hβ η h_rank
  obtain ⟨g, period, model, h_model⟩ := exists_torusModel_of_isPeriodMap e hρ u Q h_per h_smul h_ev
    h_lat
  exact ⟨g, _, abelianDim E D.Index, period, model, h_model, (Y · v₀), η', h_two, rfl⟩

end New.Variety
