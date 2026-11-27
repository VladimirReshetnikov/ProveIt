import Lib.SiegelWeil.Tower.LineTerms
import Lib.Weil.DualPair.ThetaIntegrals
import Lib.Weil.MixedModel.FockSections
import Lib.Weil.TameGaussSum

/-!
# Real, named and finite slices of data in the mixed model of an adapted splitting

For a splitting `D` of `V` over `V₀` adapted at the point 1 in a basis `t` (`D.IsAdapted 1 t`), the
adelic mixed model separates into a real part and a finite part. Vectors named by a function `Φ` of
their components at finitely many finite places have slices that are scalar multiples of named
vectors when `Φ` factors in an adapted frame. For `Φ` standard in an integral frame, orthogonality
of characters then gives the source term explicitly.

## Main definitions and results

* `New.Space.Splitting.IsAdapted.mixedModel`: the mixed Schrödinger–Fock model v ↦ v[a]
  (`New.Fock.MixedModel`) at the infinite places that D induces.
* `New.Exchange.zeroTerm_integrated`: the zero term of v ⊗ f is v[0] ⊗ (zero term of f°).
* `New.Exchange.slice_integrated`: the slice at `(t⁻¹)ᴴ x` of v ⊗ f is the real slice of v at
  the real part of x tensored with the slice of f° at the finite part.
* `New.Exchange.ReadsAt.lift`: a chosen continuous additive section of the map `π` that reads the
  components at `S`.
* `New.Exchange.slice_localDatum`: if `Φ` factors in an adapted frame, a slice is a scalar times
  a named vector.
* `New.Exchange.adaptedFrame`: a base-adapted splitting gives, through `π`, an integral frame over
  `F` in three blocks.
* `New.Exchange.ReadsAt.homSlice_localDatum`: the source term of `v ⊗ Φ` for `Φ` that is standard
  in that frame at the matrices whose first block is `π` of the finite part of the given point.

Notions from other files:
* `New.Space.Splitting`: A decomposition V = (lE^p ⊕ kE^p) ⊥ ιV₀ over E: isotropic frames l, k with
  l*Jk = 1 for the hermitian form J of V, an isometry ι from V₀ orthogonal to both, and
  rk V = rk V₀ + 2p.
* `New.Space.Splitting.IsAdapted`: `D.IsAdapted g t` says that the matrix g⁻¹(l tᴴ⁻¹, k t, ι) of
  adelic frames has orthonormal columns at the infinite places and integral finite part.
* `New.𝔸`: The product of one copy of ℂ for each infinite place of E with the finite adeles 𝔸_f:
  the adele ring of E when E is totally complex.
* `New.Space.Splitting.slice`: the slice `f ↦ f[x]` at `x ∈ 𝔸^p`, a bounded map from 𝒮(V) to
  𝒮(V₀).
* `New.Exchange.IsBaseAdapted`: The adelic frame (l, k, ι) of the splitting has orthonormal columns
  at every infinite place and integral entries at every finite place.
* `New.Exchange.IntegralFrame`: An integral invertible matrix cut into column blocks (K I L), with
  its integral inverse cut into row blocks K′, I′, L′. `adaptedFrame h D` is the frame (k, ι, l) of
  an adapted splitting read through π.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

noncomputable section

namespace New.Exchange

/-!
## The real mixed model of an adapted splitting

Conventions: `New.Space.integrated V v f` = v ⊗ f is the integral of v(y) ϱ(y) f over the real
vectors y, so it puts the Fock vector v in place of the real vacuum. f° = `New.Space.projReal V f`
is the real vacuum projection.
-/

section AdaptedMixedModel

open Matrix NumberField WeilData Fock Space Splitting Prod Heisenberg IsVacuum

variable {E : Type _} [Field E] [CMType E] [WeilData E] {n n₀ p : Type} [Fintype n] [DecidableEq n]
  [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p] {s : n → ℤˣ} {s₀ : n₀ → ℤˣ}
  {V : Space E n s} {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p} {t : GL p (𝔸 E)}

@[simp]
lemma scaleIdele_fst_apply_ne_zero (v : InfinitePlace E) : (scaleIdele E).val.1 v ≠ 0 :=
  Units.ne_zero _

/-- For a splitting adapted at `1`, the nonzero constant `c` such that the mixed term `D.slice x` at
`x` of the vacuum of `V` is `c * ‖vacuumFn (tᴴ x)‖ ^ 2` times the vacuum of `V₀`
(`slice_vacElem_eq_vacuumFactor_smul`). It is chosen from `IsAdapted.slice_omega_vacElem`. -/
noncomputable def vacuumFactor (h : D.IsAdapted 1 t) : ℂˣ :=
  Units.mk0 h.slice_omega_vacElem.choose h.slice_omega_vacElem.choose_spec.1

/-- The defining property of `vacuumFactor`: if the splitting `D` of `V` over `V₀` is adapted at
`1` in the basis `t`, the mixed term at `x` of the vacuum of `V` is
`vacuumFactor hD * ‖vacuumFn (tᴴ x)‖ ^ 2` times the vacuum of `V₀`, where `vacuumFn` is the standard
vacuum function on adelic vectors. -/
lemma slice_vacElem_eq_vacuumFactor_smul (hD : D.IsAdapted 1 t) (x : p → 𝔸 E) :
    D.slice x V.vacElem =
      ((vacuumFactor hD : ℂ) * (‖vacuumFn (t.valᴴ *ᵥ x)‖ : ℂ) ^ 2) • V₀.vacElem := by
  simpa [vacuumFactor] using hD.slice_omega_vacElem.choose_spec.2 x

/-- If `D` is adapted at `1`, two vectors `v` and `u` of the Fock space of `V₀` are equal as soon
as `V₀.integrated v` and `V₀.integrated u` (the operators `f ↦ v ⊗ f`) agree on all zero terms
`D.zeroTerm (V.projReal f)` of projections on the real vacuum of `V`. -/
lemma eq_of_integrated_zeroTerm_eq (hD : D.IsAdapted 1 t) {v u : fockSpace (realSigns E s₀)}
    (h_eq : ∀ f : 𝒮 V, V₀.integrated v (D.zeroTerm (V.projReal f)) =
      V₀.integrated u (D.zeroTerm (V.projReal f))) :
    v = u := by
  -- At the vacuum, whose zero term is a nonzero multiple of the vacuum of `V₀`, the hypothesis says
  -- that `V₀.integrated (v - u)` kills `V₀.vacElem`; now take inner products.
  have h_zeroTerm : D.zeroTerm V.vacElem = (vacuumFactor hD : ℂ) • V₀.vacElem := by
    simpa [← slice_zero, vacuumFn] using slice_vacElem_eq_vacuumFactor_smul hD 0
  have h_kill : V₀.integrated (v - u) V₀.vacElem = 0 := by
    simpa [h_zeroTerm, sub_eq_zero] using h_eq V.vacElem
  refine sub_eq_zero.1 (eq_zero_of_modelInner_self (?_ : fockInner (v - u) (v - u) = 0))
  simpa [h_kill, -map_sub] using
    (V₀.dataInner_integrated (v - u) (v - u) V₀.vacElem V₀.vacElem).symm

/-- The mixed Schrödinger–Fock model at the infinite places of a splitting `D` adapted at `1` in
the basis `t`. Its three blocks of directions are the real parts of `l tᴴ⁻¹`, `ι` and `k t`. The
slice at `a` is the translation by `l tᴴ⁻¹ a` followed by the map of Fock spaces that the zero term
induces (`New.Space.Splitting.IsAdapted.exists_apply_zero_omega_integrated_eq`). -/
@[local simp]
noncomputable def _root_.New.Space.Splitting.IsAdapted.mixedModel (h : D.IsAdapted 1 t) :
    MixedModel (realSigns E s) (realSigns E s₀) (InfinitePlace E × p) := by
  -- `T` is the map of Fock spaces with `D.zeroTerm (V.integrated v f) = V₀.integrated (T v)
  -- (D.zeroTerm (V.projReal f))` (`hT`). The two laws of `slice` are tested against such vectors by
  -- `eq_of_integrated_zeroTerm_eq`.
  choose T hT using by simpa [↓ Splitting.slice] using h.exists_apply_zero_omega_integrated_eq
                         isMixedLaw_slice
  refine
    { L := realMatrix (D.lAdelic * t⁻¹.1ᴴ)
      K := realMatrix (D.kAdelic * t.1)
      I := realMatrix D.iAdelic
      slice a := T.comp (realHeisenbergOp (realMatrix (D.lAdelic * t⁻¹.1ᴴ) *ᵥ a))
      exists_decomp :=
        ⟨realMatrix (t.1ᴴ * D.lCoord), realMatrix D.iCoord, realMatrix (t⁻¹.1 * D.kCoord),
          fun y ↦ ?_⟩
      slice_realHeisenbergOp a a' w b v := eq_of_integrated_zeroTerm_eq h fun f ↦ ?_
      slice_vac a := eq_of_integrated_zeroTerm_eq h ?_ }
  · -- The real part of the adelic decomposition of the identity, read through the injective
    -- `realVec`.
    apply (injective_iff_map_eq_zero (realVec (E := E))).2 (by simp_all [realVec, funext_iff])
    have h_vec : (D.lAdelic * D.lCoord + D.iAdelic * D.iCoord + D.kAdelic * D.kCoord) *ᵥ realVec y =
        realVec y := by
      rw [add_rotate, add_comm (D.iAdelic * _), D.sum_frame_mul_coord_eq_one, one_mulVec]
    simpa [↓map_add, ↓ realVec_realMatrix_mulVec, ↓ conjTranspose_nonsing_inv, Matrix.mul_assoc,
      add_mulVec] using h_vec
  · -- Write the real bicharacter as the adelic one; then the claim is the adelic law
    -- `isMixedLaw_slice` at real vectors.
    have h_β (x y : InfinitePlace E × p → ℂ) :
        (stdAddChar E (toAdele (j / 2) * Star.star (realVec y) ⬝ᵥ realVec x) : ℂ) =
          (realHeisenberg 1).β x y := by
      simpa [↓ adelicHeisenberg] using! (adelicSum E (n := p) 1).beta_equiv (x, 0) (y, 0)
    rw [two_nsmul a, add_assoc a a a', ← h_β]
    simpa [← hT, ↓ conjTranspose_nonsing_inv, ↓ integrated_realHeisenbergOp,
      ↓ realVec_realMatrix_mulVec, mulVec_add, ↓ Splitting.slice, ↓ adelicHeisenberg,
      ↓ star_mulVec_dotProduct] using
      D.isMixedLaw_slice (t⁻¹.1ᴴ *ᵥ _)
        (D.lAdelic *ᵥ t⁻¹.1ᴴ *ᵥ _ + D.iAdelic *ᵥ _ + D.kAdelic *ᵥ t.1 *ᵥ _) _
  · -- The vacuum becomes the Gaussian.
    simpa [← hT, ↓ integrated_realHeisenbergOp, ↓ realVec_realMatrix_mulVec, ↓ Splitting.slice]
      using h.omega_projReal_of_isMixedLaw isMixedLaw_slice _

/-- If `D` is adapted at `1`, the zero term of `v ⊗ f` (written `V.integrated v f`) is
`v' ⊗ f'`, where `v'` is the slice at `0` of `v` in the real mixed model and `f'` is the zero term
of the projection of `f` on the real vacuum. -/
lemma zeroTerm_integrated (hD : D.IsAdapted 1 t) (v : fockSpace (realSigns E s)) (f : 𝒮 V) :
    D.zeroTerm (V.integrated v f) =
      V₀.integrated (hD.mixedModel.slice 0 v) (D.zeroTerm (V.projReal f)) := by
  -- at the point `0` the slice is the map chosen in `mixedModel`
  simpa [↓ slice] using (hD.exists_apply_zero_omega_integrated_eq isMixedLaw_slice).choose_spec v f

/-- If `D` is adapted at `1` in the basis `t`, the mixed term at `(t⁻¹)ᴴ x` of `v ⊗ f` (written
`V.integrated v f`) is `v' ⊗ f'`, where `v'` is the slice of `v` in the real mixed model at the
real coordinates of `x` and `f'` is the mixed term at `(t⁻¹)ᴴ` times the finite part of `x` of the
projection of `f` on the real vacuum. -/
lemma slice_integrated (hD : D.IsAdapted 1 t) (x : p → 𝔸 E) (v : fockSpace (realSigns E s))
    (f : 𝒮 V) :
    D.slice (t⁻¹.valᴴ *ᵥ x) (V.integrated v f) =
      V₀.integrated (hD.mixedModel.slice (realCoord x) v)
        (D.slice (t⁻¹.valᴴ *ᵥ fun i : p ↦ (0, (x i).2)) (V.projReal f)) := by
  -- Split `x` into its real part, whose Heisenberg operator is absorbed into `v`, and its finite
  -- part, whose operator commutes with `integrated` and `projReal`; then apply
  -- `zeroTerm_integrated`.
  set xfin : p → 𝔸 E := fun i ↦ (0, (x i).2)
  set y : n → 𝔸 E := D.lAdelic *ᵥ t⁻¹.valᴴ *ᵥ xfin
  set a : InfinitePlace E × n → ℂ := realMatrix (D.lAdelic * t⁻¹.valᴴ) *ᵥ realCoord x
  have hy_real : ∀ i : n, (y i).1 = 0 := by simp [y, xfin, mulVec_eq_sum, ↓ fst_sum]
  have h_split : V.ϱ (D.lAdelic *ᵥ t⁻¹.valᴴ *ᵥ x) (V.integrated v f) =
      V.integrated (realHeisenbergOp a v) (V.ϱ y f) := by
    rw [integrated_realHeisenbergOp, ← V.rho_integrated v f hy_real]
    simp [a, y, xfin, ↓ realVec_realMatrix_mulVec, ← mulVec_add, realVec_realCoord_add, Rep.mul,
      ↓ star_mulVec_dotProduct, Matrix.mul_assoc, adelicHeisenberg]
  have h_proj : V.projReal (V.ϱ y f) = V.ϱ y (V.projReal f) :=
    (V.rho_integrated IsVacuum.vacElem f hy_real).symm
  calc D.slice (t⁻¹.valᴴ *ᵥ x) (V.integrated v f)
      = D.zeroTerm (V.integrated (realHeisenbergOp a v) (V.ϱ y f)) := by
        rw [slice, ContinuousLinearMap.comp_apply, h_split]
    _ = V₀.integrated (hD.mixedModel.slice 0 (realHeisenbergOp a v))
          (D.zeroTerm (V.ϱ y (V.projReal f))) := by rw [zeroTerm_integrated hD, h_proj]
    _ = V₀.integrated (hD.mixedModel.slice (realCoord x) v)
          (D.slice (t⁻¹.valᴴ *ᵥ xfin) (V.projReal f)) := by simp [a, y, slice]

end AdaptedMixedModel

/-!
## The real part of the terms along a line in each space

`New.Exchange.lineTermReal` is the map of Fock spaces that the operator `New.Exchange.lineTerm`
induces at the infinite places: a slice of the real mixed model
`New.Space.Splitting.IsAdapted.mixedModel` of the splitting `New.Exchange.lineTermSplitting`, taken
at a point supported on the last coordinate.
-/

section TwoLineRealPart

open NumberField

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r r' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} {W : Space E n s} {W' : Space E n' s'}
  {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)
  [IsBaseAdapted A] [IsBaseAdapted X]

/-- For a source space with finite basis `n` and a character of weight `μ`, the weight
`⌊#n / 2⌋ - μ w` in which the real points of the target group act at the infinite place `w`. -/
abbrev targetWeight (n : Type) [Fintype n] (μ : InfinitePlace E → ℤ) (w : InfinitePlace E) : ℤ :=
  (Fintype.card n / 2 : ℕ) + (-μ) w

/-- For base-adapted splittings `A` of `W'` over `W` and `X` of `V'` over `V` along lines, the real
part of the operator `lineTerm A X β a` (`β` selects one of its two models): the slice, in the real
mixed model of the splitting `lineTermSplitting A X β` of `Hom(W', V')` over `Hom(W, V)`, at the
point with coordinates `a` on the last coordinate (the line) and `0` elsewhere. -/
@[irreducible]
noncomputable def lineTermReal (β : Bool) (a : InfinitePlace E → ℂ) :
    Fock.fockSpace (realSigns E (homSigns s' t')) →L[ℂ]
      Fock.fockSpace (realSigns E (homSigns s t)) :=
  (isAdapted_lineTermSplitting A X β).mixedModel.slice fun p ↦ a p.1 * p.2.isRight.toNat

end TwoLineRealPart

end New.Exchange

/-!
## The real slice of a datum in the mixed model

For an adapted splitting `D` of `X` into a hyperbolic part and `W₁` (`New.Space.Splitting`,
`New.Exchange.IsBaseAdapted`), a vector of the Fock space `New.PairFock` of the pair `(X, V)` is
read in the mixed model as a function of a matrix `x` with values in the Fock space of `(W₁, V)`.
-/

/-- The slice of a real datum for (X, V) at the real part of the adelic matrix x: its value in the
mixed model attached to the splitting of Hom(X, V) induced by the base-adapted splitting D of X
over W₁, a real datum for (W₁, V). -/
noncomputable def New.Exchange.realSlice {E : Type} [Field E] [CMType E] [WeilData E]
    {n a b m : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [Fintype m] [DecidableEq m] {s : n → ℤˣ} {t : a → ℤˣ} {r : m → ℤˣ}
    {X : Space E m r} {W₁ : Space E n s} (D : X.Splitting W₁ b) (V : Space E a t) [IsBaseAdapted D]
    (x : Matrix a b (𝔸 E)) : PairFock E r t →L[ℂ] PairFock E s t :=
  (isAdapted_homSource D V).mixedModel.slice fun p ↦ (matrixToVec x p.2).1 p.1

namespace New.Exchange

/-!
## Slices of named data in the mixed model

A vector of the global model is named by a function `Φ` of the components at a set `S` of finite
places (`New.Exchange.namedVector`). The components are read by a ring map `π : 𝔸f E →+* F`
(`New.Exchange.ReadsAt`) into a product of local fields `F` with integers `O`
(`New.SemilocalField`).
-/

section NamedSlices

open Matrix MeasureTheory SemilocalField Space Splitting WeilData stdLattice

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r r' : Type} {p : Type _} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r']
  [DecidableEq r'] [Fintype p] [DecidableEq p] {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ}
  {t' : r' → ℤˣ} {W : Space E n s} {W' : Space E n' s'} {T : Space E r t} {T' : Space E r' t'}
  {F : Type} [V : SemilocalField F] {S : Set (FinPlace E)} {π : 𝔸f E →+* F}

/-- A chosen continuous additive section of `π` that takes `π x` to `idem S * x`, where `idem S` is
the idempotent of `𝔸f E` that is 1 at the places of `S` and 0 elsewhere
(`ReadsAt.continuous_lift_and_apply_lift`). -/
def ReadsAt.lift (h : ReadsAt S π) : F →+ 𝔸f E := h.exists_section.2.choose

omit [WeilData E] in
lemma ReadsAt.continuous_lift_and_apply_lift (h : ReadsAt S π) :
    Continuous h.lift ∧ (∀ y : F, π (h.lift y) = y) ∧ ∀ x : 𝔸f E, h.lift (π x) = idem S * x :=
  h.exists_section.2.choose_spec

omit [WeilData E] in
lemma ReadsAt.continuous_lift (h : ReadsAt S π) : Continuous h.lift :=
  h.continuous_lift_and_apply_lift.1

omit [WeilData E] in
lemma ReadsAt.apply_lift (h : ReadsAt S π) (y : F) : π (h.lift y) = y := by
  obtain ⟨-, h_section, -⟩ := h.continuous_lift_and_apply_lift
  exact h_section y

omit [WeilData E] in
lemma ReadsAt.lift_apply (h : ReadsAt S π) (x : 𝔸f E) : h.lift (π x) = idem S * x := by
  obtain ⟨-, -, h_idem⟩ := h.continuous_lift_and_apply_lift
  exact h_idem x

/-- The additive character `y ↦ selfDualAddChar E (σ y)` of `F` (`selfDualAddChar E` is the
character of `𝔸f E` for which `Ô E` is self-dual), where `σ = h.lift` is a chosen section of `π`
with `σ (π x) = idem S * x`. -/
def ReadsAt.ψ (h : ReadsAt S π) : AddChar F ℂ := (selfDualAddChar E).compAddMonoidHom h.lift

lemma ReadsAt.psi_apply (h : ReadsAt S π) (z : 𝔸f E) : h.ψ (π z) = selfDualAddChar E (idem S * z) :=
  congrArg (selfDualAddChar E) (h.lift_apply z)

/-- If `π` reads the components at `S`, the induced character `h.ψ` of `F` has conductor the ring
of integers `O`: it is continuous, and `h.ψ (t * ·)` is trivial on `O` exactly for `t ∈ O`. -/
lemma ReadsAt.hasIntegralConductor_psi (h : ReadsAt S π) : HasIntegralConductor h.ψ := by
  refine ⟨continuous_selfDualAddChar.comp h.continuous_lift, fun t ↦ ?_⟩
  -- Write `t = π x`; the claim becomes the self-duality of `Ô E` for `idem S * x`.
  have π_surj : Function.Surjective π := fun y ↦ ⟨h.lift y, h.apply_lift y⟩
  obtain ⟨x, rfl⟩ := π_surj t
  rw [h.mem_iff, ← forall_selfDualAddChar_mul_eq_one_iff]
  constructor
  · intro h_triv u hu
    have hu_mem : π u ∈ O := (h.mem_iff u).2 (mul_mem (idem_mem_Ô S) hu)
    calc selfDualAddChar E (idem S * x * u) = h.ψ (π x * π u) := by
          rw [← map_mul, h.psi_apply, mul_assoc]
      _ = 1 := h_triv (π u) hu_mem
  · intro h_triv s hs
    obtain ⟨u, rfl⟩ := π_surj s
    calc h.ψ (π x * π u) = selfDualAddChar E (idem S * x * (idem S * u)) := by
          rw [← map_mul, h.psi_apply, mul_mul_mul_comm, idem_mul_self]
      _ = 1 := h_triv (idem S * u) ((h.mem_iff u).1 hs)

omit [WeilData E] [DecidableEq p] in
/-- If `π : 𝔸f E →+* F` reads the components at `S`, then applying it coordinatewise carries the
Haar measure of finite adelic vectors (mass one on the integral vectors), restricted to the
vectors integral at the places outside `S`, to the volume on `p → F`. -/
lemma ReadsAt.measurePreserving_comp (h : ReadsAt S π) :
    MeasurePreserving (fun b : p → 𝔸f E ↦ π ∘ b)
      ((latticeMeasure E p).restrict (integralBox p Sᶜ)) volume := by
  have π_cont : Continuous π := h.exists_section.1
  have h_meas : Measurable fun b : p → 𝔸f E ↦ π ∘ b := by fun_prop
  refine ⟨h_meas, ?_⟩
  -- Translations by the lifts `h.lift ∘ z` preserve the box, so the image measure is proportional
  -- to the volume; the preimage of `O ^ p` in the box is the lattice, and both have mass one.
  have h_lift :
      HasAddStableLifts (π.toAddMonoidHom.compLeft p) (integralBox p Sᶜ : Set (p → 𝔸f E)) :=
    fun z ↦ ⟨h.lift ∘ z, by
      simp [mem_integralBox, idem_compl, sub_mul, ← h.lift_apply, h.apply_lift, funext_iff]⟩
  have h_pre : (fun b : p → 𝔸f E ↦ π ∘ b) ⁻¹' Set.univ.pi (fun _ ↦ (O : Subring F)) ∩
      (integralBox p Sᶜ : Set (p → 𝔸f E)) = stdLattice E p := by
    simp [← integralBox_compl_inter (S := S), Set.ext_iff, h.mem_iff, mem_integralBox, and_comm]
  have h_proportional :
      (volume : Measure (p → F)) (Set.univ.pi fun _ ↦ (O : Subring F)) •
          ((latticeMeasure E p).restrict (integralBox p Sᶜ)).map (fun b : p → 𝔸f E ↦ π ∘ b) =
        latticeMeasure E p (stdLattice E p) • (volume : Measure (p → F)).neg := by
    rw [← h_pre]
    exact measure_smul_map_restrict_eq_smul_neg (latticeMeasure E p) volume h_meas
      isOpen_integralBox.measurableSet h_lift (.univ_pi fun _ ↦ isCompact_O.measurableSet)
  simpa [volume_O, volume_pi, latticeMeasure_stdLattice] using h_proportional

open scoped Classical in
/-- Suppose that at the points with coordinates `(π x, z, y)` in the frame `D.frameAt 1 u` a
continuous function `Φ` is the product of the `f i (z i)`, cut off to `O`, times `Ψ y`. Then the
partial Fourier integral `sliceDatum` of `Φ` at the finite part of `x` is the product of the Fourier
integrals of the `f i` over `O` times `Ψ`. -/
lemma ReadsAt.sliceDatum_eq_prod_setIntegral_smul (h : ReadsAt S π)
    {D : (W'.hom T').Splitting (W.hom T) p} {u : GL p (𝔸 E)} {Φ : Matrix r' n' F → ℂ}
    (hΦ_cont : Continuous Φ) (x : p → 𝔸 E) {Ψ : Matrix r n F → ℂ} (f : p → F → ℂ)
    (h_prod : ∀ (y : Matrix r n F) (z : p → F),
      Φ (vecToMatrix ((D.frameAt 1 u).map (fun a : 𝔸 E ↦ π a.2) *ᵥ
          ((fun a : 𝔸 E ↦ π a.2) ∘ x ⊕ᵥ z ⊕ᵥ matrixToVec y))) =
        (∏ i : p, if z i ∈ O then f i (z i) else 0) * Ψ y) :
    D.sliceDatum S 1 u (fun y : r' × n' → 𝔸f E ↦ Φ ((vecToMatrix y).map π))
        (fun i : p ↦ (x i).2) =
      (∏ i : p, ∫ t : F in V.O, h.ψ (π (Star.star (x i).2) * t) * f i t) •
        fun y : r × n → 𝔸f E ↦ Ψ ((vecToMatrix y).map π) := by
  ext y
  let c : p → F := fun i ↦ π (Star.star (x i).2)
  let g : (p → F) → ℂ := fun z ↦ (∏ i, h.ψ (c i * z i)) *
    Φ (vecToMatrix ((D.frameAt 1 u).map (fun a : 𝔸 E ↦ π a.2) *ᵥ
      ((fun a : 𝔸 E ↦ π a.2) ∘ x ⊕ᵥ z ⊕ᵥ matrixToVec ((vecToMatrix y).map π))))
  have hg : Continuous g := by
    have hψ_cont : Continuous h.ψ := h.hasIntegralConductor_psi.1
    simp only [g, vecToMatrix, mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    fun_prop
  have hψ_sum (z : p → F) : h.ψ (∑ i, z i) = ∏ i, h.ψ (z i) :=
    map_prod h.ψ.toMonoidHom (fun i ↦ Multiplicative.ofAdd (z i)) Finset.univ
  have h_factor (z : p → F) : g z = (∏ i, Set.indicator (V.O : Set F)
      (fun t ↦ h.ψ (c i * t) * f i t) (z i)) * Ψ ((vecToMatrix y).map π) := by
    simp [g, h_prod, Set.indicator_apply, ← mul_assoc, ← Finset.prod_mul_distrib]
  -- the integrand of `sliceDatum` is `g ∘ π`; by `h_prod`, `g` factors over the coordinates
  calc D.sliceDatum S 1 u (fun y ↦ Φ ((vecToMatrix y).map π)) (fun i ↦ (x i).2) y
      = ∫ b : p → 𝔸f E in (integralBox p Sᶜ : Set (p → 𝔸f E)),
          g (π ∘ b) ∂latticeMeasure E p := by
        simp [g, c, sliceDatum, finFrameVector, ← h.psi_apply, ↓dotProduct_smul, vecToMatrix,
          Matrix.map, dotProduct, mulVec, hψ_sum, matrixToVec]
    _ = ∫ z, g z := h.measurePreserving_comp.hasLaw.integral_comp hg.aestronglyMeasurable
    _ = (∏ i, ∫ t : F in V.O, h.ψ (c i * t) * f i t) * Ψ ((vecToMatrix y).map π) := by
      simp only [h_factor, integral_mul_const, integral_fintype_prod_volume_eq_prod,
        integral_indicator isCompact_O.measurableSet]

open scoped Classical in
/-- The slice `D.slice` at `u⁻¹ᴴ (scaleIdele E • x)` of a datum `v ⊗ Φ` (`localDatum`: real
part `v`, named by the Schwartz–Bruhat function `Φ` of the components read through `π`;
`scaleIdele E` is the fixed scaling idele). Here `D` is adapted in the basis `u`, with adelic frame
`D.frameAt 1 u`. Suppose that at the points with coordinates `(π x, z, y)` in this frame the
function `Φ` is the product of the `f i (z i)`, cut off to `O`, times `Ψ y`. Then the slice is the
datum of `Ψ` and of the real slice of `v`, times the constant `vacuumFactor` (replaced by zero
unless the finite part of `x` is integral off `S.conjClosure`) and the Fourier integrals of the
`f i` over `O`. -/
lemma slice_localDatum (h : ReadsAt S π) {D : (W'.hom T').Splitting (W.hom T) p}
    {u : GL p (𝔸 E)} (hu : D.IsAdapted 1 u) {Φ : Matrix r' n' F → ℂ}
    {U : Set (Matrix r' n' F)} (hΦ : Φ ∈ schwartzBruhat U) (x : p → 𝔸 E) (v : PairFock E s' t')
    {Ψ : Matrix r n F → ℂ} (f : p → F → ℂ)
    (h_prod : ∀ (y : Matrix r n F) (z : p → F),
      Φ (vecToMatrix ((D.frameAt 1 u).map (fun a : 𝔸 E ↦ π a.2) *ᵥ
          ((fun a : 𝔸 E ↦ π a.2) ∘ x ⊕ᵥ z ⊕ᵥ matrixToVec y))) =
        (∏ i : p, if z i ∈ O then f i (z i) else 0) * Ψ y) :
    D.slice (u⁻¹.valᴴ *ᵥ scaleIdele E • x) (localDatum W' T' v Φ h) =
      ((if ∀ i : p, idem S.conjClosureᶜ * (x i).2 ∈ Ô E then (vacuumFactor hu : ℂ) else 0) *
          ∏ i : p, ∫ t : F in V.O, h.ψ (π (star (x i).2) * t) * f i t) •
        localDatum W T
          (hu.mixedModel.slice (fun q : NumberField.InfinitePlace E × p ↦ (x q.2).1 q.1) v)
          Ψ h := by
  -- `slice_integrated` splits off the real part. For the finite part,
  -- `omega_schrodingerOp_of_isMixedLaw` says that the slice of a named vector is the slice of the
  -- vacuum off `S.conjClosure` (the first factor), named by the partial Fourier integral
  -- `sliceDatum` at the places of `S` (the second factor and `Ψ`).
  let xf : p → 𝔸f E := fun i ↦ (x i).2
  have h_real : realCoord (scaleIdele E • x) = fun q ↦ (x q.2).1 q.1 := by
    simp [funext_iff, realCoord, Units.smul_def]
  have h_fin : (fun i ↦ (0, ((scaleIdele E • x) i).2)) = finVec xf := rfl
  have h_vac :
      D.slice (u.1⁻¹ᴴ *ᵥ finVec (idem S.conjClosureᶜ • xf))
          (ω (W'.hom T') 1 (W'.hom T').vacElem) =
        (if ∀ i, idem S.conjClosureᶜ * (x i).2 ∈ Ô E then (vacuumFactor hu : ℂ) else 0) •
          (W.hom T).vacElem := by
    have h_norm : ‖vacuumFn (u.1ᴴ *ᵥ u.1⁻¹ᴴ *ᵥ finVec (idem S.conjClosureᶜ • xf))‖ =
        if ∀ i, idem S.conjClosureᶜ * (x i).2 ∈ Ô E then 1 else 0 := by
      simp [vacuumFn, finVec, ← conjTranspose_mul, xf, apply_ite norm, Circle.norm_coe]
    rw [map_one, one_apply_eq_self, slice_vacElem_eq_vacuumFactor_smul hu, h_norm]
    split_ifs <;> simp
  have h_ev : D.sliceDatum S 1 u (fun y ↦ Φ ((vecToMatrix y).map π)) xf =
      (∏ i, ∫ t in V.O, h.ψ (π (star (x i).2) * t) * f i t) • fun y ↦ Ψ ((vecToMatrix y).map π) :=
    h.sliceDatum_eq_prod_setIntegral_smul hΦ.1.continuous x f h_prod
  have h_name :
      D.slice (u.1⁻¹ᴴ *ᵥ finVec xf) (ω (W'.hom T') 1
          ((W'.hom T').schrodingerOp S (fun y ↦ Φ ((vecToMatrix y).map π)) (W'.hom T').vacElem)) =
        (∏ i, ∫ t : F in V.O, h.ψ (π (star (x i).2) * t) * f i t) •
          (if ∀ i, idem S.conjClosureᶜ * (x i).2 ∈ Ô E then (vacuumFactor hu : ℂ) else 0) •
            (W.hom T).schrodingerOp S (fun y ↦ Ψ ((vecToMatrix y).map π)) (W.hom T).vacElem := by
    rw [hu.omega_schrodingerOp_of_isMixedLaw isMixedLaw_slice xf (W'.hom T').vacElem h.disjoint_star
      (h.isSchwartzBruhat hΦ), projOn_vacElem, h_vac, h_ev, ← smul_schrodingerOp, map_smul]
  simp only [map_one, one_apply_eq_self, ← coe_units_inv] at h_name
  rw [slice_integrated hu, projReal_eq_self_of_mem_finitePart (schrodingerOp_mem_finitePart ..),
    h_real,
    h_fin,
    mul_comm, mul_smul, ← map_smul, ← map_smul, h_name]

/-- For a base-adapted splitting `A`, the images under `π` of the finite parts of the adelic frame
`(k, ι, l)` and of its dual frame, as mutually inverse integral matrices over `F`. -/
def adaptedFrame (h : ReadsAt S π) (A : W'.Splitting W p) [k : IsBaseAdapted A] :
    IntegralFrame F n' n p where
  K := A.kAdelic.map (π.comp (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)))
  L := A.lAdelic.map (π.comp (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)))
  I := A.iAdelic.map (π.comp (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)))
  dualK := A.kCoord.map (π.comp (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)))
  dualL := A.lCoord.map (π.comp (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)))
  dualI := A.iCoord.map (π.comp (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)))
  isIntMatrix_and_mul_eq_one := by
                          -- The matrices are square by `A.card_eq`, so one of the two products
                          -- suffices. Three claims remain: the frame and its dual are integral, and
                          -- their product is one.
                          simp +arith [↓mul_eq_one_comm_of_card_eq _ n', A.card_eq, ← add_assoc,
                            fromCols_mul_fromRows]
                          obtain ⟨-, h_int⟩ := k.isOrthoIntegral
                          refine ⟨?_, ?_, ?_⟩
                          · -- the frame is integral
                            simp_all [IsIntMatrix, h.mem_iff, mul_mem]
                          · -- so is the dual frame, which is made of conjugate transposes of the
                            -- frame
                            simp_all [IsIntMatrix, h.mem_iff, mul_mem, kCoord, iCoord, lCoord,
                              star_mem_Ô, stdForm]
                          · -- apply `π` to the finite part of the decomposition of the identity
                            simpa [map_add, -RingHom.coe_comp] using! congrArg
                              (π.comp (RingHom.snd (NumberField.InfinitePlace E → ℂ)
                                (𝔸f E))).mapMatrix
                              A.sum_frame_mul_coord_eq_one

end NamedSlices

/-!
## Slices of data standard in an integral frame

`New.Exchange.ReadsAt.homSlice_localDatum` computes the term `New.Space.Splitting.homSlice` of a
datum `v ⊗ Φ` (`New.Exchange.localDatum`) for a base-adapted splitting `D`
(`New.Exchange.IsBaseAdapted`), when the function `Φ` of the components at `S` agrees with a
standard datum (`New.Exchange.IntegralFrame.stdDatum`) of the integral frame of `D` on the matrices
with the given first block.
-/

section FiniteSlices

open Matrix MeasureTheory SemilocalField Fintype WeilData IntegralFrame

variable {E : Type} [Field E] [CMType E] [WeilData E] {n : Type} {a : Type _} {b m : Type}
  [Fintype n] [DecidableEq n] [Fintype b] [DecidableEq b] [Fintype m]
  [DecidableEq m] {s : n → ℤˣ} {t : a → ℤˣ} {r : m → ℤˣ} {X : Space E m r} {W₁ : Space E n s}
  {F : Type} [SemilocalField F] {S : Set (FinPlace E)} {π : 𝔸f E →+* F}

/-- A matrix has entries in `O` exactly when its three blocks of coordinates in an integral frame
do. -/
lemma IntegralFrame.isIntMatrix_iff_blocks (A : IntegralFrame F m n b) (z : Matrix a m F) :
    IsIntMatrix O z ↔
      IsIntMatrix O (z * A.K) ∧ IsIntMatrix O (z * A.I) ∧ IsIntMatrix O (z * A.L) := by
  have h_blocks : A.BlockRelations := A.blockRelations
  refine ⟨fun hz ↦ ⟨hz.mul h_blocks.isIntMatrix_K, hz.mul h_blocks.isIntMatrix_I,
    hz.mul h_blocks.isIntMatrix_L⟩, fun ⟨hK, hI, hL⟩ ↦ ?_⟩
  obtain ⟨-, -, h_inverse, -⟩ := A.isIntMatrix_and_mul_eq_one
  have h_one : A.K * A.dualK + (A.I * A.dualI + A.L * A.dualL) = 1 := by
    rwa [fromCols_mul_fromRows, fromCols_mul_fromRows] at h_inverse
  rw [show z = z * A.K * A.dualK + (z * A.I * A.dualI + z * A.L * A.dualL) by
    simp only [Matrix.mul_assoc, ← Matrix.mul_add, h_one, Matrix.mul_one]]
  exact (hK.mul h_blocks.isIntMatrix_dualK).add
    ((hI.mul h_blocks.isIntMatrix_dualI).add (hL.mul h_blocks.isIntMatrix_dualL))

/-- The matrix with blocks of coordinates `k`, `w`, `l` in the frame `A` has first block `k`. -/
lemma IntegralFrame.blocks_mul_K (A : IntegralFrame F m n b) (k l : Matrix a b F)
    (w : Matrix a n F) : (k * A.dualK + l * A.dualL + w * A.dualI) * A.K = k := by
  simp [Matrix.add_mul, Matrix.mul_assoc, A.blockRelations.dualK_mul_K,
    A.blockRelations.dualL_mul_K,
    A.blockRelations.dualI_mul_K]

open scoped Classical in
/-- At the matrix with blocks of coordinates `k`, `w`, `l` in the frame `A`, the function
`A.stdDatum G` is `G (k, w)` if the three blocks are integral and `0` otherwise. -/
lemma IntegralFrame.stdDatum_blocks (A : IntegralFrame F m n b) (G : Matrix a (b ⊕ n) F → ℂ)
    (k l : Matrix a b F) (w : Matrix a n F) :
    A.stdDatum G (k * A.dualK + l * A.dualL + w * A.dualI) =
      if IsIntMatrix O k ∧ IsIntMatrix O w ∧ IsIntMatrix O l then G (fromCols k w) else 0 := by
  have h_blocks : A.BlockRelations := A.blockRelations
  have hI : (k * A.dualK + l * A.dualL + w * A.dualI) * A.I = w := by
    simp [Matrix.add_mul, Matrix.mul_assoc, h_blocks.dualK_mul_I, h_blocks.dualL_mul_I,
      h_blocks.dualI_mul_I]
  have hL : (k * A.dualK + l * A.dualL + w * A.dualI) * A.L = l := by
    simp [Matrix.add_mul, Matrix.mul_assoc, h_blocks.dualK_mul_L, h_blocks.dualL_mul_L,
      h_blocks.dualI_mul_L]
  simp only [stdDatum, A.isIntMatrix_iff_blocks (k * A.dualK + l * A.dualL + w * A.dualI),
    mul_fromCols,
    A.blocks_mul_K k l w, hI, hL]

open scoped Classical in
/-- Orthogonality of characters: the integral of `t ↦ h.ψ (c * t)` over `O` is `1` if `c` lies in
`O` and `0` otherwise, since `h.ψ` has conductor `O` and `O` has volume one. -/
lemma ReadsAt.setIntegral_psi_mul (h : ReadsAt S π) (c : F) :
    ∫ t : F in (O : Subring F), h.ψ (c * t) = if c ∈ O then 1 else 0 := by
  obtain ⟨-, h_conductor⟩ := h.hasIntegralConductor_psi
  simpa [volume_O, Measure.real, h_conductor] using
    setIntegral_char (ν := volume) (M := O.toAddSubgroup) isOpen_O (χ := fun t ↦ h.ψ (c * t))
      fun s t ↦ by rw [mul_add, h.ψ.map_add_eq_mul]

omit [WeilData E] in
/-- A finite adele `c` is integral exactly when it is integral off `S` and its conjugate, on the
conjugate of `S` (read by `π (star c)`), and on `S` (read by `π c`). -/
lemma ReadsAt.mem_Ô_iff (h : ReadsAt S π) (c : 𝔸f E) :
    c ∈ Ô E ↔ idem S.conjClosureᶜ * c ∈ Ô E ∧ π (Star.star c) ∈ O ∧ π c ∈ O := by
  have h_star : π (Star.star c) ∈ O ↔ idem (Star.star ⁻¹' S) * c ∈ Ô E := h.star.mem_iff c
  rw [h_star, h.mem_iff, idem_mul_mem_Ô, idem_mul_mem_Ô, idem_mul_mem_Ô, mem_Ô]
  refine ⟨fun hc ↦ ⟨fun w _ ↦ hc w, fun w _ ↦ hc w, fun w _ ↦ hc w⟩, ?_⟩
  rintro ⟨h_off, h_conj, h_on⟩ w
  by_cases hw : w ∈ S.conjClosure
  · exact hw.elim (h_on w) (h_conj w)
  · exact h_off w hw

open scoped Classical in
/-- Let `Φ` be a Schwartz–Bruhat function, and write `y` for the finite part of `x`. Suppose that
on the matrices `w` whose first block in the frame of `D` is `π y`, the function `Φ` is `G` of the
first two blocks if `w` is integral and `0` otherwise (`stdDatum`). Then `D.homSlice` (translate
by the map that is the given point on the `k`-frame, then take the zero term) of `v ⊗ Φ`
(`localDatum`) at `scaleIdele E • x` is zero unless `y` is integral; then it is `vacuumFactor`
times the real slice of `v` at `x` tensored with the function `z ↦ G (π y, z)` on integral `z`. -/
lemma ReadsAt.homSlice_localDatum [Fintype a] [DecidableEq a]
    (D : X.Splitting W₁ b) (V : Space E a t) (h : ReadsAt S π)
    [IsBaseAdapted D] {G : Matrix a (b ⊕ n) F → ℂ} {Φ : Matrix a m F → ℂ} {U : Set (Matrix a m F)}
    (hΦ : Φ ∈ schwartzBruhat U) (x : Matrix a b (𝔸 E)) (v : PairFock E r t)
    (h_std : ∀ w : Matrix a m F,
      w * (adaptedFrame h D).K =
          (x.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))).map π →
        Φ w = (adaptedFrame h D).stdDatum G w) :
    D.homSlice V (scaleIdele E • x) (localDatum X V v Φ h) =
      (if IsIntMatrix (Ô E) (x.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))) then
          (vacuumFactor (isAdapted_homSource D V) : ℂ) else 0) •
        localDatum W₁ V (realSlice D V x v)
          (fun z : Matrix a n F ↦ if IsIntMatrix O z then
            G (fromCols ((x.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))).map π) z)
          else 0) h := by
  -- Along the frame of `D`, with first block `π y`, the function `Φ` factors as indicators of `O`
  -- times `Ψ`. Then `slice_localDatum` applies, and orthogonality of characters evaluates the
  -- Fourier integrals.
  set y : Matrix a b (𝔸f E) := x.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))
  set A : IntegralFrame F m n b := adaptedFrame h D
  let f : a × b → F → ℂ := fun i _ ↦ if π (matrixToVec y i) ∈ O then 1 else 0
  let Ψ : Matrix a n F → ℂ := fun z ↦ if IsIntMatrix O z then G (fromCols (y.map π) z) else 0
  -- the point at which `slice_localDatum` reads `Φ`, in the dual basis of the frame
  have h_point (w : Matrix a n F) (z : a × b → F) :
      vecToMatrix
          (((D.homSource V).frameAt 1 (adaptedHomBasis b V)).map (fun c : 𝔸 E ↦ π c.2) *ᵥ
            ((fun c : 𝔸 E ↦ π c.2) ∘ matrixToVec x ⊕ᵥ z ⊕ᵥ matrixToVec w)) =
        y.map π * A.dualK + vecToMatrix z * A.dualL + w * A.dualI := by
    ext i j
    -- both sides are sums over the same blocks, up to the order of the terms
    simp [frameAt_homSource, stdForm, dotProduct, mulVec, vecToMatrix, sum_prod_type, diagonal,
      apply_ite, Matrix.one_apply]
    ac_rfl
  -- that point has blocks `π y`, `w`, `vecToMatrix z`, so `h_std` and `stdDatum_blocks` evaluate
  -- `Φ`
  have h_factor (w : Matrix a n F) (z : a × b → F) :
      Φ (y.map π * A.dualK + vecToMatrix z * A.dualL + w * A.dualI) =
        (∏ i : a × b, if z i ∈ O then f i (z i) else 0) * Ψ w := by
    have h_prod : (∏ i : a × b, if z i ∈ O then f i (z i) else 0) =
        if IsIntMatrix O (y.map π) ∧ IsIntMatrix O (vecToMatrix z) then 1 else 0 := by
      simp only [f, ← ite_and, Fintype.prod_boole]
      simp [IsIntMatrix, forall_and, matrixToVec, vecToMatrix, and_comm]
    rw [h_std _ (A.blocks_mul_K (y.map π) (vecToMatrix z) w), A.stdDatum_blocks, h_prod]
    simp [Ψ, ← ite_and, and_assoc, and_comm]
  -- integrality off `S` and its conjugate, on the conjugate and on `S` is integrality everywhere
  have h_scalar (c : ℂ) :
      (if ∀ i : a × b, idem S.conjClosureᶜ * (matrixToVec x i).2 ∈ Ô E then c else 0) *
          ∏ i : a × b,
            ∫ t : F in (O : Subring F), h.ψ (π (Star.star (matrixToVec x i).2) * t) * f i t =
        if IsIntMatrix (Ô E) y then c else 0 := by
    have h_coord (i : a × b) : (matrixToVec x i).2 = matrixToVec y i := rfl
    have h_int : IsIntMatrix (Ô E) y ↔
        (∀ i : a × b, idem S.conjClosureᶜ * matrixToVec y i ∈ Ô E) ∧
          ∀ i : a × b, π (Star.star (matrixToVec y i)) ∈ O ∧ π (matrixToVec y i) ∈ O := by
      simp [IsIntMatrix, h.mem_Ô_iff (y _ _), forall_and, matrixToVec]
    have h_integral (i : a × b) :
        ∫ t : F in (O : Subring F), h.ψ (π (Star.star (matrixToVec y i)) * t) * f i t =
          if π (Star.star (matrixToVec y i)) ∈ O ∧ π (matrixToVec y i) ∈ O then 1 else 0 := by
      rw [integral_mul_const, h.setIntegral_psi_mul, ite_zero_mul_ite_zero, mul_one]
    simp only [h_coord, h_integral, h_int, Fintype.prod_boole, ite_zero_mul_ite_zero, mul_one]
  have h_scale : matrixToVec (scaleIdele E • x) = scaleIdele E • matrixToVec x := rfl
  have h_real : (isAdapted_homSource D V).mixedModel.slice
      (fun q : NumberField.InfinitePlace E × (a × b) ↦ (matrixToVec x q.2).1 q.1) v =
      realSlice D V x v := rfl
  rw [homSlice_eq_adapted_slice, h_scale, slice_localDatum h (isAdapted_homSource D V) hΦ
    (matrixToVec x) v f fun w z ↦ (congrArg Φ (h_point w z)).trans (h_factor w z), h_scalar, h_real]

end FiniteSlices

end New.Exchange

end
