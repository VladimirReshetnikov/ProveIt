import Lib.GaloisRep.Pseudocharacter.SemisimpleRepresentations
import Lib.General.NumberTheory.PadicLimitsValuation
import Lib.PadicHodge.Kisin.PeriodMatrixFrame
import Lib.PadicHodge.RadiusLemma

/-!
# Uniform period bounds and limits of crystalline lattices with bounded jumps

Let `A = New.Period.Amax` and `B = New.Period.Bmax`, with tensor products over `ℤ_p`. A continuous,
trace-nondegenerate `p`-adic limit of continuous crystalline representations with jumps in `[0, h]`
is crystalline. The limit is formulated through representations of the group ring `ℤ_p[G]`,
restricted along a multiplicative map from a local Galois group.

## Main definitions and results

* `New.Period.IsCrystallineUpTo`: crystalline with all Hodge–Tate jumps (`New.Period.jump`) in [0,
  h].
* `New.Period.PadicRep`: a matrix representation of Γ over Q̄_p, bundled with its index set.
* `New.Lift.uniform_period_bound`: one element `a` of the period ring `A = New.Period.Amax` bounds
  the denominators of the periods of all crystalline `ℤ_p`-lattices with Hodge–Tate jumps in
  `[0, h]` (`New.Period.IsCrystallineUpTo`). The element `a` is chosen for the given `Γ`, with its
  `OverGp Γ p` instance (the map `toGp` to `G_p`), and for the given `h`.
* `New.Period.exists_finite_groupRing_quotient`: the image of `ℤ_p[G]` in finitely many continuous
  representations is a finite free `ℤ_p`-algebra with the properties
  `New.Period.IsFiniteGroupRingQuotient`.
* `New.Period.isCrystalline_of_trace_limit`: the limit theorem.

Notions from other files:
* `New.Period.IsCrystalline`: T is crystalline: the elements of B⊗T fixed by all of Γ span B⊗T over
  B.
* `New.Period.Amax`: Colmez's period ring A_max, the p-adic completion of A_inf[X]/(pX − ξ).
* `New.Period.Bmax`: The period ring B = B^+[1/μ] (Colmez's B_max, used in place of Fontaine's
  B_cris), over which crystalline representations are defined; B^+ = A[1/p] is `New.Period.BPlus`.
* `New.IsTraceNondeg`: for a representation r, any x in the span of r(G) with tr(x r(g)) = 0 for all
  g is zero.
* `OverGp Γ p`: a group Γ with a homomorphism `toGp` to G_p = Gal(Q̄_p/Q_p) whose image is open.
* `New.Period.fixedPeriods ρ B F`: the elements of B ⊗ T fixed by `toGp g ⊗ ρ g` for F-almost all g.
* `New.Lift.Chart` c with `c.IsChartOf j`: a chart W(F_q)⟦X⟧ → A_inf with coefficients `WittFq c.f`,
  sending X to z; `IsChartOf j` says that every g in G_p that fixes `WittFq c.f` pointwise and fixes
  θ(z) lies in j(Γ).
* `New.Lift.AdicBasis I A`: for an ideal I of a ring Λ and a Λ-module A, a topological basis of A
  for the I-adic topology, with coordinate forms.

## Relation to the literature

Known; see `Lib.PadicHodge.Limit.TraceLimit` and `Lib.PadicHodge.RadiusLemma` for sources.
-/

/-! ## Crystalline modules with Hodge–Tate jumps in [0, h] -/

namespace New.Period

open TensorProduct Module

variable {p : ℕ} [ThePrime p]
  {Γ T R : Type} [Group Γ] [OverGp Γ p] [AddCommGroup T] [Module ℤ_[p] T] [CommRing R] [Module R T]
  [Algebra ℤ_[p] R] [IsScalarTower ℤ_[p] R T]

/-- For `T` flat over `ℤ_p`, the map `A ⊗ T → B ⊗ T` (`periodTensorMap`) induced by the inclusion
of `A = Amax` in `B = Bmax` and the identity of `T` is injective. -/
lemma periodTensorMap_injective [Flat ℤ_[p] T] :
    Function.Injective (periodTensorMap Amax Bmax (LinearMap.id : T →ₗ[ℤ_[p]] T)) :=
  Flat.rTensor_preserves_injective_linearMap (Algebra.algHom ℤ_[p] Amax Bmax).toLinearMap
    (injective_BPlus_Bmax.comp injective_Amax_BPlus)

/-- The representation is crystalline and all its Hodge–Tate jumps, at every γ: R → C_p, lie in
[0, h]. -/
def IsCrystallineUpTo (h : ℕ) (ρ : Representation R Γ T) : Prop :=
  IsCrystalline ρ ∧ ∀ (γ : R →ₐ[ℤ_[p]] ℂ_[p]) (k : ℤ), jump ρ γ k ≠ 0 → 0 ≤ k ∧ k ≤ h

/-- A finite index type m with a group homomorphism Γ → GL_m(ℚ̄_p): a matrix representation of
unspecified dimension. -/
structure PadicRep (Γ : Type*) [Group Γ] (p : ℕ) [ThePrime p] where
  /-- The index set of the rows and columns. -/
  {Index : Type}
  /-- The index set is finite. -/
  [fintypeIndex : Fintype Index]
  [decEqIndex : DecidableEq Index]
  /-- The homomorphism from `Γ` to invertible matrices over the algebraic closure of `ℚ_p`. -/
  rep : Γ →* GL Index (PadicAlgCl p)

attribute [instance] PadicRep.fintypeIndex PadicRep.decEqIndex

/-- For a Z_p-linear map u from T to square matrices over Q̄_p and a vector v, the Z_p-linear
map sending x to u(x)v. -/
noncomputable abbrev applyVec {m : Type*} [Fintype m] (u : T →ₗ[ℤ_[p]] Matrix m m (PadicAlgCl p))
    (v : m → PadicAlgCl p) : T →ₗ[ℤ_[p]] m → PadicAlgCl p :=
  (Matrix.mulVecBilin ℤ_[p] ℤ_[p]).flip v ∘ₗ u

end New.Period

/-! ## The uniform period bound -/

section UniformBound

open New.Period TensorProduct Matrix Module Submodule MulSemiringAction Function algebraMap

/-- **Uniform period bound.** For `Γ` over `G_p` with open image (instance `OverGp Γ p`) and `h : ℕ`
there is `a` in `A = Amax`, a unit in `B = Bmax`, such that for every crystalline `ρ` on `T` with
basis `e` and jumps in `[0, h]`: (a) each `a ⊗ t` lies in the `A`-span of the invariants of `A ⊗ T`;
(b) some `U`, `U'` over `A` have `U U' = a · 1` and `ρ(g) · g(U) = U`, with `ρ(g)` the matrix of
`ρ g` in `e`: the columns of `U` are invariant vectors.
Known result: Dwork's trick (an integral crystalline comparison with a uniform denominator). -/
lemma New.Lift.uniform_period_bound {p : ℕ} [ThePrime p] (Γ : Type) [Group Γ] [OverGp Γ p] (h : ℕ) :
    ∃ a : Amax, IsUnit (a : Bmax) ∧
      ∀ {T ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Fintype ι] [DecidableEq ι]
        (e : Basis ι ℤ_[p] T) {ρ : Representation ℤ_[p] Γ T}, IsCrystallineUpTo h ρ →
        -- (a)
        (∀ t : T, a ⊗ₜ t ∈ span Amax (fixedPeriods ρ Amax ⊤)) ∧
        -- (b)
        ∃ U U' : Matrix ι ι Amax,
          U * U' = a • 1 ∧
          ∀ g : Γ,
            ((ρ g).toMatrix e e).map ((↑) : ℤ_[p] → Amax) * U.map (fun x : Amax ↦ toGp g • x) =
              U := by
  -- A period matrix `U` of `ρ` has entries in `BPlus = Amax [1/p]`. After a Frobenius power `m`
  -- that depends on `Γ` only, a change of basis fixed by `toGp Γ` brings it into `Amax`. The Kummer
  -- chart `k` of the fixed field of `toGp Γ` has a coordinate `z` and an Eisenstein element `E` of
  -- degree `k.e`; `toGp Γ` fixes its constants `Λ` and `θ z` (`h_fix`).
  obtain ⟨k, h_fix, -⟩ := exists_kummerChart Γ
  -- `m` is `φ ^ l` with `3 k.e ≤ p ^ l` (as the radius lemma asks), `α : Ainf → Amax` is `m`
  -- followed by the structure map, and `a = α (E τ) ^ h`, a unit of `Bmax` as `E τ ∣ μ`.
  let m : FrobGal := (.ofAdd (p.clog (3 * k.e)), 1)
  let α : Ainf →+* Amax := (algebraMap Ainf Amax).comp (toRingHom FrobGal Ainf m)
  have h_unit : IsUnit ((α (k.E * tau) ^ h : Amax) : Bmax) := by
    simpa [α, ← IsScalarTower.algebraMap_apply] using
      (isUnit_smul_of_dvd_mu m k.associated_E_mul_tau_mu.dvd).pow h
  refine ⟨α (k.E * tau) ^ h, h_unit, ?_⟩
  intro T ι _ _ _ _ e ρ hρ
  -- It suffices to prove (b), from which (a) follows.
  refine (and_iff_right_of_imp fun h_matrix t ↦ ?_).mpr ?_
  · -- Claim (a) follows from (b): if `u` is the linear map with matrix `U`, then
    -- `a ⊗ t = U U' (1 ⊗ t)` is a combination of the columns `u (b n)` of `U`, which are invariant.
    let b : Basis ι Amax (Amax ⊗[ℤ_[p]] T) := e.baseChange Amax
    obtain ⟨u, U', h_mul, h_inv⟩ := (toLinAlgEquiv b).symm.surjective.exists.mp h_matrix
    -- apply both sides of `h_mul`, as maps, to `1 ⊗ t`
    have h_comb : (α (k.E * tau) ^ h) ⊗ₜ t = ∑ n, (U' *ᵥ b.repr (1 ⊗ₜ t)) n • u (b n) := by
      simpa [toLinAlgEquiv_apply, smul_tmul'] using
        (congrArg (toLinAlgEquiv b · (1 ⊗ₜ t)) h_mul).symm
    refine Set.mem_of_eq_of_mem h_comb (sum_smul_mem _ _ fun n _ ↦ subset_span fun g ↦ ?_)
    have h_coord : b.equivFun (u (b n)) = ((toLinAlgEquiv b).symm u).col n :=
      funext fun _ ↦ by simp [LinearMap.toMatrixAlgEquiv_apply]
    refine b.equivFun.injective ((equivFun_tensorAction ..).trans ?_)
    rw [h_coord]
    exact congrArg (fun X : Matrix ι ι Amax ↦ X.col n) (h_inv g)
  -- Take a period matrix `U` over `BPlus`, equal over `Bmax` to a matrix `M` with invariant
  -- columns, and its frame: `Q L = τ ^ h` over `Ainf`, `U Z = E ^ h Q`, `Z' Z = E ^ h`, and
  -- `g Z = Z G` with `G` over `Ainf` for `g` fixing `Λ` and `θ z` (`Z_gal`).
  obtain ⟨hρ_crys, hρ_jumps⟩ := hρ
  obtain ⟨M, U, v, M_inv, -, hU, hUM⟩ :=
    k.chart_isChartOf.exists_isPeriodMatrixOf 0 h hρ_crys e (hρ_jumps _)
  rw [zero_add, pow_zero] at hU
  rw [pow_zero, one_smul] at hUM
  obtain ⟨Q, L, Z, Z', -, hQL, hZ, hUZ, hZ', -, Z_gal⟩ := hU.exists_frame
  -- The radius lemma, for `t` with `t z = [ε] z`, gives `m Z = C V` with `V` invertible over
  -- `Amax` and `C` fixed by whatever fixes `Λ`, so by `toGp Γ`.
  obtain ⟨t, ht⟩ := k.exists_smul_z 1
  obtain ⟨G, hG⟩ := Z_gal _ (h_fix t.val)
  obtain ⟨V, C, hC, hV, -⟩ :=
    k.radius_lemma (h_fix t.val) (by simpa using ht) hZ hZ' hG (p.le_pow_clog Fact.out _) 0
  -- on matrices: `act x` is the action of `x`, and `incl` the inclusion of `Amax` in `BPlus`
  let act (x : FrobGal) : Matrix ι ι BPlus →+* Matrix ι ι BPlus :=
    (toRingHom FrobGal BPlus x).mapMatrix
  let incl : Matrix ι ι Amax →+* Matrix ι ι BPlus := (algebraMap Amax BPlus).mapMatrix
  have h_act_Z : act m Z = C * incl V.val := by
    simpa [← ext_iff, act, m, incl, FrobGal.smul_def] using hV
  -- The new matrix is `α (E ^ h Q) V⁻¹`, over `Amax`; over `BPlus` it equals `(m U) C`.
  have h_new_matrix : incl ((k.E.1 ^ h • Q).map α * V.val⁻¹) = act m U * C := by
    -- multiplied by `incl V`, both sides become `m (U Z) = m (E ^ h Q)`
    have h_mul_V : incl ((k.E.1 ^ h • Q).map α) = act m U * C * incl V.val := by
      rw [mul_assoc, ← h_act_Z, ← map_mul]
      simp [← ext_iff, hUZ, incl, act, α, Algebra.smul_def (A := BPlus),
        ← IsScalarTower.algebraMap_apply]
    rw [map_mul, ← coe_units_inv, h_mul_V, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  refine ⟨(k.E.1 ^ h • Q).map α * V.val⁻¹, V * L.map α, ?_, fun g ↦ ?_⟩
  · -- `α (E ^ h Q) V⁻¹ · V α L = α (E ^ h τ ^ h)`, as `Q L = τ ^ h`
    simpa [mul_assoc, Matrix.map_smul', mul_pow, mul_smul] using
      congrArg (fun X : Matrix ι ι Ainf ↦ α (k.E.1 ^ h) • X.map α) hQL
  · -- Invariance can be checked over `BPlus`: `U` is invariant, `m` commutes with `toGp g`, and
    -- `toGp g` fixes `C`.
    -- `using!`: the coercions from `ℤ_p` and `Amax` to `Bmax` agree with the composite maps only
    -- after unfolding
    have U_inv : (repMatrix ρ e g).map (↑) * act (1, toGp g) U = U :=
      map_injective injective_BPlus_Bmax (by simpa [← hUM, comp_def] using! M_inv g)
    have incl_gal (X : Matrix ι ι Amax) :
        incl (X.map fun x ↦ toGp g • x) = act (1, toGp g) (incl X) :=
      ext fun _ _ ↦ (smul_algebraMap_eq_algebraMap_smul (A := Amax) (toGp g) _).symm
    have C_fix : act (1, toGp g) C = C := hC _ (h_fix g).left
    apply map_injective injective_Amax_BPlus
    change incl _ = incl _
    -- `using!`: the matrix of `ρ g` with entries cast to `Amax` and then to `BPlus` matches the one
    -- in `U_inv` only after unfolding the casts
    simpa [map_mul, incl_gal, ↓h_new_matrix, mul_assoc, C_fix, act, m, comp_def, smul_smul] using!
      congrArg (act m · * C) U_inv

end UniformBound

/-!
## Limits of crystalline representations in group-ring form

A continuous, trace-nondegenerate `p`-adic limit of continuous crystalline representations with
jumps in `[0, h]` is crystalline.

Representations of a compact group `G` are extended to the group ring (`New.Period.groupRingHom`)
and restricted along a multiplicative map `w : Δ →* ℤ_p[G]` from a local Galois group
(`New.Period.viaGroupRing`).
-/

section CrystallineLimit

namespace New.Period

open TensorProduct Matrix MonoidAlgebra Submodule Finset LinearMap Algebra Module Lift nsmulRange
  NeZero ContinuousMap Set Metric IsLocalRing PadicInt WittVector

variable {p : ℕ} [ThePrime p]
  {G Δ κ I : Type} [Group G] [Group Δ] [OverGp Δ p] [TopologicalSpace G] [CompactSpace G]
  {ι : I → Type} [∀ η, Finite (ι η)]
  (w : Δ →* ℤ_[p][G]) (σ : PadicRep G p) {R : PadicRep G p}

/-- For a matrix representation σ: G→GL_m(Q̄_p), the Z_p-algebra homomorphism from the group
ring Z_p[G] to m×m matrices over Q̄_p extending σ. -/
noncomputable abbrev groupRingHom : ℤ_[p][G] →ₐ[ℤ_[p]] Matrix σ.Index σ.Index (PadicAlgCl p) :=
  MonoidAlgebra.lift ℤ_[p] (Matrix σ.Index σ.Index (PadicAlgCl p)) G
    ((Units.coeHom (Matrix σ.Index σ.Index (PadicAlgCl p))).comp σ.rep)

/-- For a multiplicative map w: Δ→Z_p[G] and a matrix representation σ of G over Q̄_p, the matrix
representation of Δ sending g to σ(w(g)), σ extended linearly. -/
noncomputable abbrev viaGroupRing : Representation (PadicAlgCl p) Δ (σ.Index → PadicAlgCl p) :=
  matrixRep ((groupRingHom σ).toMonoidHom.comp w).toHomUnits

variable (Δ) in
/-- `q : ℤ_p[G] → T` and the maps `u s` from `T` to matrices over `Q̄_p` indexed by `(τ s).Index`
present `T` as a finite free quotient of the group ring `ℤ_p[G]` through which the representations
`τ s` factor; along any multiplicative map `w : Δ → ℤ_p[G]`, `T` is crystalline with jumps in
`[0, h]` if all `τ s`, read along `w`, are. -/
structure IsFiniteGroupRingQuotient (τ : κ → PadicRep G p) (T : AlgCat ℤ_[p])
    (q : ℤ_[p][G] →ₐ[ℤ_[p]] T)
    (u : ∀ s : κ, T →ₐ[ℤ_[p]] Matrix (τ s).Index (τ s).Index (PadicAlgCl p)) : Prop where
  /-- `T` is free as a `ℤ_p`-module. -/
  free : Free ℤ_[p] T
  /-- `T` is finitely generated as a `ℤ_p`-module. -/
  finite : Module.Finite ℤ_[p] T
  /-- `T` is a quotient of the group ring. -/
  surjective : (⇑q).Surjective
  /-- The extension of `τ s` to the group ring (`groupRingHom`) is `u s ∘ q`. -/
  factors : ∀ (s : κ) (y : ℤ_[p][G]), u s (q y) = groupRingHom (τ s) y
  /-- The kernel of `q` is the common kernel of these extensions. -/
  apply_eq_zero_iff : ∀ y : ℤ_[p][G], q y = 0 ↔ ∀ s : κ, groupRingHom (τ s) y = 0
  /-- If every `τ s`, read along `w`, is crystalline with jumps in `[0, h]`, so is `Δ` acting on `T`
  by left multiplication with `q (w g)`. -/
  isCrystallineUpTo : ∀ {h : ℕ} {w : Δ →* ℤ_[p][G]},
    (∀ s : κ, IsCrystallineUpTo h (viaGroupRing w (τ s))) →
      IsCrystallineUpTo h (actionRep ℤ_[p] T (q.toMonoidHom.comp w))

variable (Δ) in
/-- For finitely many continuous representations `τ s` of the compact group `G` over `Q̄_p`, there
exist a `ℤ_p`-algebra `T`, a map `q : ℤ_p[G] → T` and maps `u s` from `T` to matrices over `Q̄_p`
indexed by `(τ s).Index`. These present `T` as a finite free quotient of the group ring `ℤ_p[G]`
through which every `τ s` factors (`IsFiniteGroupRingQuotient`). Moreover, for the group `Δ` with
its map to `Gal(Q̄_p/Q_p)` and any multiplicative map `w : Δ → ℤ_p[G]`, `T` is crystalline with
jumps in `[0, h]` whenever all `τ s`, read along `w`, are. -/
lemma exists_finite_groupRing_quotient [IsTopologicalGroup G] [Finite κ] {τ : κ → PadicRep G p}
    (hτ : ∀ s : κ, Continuous (τ s).rep) :
    ∃ (T : AlgCat ℤ_[p]) (q : ℤ_[p][G] →ₐ[ℤ_[p]] T)
        (u : ∀ s : κ, T →ₐ[ℤ_[p]] Matrix (τ s).Index (τ s).Index (PadicAlgCl p)),
      IsFiniteGroupRingQuotient Δ τ T q u := by
  -- `T` is the image of `ℤ_[p][G]` in the product of the matrix algebras.
  let Φ : ℤ_[p][G] →ₐ[ℤ_[p]] ∀ s, Matrix (τ s).Index (τ s).Index (PadicAlgCl p) :=
    AlgHom.pi fun s ↦ groupRingHom (τ s)
  -- Each `τ s` is conjugate by `P s` to a representation `ν s` over the integers `O s` of a finite
  -- extension of `ℚ_[p]`. So the image lies in the product of the finite modules
  -- `P s * M(O s) * (P s)⁻¹`.
  choose O ν P hP using fun s ↦ (eventually_exists_isLatticeIn (hτ s)).exists
  have h_finite : Module.Finite ℤ_[p] Φ.range := by
    let L (s : κ) : Matrix (τ s).Index (τ s).Index (O s) →ₗ[ℤ_[p]]
        Matrix (τ s).Index (τ s).Index (PadicAlgCl p) :=
      mulLeftRight ℤ_[p] ((P s).val, (P s).inv) ∘ₗ (O s).1.val.toLinearMap.mapMatrix
    refine Finite.of_fg ((fg_pi fun s ↦ fg_range (L s)).of_le (S := Φ.range.toSubmodule) ?_)
    rintro _ ⟨y, rfl⟩ s -
    refine ⟨y.lift _ _ _ (ν s), ?_⟩
    have h_conj (g : G) :
        (ν s g).map Subtype.val = (P s).val⁻¹ * (τ s).rep g * (P s).val := by
      simpa using (hP s g).symm
    simp [L, Φ, lift_apply, Finsupp.sum, h_conj, mul_assoc]
  -- It is torsion free, being inside matrices over `Q̄_p`, hence free. `h_torsionFree`, a statement
  -- about all modules over `Q̄_p`, serves as the instance.
  have h_torsionFree := IsTorsionFree.trans_faithfulSMul ℤ_[p] (PadicAlgCl p)
  let u (s : κ) : Φ.range →ₐ[ℤ_[p]] Matrix (τ s).Index (τ s).Index (PadicAlgCl p) :=
    (Pi.evalAlgHom _ _ s).comp Φ.range.val
  refine ⟨.of _ Φ.range, Φ.rangeRestrict, u,
    { free := inferInstance
      finite := h_finite
      surjective := Φ.rangeRestrict_surjective
      factors := fun s y ↦ by simp [u, Φ] -- the maps `u s` recover the `τ s`
      apply_eq_zero_iff := fun y ↦ by simp [Φ, Subtype.ext_iff, funext_iff]
      isCrystallineUpTo := fun {h w} h_crys ↦ ?_ }⟩
  -- The columns of the `u s` are jointly injective equivariant maps from `T` to the `τ s`.
  let f (s : Σ s, (τ s).Index) : Φ.range →ₗ[ℤ_[p]] (τ s.fst).Index → PadicAlgCl p :=
    applyVec (u s.fst).toLinearMap (Pi.single s.snd 1)
  have h_inj (t : Φ.range) (ht : ∀ s : Σ s, (τ s).Index, f s t = 0) : t = 0 := by
    ext s i l
    -- the entry `(i, l)` of `u s t` is the `i`-th coordinate of `f ⟨s, l⟩ t`, which is zero
    simpa [f, u] using congrFun (ht ⟨s, l⟩) i
  have h_equiv (s : Σ s, (τ s).Index) (g : Δ) (t : Φ.range) :
      f s (actionRep ℤ_[p] Φ.range (Φ.rangeRestrict.toMonoidHom.comp w) g t) =
        viaGroupRing w (τ s.fst) g (f s t) := by
    simp [f, u, Φ, -mulVec_single]
  refine ⟨.of_jointly_injective le_top (fun s ↦ (h_crys _).left) f
    (fun s ↦ .of_forall (h_equiv s)) h_inj, fun γ k h_jump ↦ ?_⟩
  -- Every jump of `T` is a jump of some `τ s` (`γ` is the only `ℤ_[p]`-algebra map to `ℂ_[p]`).
  obtain rfl : γ = ofId _ _ := ext_id _ _ _
  obtain ⟨s, hs⟩ :=
    exists_jump_of_linearIndependent (fun s ↦ (h_crys _).left.isPotentiallyCrystalline) _
      (asSemilinear f) (fun s ↦ .of_forall (h_equiv s.fst))
      (linearIndependent_algHom_coord f (finBasis ℤ_[p] Φ.range) h_inj) h_jump
  exact (h_crys s.fst.fst).right _ _ hs

/-- Let `R` be a continuous matrix representation of the compact group `G` whose trace form is
non-degenerate. Let `T` be a finite free `ℤ_p`-algebra, a quotient `q` of `ℤ_p[G]` whose kernel
contains that of `groupRingHom R`, and let `u` map `T` to matrices with `u ∘ q = groupRingHom R`.
Traces define the `p`-adic topology on `T`: for every `k` there is `ε > 0` such that `t ∈ p ^ k T`
as soon as the traces of all `u t * R g` have norm at most `ε`. -/
lemma exists_pos_mem_pow_of_norm_trace_le (hR : Continuous R.rep) (hR_nondeg : IsTraceNondeg R.rep)
    {T : Type*} [Ring T] [Algebra ℤ_[p] T] [Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    {q : ℤ_[p][G] →ₐ[ℤ_[p]] T} {u : T →ₐ[ℤ_[p]] Matrix R.Index R.Index (PadicAlgCl p)}
    (hq : (⇑q).Surjective) (hu : ∀ y : ℤ_[p][G], u (q y) = groupRingHom R y)
    (hq_ker : ∀ y : ℤ_[p][G], groupRingHom R y = 0 → q y = 0) (k : ℕ) :
    ∃ ε > (0 : ℝ), ∀ t : T, (∀ g : G, ‖(u t * R.rep g).trace‖ ≤ ε) → t ∈ nsmulRange (p ^ k) T := by
  -- In coordinates `F`, `t ↦ (g ↦ trace (u t * R g))` is a continuous map `Φ` from a compact space
  -- to `C(G, Q̄_p)`, hence closed, and only `0` is sent to `0`.
  let F : T ≃ₗ[ℤ_[p]] Fin (finrank ℤ_[p] T) → ℤ_[p] := (finBasis ℤ_[p] T).equivFun
  have h_cont : Continuous fun x : (Fin (finrank ℤ_[p] T) → ℤ_[p]) × G ↦
      (u (F.symm x.fst) * R.rep x.snd).trace :=
    ((u.toLinearMap ∘ₗ F.symm.toLinearMap).continuous_on_pi.fst'.mul
      (Units.continuous_val.comp hR).snd').matrix_trace
  let Φ : C(Fin (finrank ℤ_[p] T) → ℤ_[p], C(G, PadicAlgCl p)) := curry ⟨_, h_cont⟩
  have hΦ (t : T) (g : G) : Φ (F t) g = (u t * R.rep g).trace :=
    congrArg (fun s ↦ (u s * R.rep g).trace) (F.symm_apply_apply t)
  have hfibre (t : T) (ht : Φ (F t) = 0) : t = 0 := by
    obtain ⟨z, rfl⟩ := hq t
    have h_trace_zero (g : G) : (groupRingHom R z * R.rep g).trace = 0 := by
      simp [← hu, ← hΦ, ht]
    refine hq_ker _ (hR_nondeg _ (span_subset_span ℤ_[p] _ _ ?_) h_trace_zero)
    simp [Finsupp.mem_span_range_iff_exists_finsupp, lift_apply]
  -- So the open set of points whose coordinates all lie in `p ^ k ℤ_p` is a neighbourhood of the
  -- fibre, and it contains the preimage of a ball.
  have hnear : ∀ᶠ φ : C(G, PadicAlgCl p) in nhds 0,
      ∀ x ∈ Φ ⁻¹' {φ}, ∀ i ∈ Set.univ, x i ∈ maximalIdeal ℤ_[p] ^ k := by
    refine Φ.continuous.isClosedMap.eventually_nhds_fiber 0 (F.surjective.forall.mpr fun t ht ↦ ?_)
    refine (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_maximalIdeal_pow _ k).mem_nhds ?_
    simp [hfibre t ht]
  obtain ⟨ε, hε, hball⟩ := nhds_basis_closedBall.mem_iff.mp hnear
  refine ⟨ε, hε, fun t ht ↦ ?_⟩
  have h_ball : Φ (F t) ∈ closedBall 0 ε := by simpa [hΦ, norm_le_of_nonempty] using ht
  have hcoord (i : Fin (finrank ℤ_[p] T)) : F t i ∈ Ideal.span {(p : ℤ_[p])} ^ k := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact hball h_ball (F t) rfl i (Set.mem_univ i)
  rw [← (finBasis ℤ_[p] T).sum_equivFun t]
  exact mem_span_pow_smul_top_iff.mp (sum_mem fun i _ ↦ smul_mem_smul (hcoord i) Submodule.mem_top)

/-- Let `c` be a chart (a Λ-algebra map Λ[[X]] → `A_inf`, Λ = `WittFq c.f`, sending X to z = [ϖ^♭])
for `Δ`: every g in Gal(Q̄_p/Q_p) fixing Λ pointwise and fixing θ(z) lies in the image of `Δ`. Let
`A = Amax` and `W = WittFq c.f`, with an algebra map `W → A` that agrees with `W → Ainf` after both
are mapped to `Bmax` (`halg`), and let `T` be flat over `ℤ_p` with a representation `ρ` of `Δ`.
Finitely many elements of `A ⊗ T` fixed by `Δ` that are linearly independent over `W` stay so over
`A`. -/
lemma linearIndependent_of_mem_fixedPeriods {c : Chart} (hc : c.IsChartOf (Γ := Δ) OverGp.toGp)
    [Algebra (WittFq c.f) Amax]
    (halg : ∀ a : WittFq c.f, algebraMap Amax Bmax (algebraMap (WittFq c.f) Amax a) =
      algebraMap Ainf Bmax (algebraMap (WittFq c.f) Ainf a))
    {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Flat ℤ_[p] T] {ρ : Representation ℤ_[p] Δ T}
    {n : Type} [Fintype n] {y : n → Amax ⊗[ℤ_[p]] T} (hy : ∀ i : n, y i ∈ fixedPeriods ρ Amax ⊤)
    (hy_indep : LinearIndependent (WittFq c.f) y) :
    LinearIndependent Amax y := by
  -- It suffices to show independence over `B = Bmax` of the images in `B ⊗ T`.
  suffices hB : LinearIndependent Bmax (periodTensorMap Amax Bmax LinearMap.id ∘ y) by
    -- `Amax → Bmax` is injective, so independence over `Bmax` restricts to `Amax`.
    have h_inj_smul : Function.Injective fun r : Amax ↦ r • (1 : Bmax) := by
      simpa [Algebra.smul_def] using! injective_BPlus_Bmax.comp injective_Amax_BPlus
    exact .of_comp (periodTensorMap Amax Bmax .id) (hB.restrict_scalars h_inj_smul)
  -- The identity of `T` commutes with `ρ`, so the images of the `y i` stay fixed.
  have hfix (i : n) : (periodTensorMap Amax Bmax LinearMap.id ∘ y) i ∈ fixedPeriods ρ Bmax ⊤ :=
    fixedPeriods.periodTensorMap_mem (by simp) (hy i)
  let φ : (n →₀ Bmax) →ₗ[Bmax] Bmax ⊗[ℤ_[p]] T :=
    Finsupp.linearCombination Bmax (periodTensorMap Amax Bmax .id ∘ y)
  -- The relations are saturated: if a nonzero multiple of a vector is a relation, so is the vector.
  have h_sat : ∀ b ≠ (0 : Bmax), ∀ v : n →₀ Bmax, b • v ∈ ker φ → v ∈ ker φ := by
    simp +contextual
  -- The relations over `B` form a saturated stable submodule, so invariant relations span it:
  -- it is enough that these vanish.
  refine ker_eq_bot.mp (bot_unique
    (le_of_fixed_mem_of_saturated (Γ := Δ) le_top h_sat (fun a ha g ↦ ?_) fun a ha hinv ↦ ?_))
  · -- The relations are stable under `Δ`, as the `y i` are fixed.
    show toGp g • a ∈ ker φ
    rw [mem_ker, ← eventually_tensorAction_eq hfix a g, mem_ker.mp ha, map_zero]
  -- The coefficients of an invariant relation lie in `W[1/p]`.
  have hcoef (t : n) : ∃ (m : ℕ) (b : WittFq c.f),
      p ^ m * a t = algebraMap Amax Bmax (algebraMap (WittFq c.f) Amax b) := by
    have h_fixed_t (g : Δ) : (1 : Bmax) * toGp g • a t = toGp g • (1 : Bmax) * a t := by
      simpa using DFunLike.congr_fun (hinv g) t
    simpa [halg] using exists_pow_mul_eq_wittFq_mul_of_isChartOf hc one_ne_zero h_fixed_t
  choose m b hb using hcoef
  -- Clearing denominators gives a relation over `W`, which is trivial.
  have hrel : ∑ t : n, (p ^ (univ.sup m - m t) • b t) • y t = 0 := by
    -- the image of this sum in `B ⊗ T` is `p ^ M • φ a = 0`, with `M` the largest exponent
    have h_image : periodTensorMap Amax Bmax .id
        (∑ t : n, (p ^ (univ.sup m - m t) • b t) • y t) = p ^ univ.sup m • φ a := by
      simp [φ, ← algebraMap_smul (R := Amax) Bmax, ← hb, le_sup, smul_sum,
        ← algebraMap_smul (R := WittFq c.f) Amax, ← smul_assoc, ← pow_add, Finsupp.sum_fintype,
        ← mul_assoc, Finsupp.linearCombination]
    exact periodTensorMap_injective (by rw [h_image, mem_ker.mp ha, smul_zero, map_zero])
  have hb₀ (t : n) : b t = 0 := by
    simpa [WittVector.p_nonzero] using Fintype.linearIndependent_iff.mp hy_indep _ hrel t
  ext t
  have hp : (p : Bmax) ≠ 0 := (NeZero.of_faithfulSMul ℚ_[p] Bmax p).out
  simpa [hp, hb₀] using hb t

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `A = Amax`, and let `W = WittFq c.f` be the coefficient ring of a chart `c` for `Δ`, with
an algebra map `W → A` that agrees with `W → Ainf` after both are mapped to `Bmax` (`halg`). Let
`T` be finite free over `ℤ_p` with a representation `ρ` of `Δ`. A `W`-submodule `D` of invariant
elements of `A ⊗ T` is finite free, and `A ⊗_W D → A ⊗ T` is injective. -/
lemma finite_free_of_fixed_periods {c : Chart} (hc : c.IsChartOf (Γ := Δ) OverGp.toGp)
    [Algebra (WittFq c.f) Amax]
    (halg : ∀ a : WittFq c.f, algebraMap Amax Bmax (algebraMap (WittFq c.f) Amax a) =
      algebraMap Ainf Bmax (algebraMap (WittFq c.f) Ainf a)) {T : Type} [AddCommGroup T]
    [Module ℤ_[p] T] [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] {ρ : Representation ℤ_[p] Δ T}
    {D : Submodule (WittFq c.f) (Amax ⊗[ℤ_[p]] T)} (hD : ∀ y ∈ D, y ∈ fixedPeriods ρ Amax ⊤) :
    (⇑(D.subtype.liftBaseChange Amax)).Injective ∧
      Free (WittFq c.f) D ∧ Module.Finite (WittFq c.f) D := by
  have : HasUniqueDiv (Amax ⊗[ℤ_[p]] T) := .of_isTorsionFree Amax _
  have hindep {n : Type} [Fintype n] {y : n → D} (hy : LinearIndependent (WittFq c.f) y) :
      LinearIndependent Amax fun i : n ↦ (y i).val :=
    linearIndependent_of_mem_fixedPeriods hc halg (fun i ↦ hD _ (y i).prop)
      (hy.map' _ D.ker_subtype)
  -- `D` is `p`-adically separated and `p`-torsion free, of rank at most the rank of `A ⊗ T`.
  have hsep : IsHausdorff (Ideal.span {(p : WittFq c.f)}) D :=
    isHausdorff_of_injective_pi _
      (.restrictScalars _ (finBasis Amax _).equivFun.toLinearMap ∘ₗ D.subtype)
      ((finBasis Amax _).equivFun.injective.comp D.injective_subtype)
  have hrank : Module.rank (WittFq c.f) D ≤ finrank Amax (Amax ⊗[ℤ_[p]] T) :=
    rank_le fun s hs ↦ by simpa using (hindep hs).fintype_card_le_finrank
  -- So it is finite free by `free_finite_of_rank_le` (a criterion over a ring complete for a
  -- maximal ideal with two generators), with the ideal `(p)` written as `(0, p)`.
  have : (Ideal.span {(p : WittFq c.f)}).IsMaximal :=
    (isMaximal_iff _).mpr (irreducible p).maximalIdeal_eq.symm
  obtain ⟨hfree, hfinite⟩ : Free (WittFq c.f) D ∧ Module.Finite (WittFq c.f) D :=
    free_finite_of_rank_le span_insert_zero.symm hsep (by simp [ne, Nat.cast_smul_eq_nsmul]) _ hrank
      (by simp)
  -- A basis of `D` stays independent over `A`.
  refine ⟨injective_of_linearIndependent ((finBasis ..).baseChange _).span_eq ?_, hfree, hfinite⟩
  simpa [Function.comp_def] using hindep (finBasis ..).linearIndependent

/-- A finite free module over `Amax` is `p`-adically separated and complete: the bundle of
`eq_zero_of_forall_mem_nsmulRange` and `exists_forall_sub_mem_nsmulRange_of_sub_mem`. -/
lemma separated_and_complete_of_free (M : Type) [AddCommGroup M] [Module Amax M] [Free Amax M]
    [Module.Finite Amax M] :
    (∀ x : M, (∀ k : ℕ, x ∈ nsmulRange (p ^ k) M) → x = 0) ∧
    ∀ s : ℕ → M, (∀ {k m : ℕ}, k ≤ m → s k - s m ∈ nsmulRange (p ^ k) M) →
      ∃ x : M, ∀ k : ℕ, s k - x ∈ nsmulRange (p ^ k) M := by
  simpa only [isAdicComplete_iff, isHausdorff_iff, isPrecomplete_iff, SModEq.sub_mem, sub_zero,
    mem_span_pow_smul_top_iff] using isAdicComplete_of_free (S := Amax) (M := M) (.span {↑p})

/-- In a finite free `Amax`-module, an element that lies in `p ^ k M` for every `k` is zero. -/
lemma eq_zero_of_forall_mem_nsmulRange {M : Type} [AddCommGroup M] [Module Amax M] [Free Amax M]
    [Module.Finite Amax M] {x : M} (hx : ∀ k : ℕ, x ∈ nsmulRange (p ^ k) M) : x = 0 :=
  (separated_and_complete_of_free M).left x hx

/-- In a finite free `Amax`-module, a sequence `s` with `s k - s m ∈ p ^ k M` for `k ≤ m` has a
limit `x`: `s k - x ∈ p ^ k M` for every `k`. -/
lemma exists_forall_sub_mem_nsmulRange_of_sub_mem {M : Type} [AddCommGroup M] [Module Amax M]
    [Free Amax M] [Module.Finite Amax M] {s : ℕ → M}
    (hs : ∀ {k m : ℕ}, k ≤ m → s k - s m ∈ nsmulRange (p ^ k) M) :
    ∃ x : M, ∀ k : ℕ, s k - x ∈ nsmulRange (p ^ k) M :=
  (separated_and_complete_of_free M).right s hs

/-- For finite families `b k` in a module with topological basis `c` there are increasing finite
sets `S k` of indices that give every `b k i` modulo `I ^ k`; the other coordinates of `b k i` lie
in `I ^ k`. -/
lemma exists_monotone_coord_support {Λ A : Type} [CommRing Λ] [AddCommGroup A] [Module Λ A]
    {I : Ideal Λ} (c : AdicBasis I A) {n : ℕ → ℕ} (b : ∀ k : ℕ, Fin (n k) → A) :
    ∃ S : ℕ → Finset c.Index, Monotone S ∧
      (∀ (k : ℕ) (i : Fin (n k)),
        b k i - ∑ s ∈ S k, c.coord s (b k i) • c.b s ∈ I ^ k • (⊤ : Submodule Λ A)) ∧
      ∀ (k : ℕ) (i : Fin (n k)) (s : c.Index), s ∉ S k → c.coord s (b k i) ∈ I ^ k := by
  classical
  -- For each `k`, every large enough finite set of indices approximates all `b k i`; the partial
  -- unions of such sets are increasing.
  choose S hS using fun k : ℕ ↦ show ∃ S₀ : Finset c.Index, ∀ S' ⊇ S₀, ∀ i : Fin (n k),
      b k i - ∑ s ∈ S', c.coord s (b k i) • c.b s ∈ I ^ k • (⊤ : Submodule Λ A) from
    (Filter.eventually_all.mpr fun i ↦ c.eventually_sub_sum_mem (b k i) k).exists_forall_of_atTop
  refine ⟨partialSups S, (partialSups S).mono, fun k ↦ hS k _ (le_partialSups S k), ?_⟩
  -- The coordinate `s ∉ S k` of the approximating sum is `0`, so that of `b k i` lies in `I ^ k`.
  intro k i s hs
  have h_approx : b k i - Finsupp.linearCombination Λ c.b (∑ s' ∈ partialSups S k,
      Finsupp.single s' (c.coord s' (b k i))) ∈ I ^ k • (⊤ : Submodule Λ A) := by
    simpa using hS k _ (le_partialSups S k) i
  simpa [Finsupp.single_apply, hs] using c.coord_sub_mem_pow h_approx s

/-- Passage to the limit. Let `A = Amax` be an algebra over a `p`-adically complete ring `Λ` with
`(p)` maximal. Let `Q : M → N` and `Q' k : M → N' k` be `A`-linear, with `Q` zero modulo `p ^ k` on
the kernel of `Q' k`, and let `D ⊆ N`, `D' k ⊆ N' k` be `Λ`-submodules (`N` finite free over `A`,
`D` finite free over `Λ` and `p`-saturated, `A ⊗_Λ D' k → N' k` injective) such that the preimages
`Q' k ⁻¹' D' k` decrease and `D` holds the limits of their images. If `x` lies in the `A`-span of
every preimage, then `Q x` lies in the `A`-span of `D`. -/
lemma mem_span_of_forall_mem_span_preimage {Λ : Type} [CommRing Λ] [Algebra Λ Amax]
    [(Ideal.span {(p : Λ)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : Λ)}) Λ] {M N : Type}
    {N' : ℕ → Type} [AddCommGroup M] [Module Amax M] [Module Λ M] [IsScalarTower Λ Amax M]
    [AddCommGroup N] [Module Amax N] [Module Λ N] [IsScalarTower Λ Amax N] [Free Amax N]
    [Module.Finite Amax N] [∀ k : ℕ, AddCommGroup (N' k)] [∀ k : ℕ, Module Amax (N' k)]
    [∀ k : ℕ, Module Λ (N' k)] [∀ k : ℕ, IsScalarTower Λ Amax (N' k)] {Q : M →ₗ[Amax] N}
    {Q' : ∀ k : ℕ, M →ₗ[Amax] N' k} {D : Submodule Λ N} [Free Λ D] [Module.Finite Λ D]
    {D' : ∀ k : ℕ, Submodule Λ (N' k)}
    (hker : ∀ (k : ℕ) (v : M), Q' k v = 0 → Q v ∈ nsmulRange (p ^ k) N)
    (hinj : ∀ k : ℕ, (⇑((D' k).subtype.liftBaseChange Amax)).Injective)
    (hanti : ∀ (k m : ℕ) (v : M), k ≤ m → Q' m v ∈ D' m → Q' k v ∈ D' k)
    (hclosed : ∀ z : N, (∀ k : ℕ, ∃ v : M, Q' k v ∈ D' k ∧ Q v - z ∈ nsmulRange (p ^ k) N) → z ∈ D)
    (hsat : ∀ (k : ℕ) (v : N), p ^ k • v ∈ D → v ∈ D) {x : M}
    (hx : ∀ k : ℕ, x ∈ span Amax (Q' k ⁻¹' D' k)) : Q x ∈ span Amax (D : Set N) := by
  classical
  -- Write `x = ∑ i, b k i • y k i` with `Q' k (y k i) ∈ D' k`. `U s k` is this sum with each
  -- `b k i` replaced by its `s`-th coordinate in a topological basis `c` of `A` over `Λ`.
  choose n b y hy using fun k ↦ mem_span_set'.mp (hx k)
  obtain ⟨c⟩ : Nonempty (AdicBasis (Ideal.span {(p : Λ)}) Amax) := Amax.nonempty_adicBasis Λ rfl
  let U (s : c.Index) (k : ℕ) : M := ∑ i, c.coord s (b k i) • (y k i).val
  have hU (s : c.Index) (k : ℕ) : Q' k (U s k) ∈ D' k := by
    simpa [U] using sum_mem fun i _ ↦ (D' k).smul_mem (c.coord s (b k i)) (y k i).prop
  -- For `k ≤ m` both sums give elements of `A ⊗_Λ D' k` with image `Q' k x`; by injectivity they
  -- agree, and so do their coordinates.
  have hU_compat (s : c.Index) {k m : ℕ} (hkm : k ≤ m) : Q' k (U s k - U s m) = 0 := by
    let v (m : ℕ) (hkm : k ≤ m) : Amax ⊗[Λ] D' k :=
      ∑ i, b m i ⊗ₜ[Λ] (⟨_, hanti k m _ hkm (y m i).prop⟩ : D' k)
    have hv : v k le_rfl = v m hkm := hinj k (by simpa [v, ← hy m] using congrArg (Q' k) (hy k))
    -- Apply the `s`-th coordinate to both sides of `hv`.
    simpa [U, v, sub_eq_zero] using
      congrArg (fun t ↦ (lift (lsmul Λ (D' k) ∘ₗ c.coord s) t).val) hv
  -- So `Q (U s k)` converges to some `z s`, which lies in `D`.
  choose z hz using fun s ↦ exists_forall_sub_mem_nsmulRange_of_sub_mem (s := fun k ↦ Q (U s k))
    fun hkm ↦ by simpa using hker _ _ (hU_compat s hkm)
  lift z to c.Index → D using fun s ↦ hclosed _ fun k ↦ ⟨U s k, hU s k, hz s k⟩
  -- Outside `S k` the coordinates of the `b k i` are divisible by `p ^ k`, hence so is `z s`, also
  -- in `D` because `D` is saturated.
  obtain ⟨S, hS_mono, hS, hcoord⟩ := exists_monotone_coord_support c b
  have hz_small (k : ℕ) (s : c.Index) (hs : s ∉ S k) : z s ∈ nsmulRange (p ^ k) D := by
    have hU_small : U s k ∈ nsmulRange (p ^ k) M :=
      sum_mem fun i _ ↦ mem_span_pow_smul_top_iff.mp (smul_mem_smul (hcoord k i s hs) mem_top)
    obtain ⟨v, hv : p ^ k • v = (z s : N)⟩ : (z s).val ∈ nsmulRange (p ^ k) N := by
      simpa using sub_mem (nsmulRange.map_mem Q hU_small) (hz s k)
    exact ⟨⟨v, hsat k v (by simp [hv])⟩, Subtype.ext hv⟩
  -- So the partial sums of `∑ s, c.b s ⊗ z s` form a Cauchy sequence: the terms added between
  -- `S k` and `S m` lie in `p ^ k (A ⊗_Λ D)`.
  have h_cauchy {k m : ℕ} (hkm : k ≤ m) : ∑ s ∈ S k, c.b s ⊗ₜ[Λ] z s - ∑ s ∈ S m, c.b s ⊗ₜ[Λ] z s ∈
      nsmulRange (p ^ k) (Amax ⊗[Λ] ↥D) := by
    rw [sub_mem_comm_iff, ← sum_sdiff_eq_sub (hS_mono hkm)]
    exact sum_mem fun s hs ↦
      nsmulRange.map_mem (mk Λ Amax _ _) (hz_small k s (Finset.mem_sdiff.mp hs).right)
  -- It converges to some `ω` in `A ⊗_Λ D`.
  obtain ⟨ω, hω⟩ : ∃ ω, ∀ k, ∑ s ∈ S k, c.b s ⊗ₜ[Λ] z s - ω ∈ nsmulRange (p ^ k) (Amax ⊗[Λ] ↥D) :=
    exists_forall_sub_mem_nsmulRange_of_sub_mem h_cauchy
  -- Modulo `p ^ k` the image of `ω` is `∑ s ∈ S k, c.b s • z s ≡ ∑ s ∈ S k, c.b s • Q (U s k)`,
  -- which is `∑ i, (∑ s ∈ S k, c.coord s (b k i) • c.b s) • Q (y k i) ≡ Q x`.
  suffices hω_eq : Q x = D.subtype.liftBaseChange Amax ω by
    simpa using (D.subtype.range_liftBaseChange Amax).le ⟨ω, hω_eq.symm⟩
  refine eq_of_sub_eq_zero (eq_zero_of_forall_mem_nsmulRange fun k ↦ ?_)
  have hb_close : ∑ i, (b k i - ∑ s ∈ S k, c.coord s (b k i) • c.b s) • Q (y k i) ∈
      nsmulRange (p ^ k) N :=
    sum_mem fun i _ ↦
      nsmulRange.map_mem (toSpanSingleton _ _ (Q (y k i))) (mem_span_pow_smul_top_iff.mp (hS k i))
  have hz_close : ∑ s ∈ S k, c.b s • (Q (U s k) - z s) ∈ nsmulRange (p ^ k) N :=
    sum_mem fun s _ ↦ nsmulRange.map_mem (lsmul _ _ (c.b s)) (hz s k)
  have hω_close :
      D.subtype.liftBaseChange Amax (∑ s ∈ S k, c.b s ⊗ₜ[Λ] z s - ω) ∈ nsmulRange (p ^ k) N :=
    nsmulRange.map_mem _ (hω k)
  -- The sum of these three differences telescopes to `Q x` minus the image of `ω`.
  simpa [U, ← hy k, sub_smul, sum_smul, smul_sum, smul_sub, univ.sum_comm, smul_comm (c.b _)] using
    add_mem (add_mem hb_close hz_close) hω_close

omit [TopologicalSpace G] [CompactSpace G] [∀ η : I, Finite (ι η)] in
/-- The kernel step of `isCrystalline_of_trace_limit`, for `R: PadicRep G p` (any group `G`) and
families `X η` (`η: I`) indexed by `ι η`; `groupRingHom` extends a representation linearly to
`ℤ_p[G]`. Let `u (q y)` extend `R` (`hu`), let traces of `R` bound `p`-divisibility in `T`
(`htrace`), let the trace of `R` be small on the common kernel of each family `X (η k)` (`hη`), and
let each surjection `π k` have as kernel the common kernel of the `X (η l)`, `l ≤ k` (`hπ_ker`).
Then over `Amax` an element killed by `π k` is sent by `q` into `p ^ k (Amax ⊗ T)` and killed by
every `π l`, `l ≤ k`. -/
private lemma baseChange_mem_nsmulRange_and_eq_zero_of_eq_zero {T : AlgCat ℤ_[p]}
    {q : ℤ_[p][G] →ₐ[ℤ_[p]] T} {u : T →ₐ[ℤ_[p]] Matrix R.Index R.Index (PadicAlgCl p)}
    (hu : ∀ y : ℤ_[p][G], u (q y) = groupRingHom R y) {ε : ℕ → ℝ}
    (htrace : ∀ (k : ℕ) (t : T),
      (∀ g : G, ‖(u t * R.rep g).trace‖ ≤ ε k) → t ∈ nsmulRange (p ^ k) T)
    {X : ∀ η : I, ι η → PadicRep G p} {η : ℕ → I}
    (hη : ∀ (k : ℕ) (y : ℤ_[p][G]),
      (∀ x : ι (η k), groupRingHom (X (η k) x) y = 0) → ‖(groupRingHom R y).trace‖ ≤ ε k)
    {T' : ℕ → AlgCat ℤ_[p]} {π : ∀ k : ℕ, ℤ_[p][G] →ₐ[ℤ_[p]] T' k}
    (hπ : ∀ k : ℕ, Function.Surjective (π k))
    (hπ_ker : ∀ (k : ℕ) (y : ℤ_[p][G]), π k y = 0 ↔
      ∀ s : Σ l : Set.Iic k, ι (η l.val), groupRingHom (X (η s.fst.val) s.snd) y = 0)
    {k : ℕ} {v : Amax ⊗[ℤ_[p]] ℤ_[p][G]} (hv : (π k).toLinearMap.baseChange Amax v = 0) :
    q.toLinearMap.baseChange Amax v ∈ nsmulRange (p ^ k) (Amax ⊗[ℤ_[p]] T) ∧
      ∀ l ≤ k, (π l).toLinearMap.baseChange Amax v = 0 := by
  -- First for `z` in `ℤ_p[G]`: the traces of `R` on `z` are small, and `z` lies in the kernel of
  -- `π l` for every `l ≤ k`.
  have hker_π (z : ℤ_[p][G]) (hz : π k z = 0) :
      q z ∈ nsmulRange (p ^ k) T ∧ ∀ l ≤ k, π l z = 0 := by
    have hX₀ (l : ℕ) (hl : l ≤ k) (x : ι (η l)) : groupRingHom (X (η l) x) z = 0 :=
      (hπ_ker k z).mp hz ⟨⟨l, hl⟩, x⟩
    refine ⟨htrace k _ fun g ↦ ?_, fun l hl ↦ (hπ_ker l z).mpr fun s ↦ ?_⟩
    · simpa [hu] using hη k (z * .single g 1) (by simp [hX₀ k le_rfl])
    · exact hX₀ _ (s.fst.prop.trans hl) _
  -- Then after base change: `v` is a sum of elements `a ⊗ z` with `π k z = 0`.
  obtain ⟨v, rfl⟩ : v ∈ Set.range (lTensor Amax (ker (π k).toLinearMap).subtype) :=
    (lTensor_exact Amax (exact_subtype_ker_map (π k).toLinearMap) (hπ k) v).mp hv
  clear hv
  induction v with
  | tmul a z =>
    exact (hker_π z z.prop).imp (nsmulRange.map_mem (mk ℤ_[p] Amax T a)) (by simp +contextual)
  | add x y hx hy =>
    exact ⟨by simpa using add_mem hx.1 hy.1, fun l hl ↦ by simp [hx.2 l hl, hy.2 l hl]⟩

/-- Let `G` be a compact group, `Δ` a group with a homomorphism `j : Δ → G_p` of open image
(`OverGp Δ p`), `w : Δ → ℤ_p[G]` multiplicative, and `R : G → GL_m(ℚ̄_p)` continuous with trace form
non-degenerate on the span of the matrices `R(g)`. Let `X η` be finite families of continuous
representations of `G` over `ℚ̄_p` whose pullbacks `g ↦ X(w(g))` along `w` (`viaGroupRing`, through
the linear extension `groupRingHom` to `ℤ_p[G]`; `η : I`, members indexed by finite `ι η`) are
crystalline (with respect to `j`) with Hodge–Tate jumps in `[0, h]`. If for each `ε > 0` some `X η`
has `‖tr R(y)‖ ≤ ε` for all `y ∈ ℤ_p[G]` killed by every member of `X η`, then the pullback of `R`
along `w` is crystalline. -/
lemma isCrystalline_of_trace_limit [IsTopologicalGroup G]
    {h : ℕ} (hR : Continuous R.rep) (hR_nondeg : IsTraceNondeg R.rep)
    {X : ∀ η : I, ι η → PadicRep G p}
    (hX_crys : ∀ (η : I) (x : ι η), IsCrystallineUpTo h (viaGroupRing w (X η x)))
    (hX : ∀ (η : I) (x : ι η), Continuous (X η x).rep)
    (happrox : ∀ ε > (0 : ℝ), ∃ η : I, ∀ y : ℤ_[p][G],
      (∀ x : ι η, groupRingHom (X η x) y = 0) → ‖(groupRingHom R y).trace‖ ≤ ε) :
    IsCrystalline (viaGroupRing w R) := by
  -- Let `T` be the image of `ℤ_p[G]` under `R`, and `T' k` its image under families `0, …, k`,
  -- chosen so that the kernel of `ℤ_p[G] → T' k` dies in `T / p ^ k`. One period `δ` puts `δ ⊗ 1`
  -- in the `A`-span (`A = Amax`) of the invariants of every `A ⊗ T' k`, hence, in the limit, of
  -- those of `A ⊗ T`. `Λ` is the coefficient ring of a chart for `Δ`, fixed by `Δ` (`hfix`).
  obtain ⟨chart, hfix, -⟩ := exists_kummerChart Δ
  -- `δ ∈ A` is a unit in `Bmax`, and `δ ⊗ t` lies in the `A`-span of the invariants of `A ⊗ L`
  -- for every crystalline lattice `L` with jumps in `[0, h]` and every `t ∈ L`.
  obtain ⟨δ, hδ_unit, hδ⟩ := uniform_period_bound Δ h
  let A : Type := Amax
  let Λ : Type := WittFq chart.f
  -- `Λ` acts on `A` through `Ainf`.
  let h_algebra : Algebra Λ A := Algebra.compHom A (algebraMap Λ Ainf)
  have h_max : (Ideal.span {(p : Λ)}).IsMaximal :=
    (isMaximal_iff _).mpr (irreducible p).maximalIdeal_eq.symm
  -- Torsion-free `A`-modules have no additive torsion (used below as an instance).
  have h_torsionFree := HasUniqueDiv.of_isTorsionFree.{0, 0} A
  -- The invariants of `A ⊗ T` form a `Λ`-module, as the group fixes `Λ`.
  let D {T : AlgCat ℤ_[p]} (q : ℤ_[p][G] →ₐ[ℤ_[p]] T) : Submodule Λ (A ⊗[ℤ_[p]] T) :=
    { carrier := fixedPeriods (actionRep ℤ_[p] T (q.toMonoidHom.comp w)) A ⊤
      add_mem' := by simp +contextual [fixedPeriods]
      zero_mem' := by tauto
      smul_mem' a _ hy g := by
        erw [← algebraMap_smul A, mem_ofPred, tensorAction_smul, hy,
          smul_algebraMap_eq_algebraMap_smul (A := Ainf), (hfix _).1]
        rfl }
  have hD {T : AlgCat ℤ_[p]} [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] (q : ℤ_[p][G] →ₐ[ℤ_[p]] T) :
      (⇑((D q).subtype.liftBaseChange A)).Injective ∧ Free Λ (D q) ∧ Module.Finite Λ (D q) :=
    finite_free_of_fixed_periods chart.chart_isChartOf (fun _ ↦ rfl) fun _ hy ↦ hy
  -- The lattices `q : ℤ_p[G] → T` and `π k : ℤ_p[G] → T' k`.
  obtain ⟨T, q, u, hT_free, hT_finite, hq, hu, hq_ker, -⟩ :=
    exists_finite_groupRing_quotient Δ fun _ : Unit ↦ hR
  obtain ⟨-, hDq_free, hDq_finite⟩ := hD q
  -- Traces control divisibility by `p ^ k` in `T`, and the trace of `R` is small on the common
  -- kernel of some family `X (η k)`.
  choose ε hε htrace using
    exists_pos_mem_pow_of_norm_trace_le hR hR_nondeg hq (hu ()) fun y hy ↦ (hq_ker y).mpr fun _ ↦ hy
  choose η hη using fun k ↦ happrox (ε k) (hε k)
  -- `T' k` is the image of `ℤ_p[G]` in the families `X (η l)`, `l ≤ k`.
  choose T' π _u' hT' using fun k ↦
    exists_finite_groupRing_quotient Δ fun s : Σ l : Set.Iic k, ι (η l.val) ↦ hX _ s.snd
  have hT'_free (k : ℕ) : Free ℤ_[p] (T' k) := (hT' k).free
  have hT'_finite (k : ℕ) : Module.Finite ℤ_[p] (T' k) := (hT' k).finite
  let Q : A ⊗[ℤ_[p]] ℤ_[p][G] →ₗ[A] A ⊗[ℤ_[p]] T := q.toLinearMap.baseChange A
  let Q' (k : ℕ) : A ⊗[ℤ_[p]] ℤ_[p][G] →ₗ[A] A ⊗[ℤ_[p]] T' k := (π k).toLinearMap.baseChange A
  -- The kernel of `Q' k` dies in `(A ⊗ T) / p ^ k` and in `A ⊗ T' l` for `l ≤ k`.
  have hker {k : ℕ} {v : A ⊗[ℤ_[p]] ℤ_[p][G]} (hv : Q' k v = 0) :
      Q v ∈ nsmulRange (p ^ k) _ ∧ ∀ l ≤ k, Q' l v = 0 :=
    baseChange_mem_nsmulRange_and_eq_zero_of_eq_zero (hu ()) htrace hη (fun k ↦ (hT' k).surjective)
      (fun k ↦ (hT' k).apply_eq_zero_iff) hv
  -- Invariance of `Q' k v`, read in `A ⊗ ℤ_p[G]`.
  have hinv {k : ℕ} {v : A ⊗[ℤ_[p]] ℤ_[p][G]} : Q' k v ∈ D (π k) ↔
      ∀ g : Δ, Q' k (tensorAction A (OverGp.toGp g) (mulLeft ℤ_[p] (w g)) v - v) = 0 :=
    forall_congr' fun g ↦ (tensorAction_periodTensorMap (g := mulLeft ℤ_[p] (w g))
      (by simp) (OverGp.toGp g) v).congr_left.trans sub_mem_ker_iff.symm
  -- The uniform period: `δ ⊗ 1` is in the `A`-span of the `v` with `Q' k v` invariant.
  have hspan (k : ℕ) : δ ⊗ₜ 1 ∈ span A (Q' k ⁻¹' D (π k)) := by
    rw [span_preimage_eq (f := Q' k) (D _).nonempty
      fun x _hx ↦ lTensor_surjective A (hT' k).surjective x]
    exact (hδ (finBasis ℤ_[p] (T' k)) ((hT' k).isCrystallineUpTo fun s ↦ hX_crys _ s.snd)).left _
  -- An element that is invariant modulo every `p ^ k` is invariant.
  have hclosed (z : A ⊗[ℤ_[p]] T)
      (hz : ∀ k : ℕ, ∃ v, Q' k v ∈ D (π k) ∧ Q v - z ∈ nsmulRange (p ^ k) _) : z ∈ D q := by
    refine fun g ↦ eq_of_sub_eq_zero (eq_zero_of_forall_mem_nsmulRange fun k ↦ ?_)
    obtain ⟨v, hv, hvz⟩ := hz k
    let σ := tensorAction A (OverGp.toGp g) (actionRep ℤ_[p] T (q.toMonoidHom.comp w) g)
    have h₁ : σ (Q v) - Q v ∈ nsmulRange (p ^ k) _ := by
      -- `erw`: `σ` is the action on `A ⊗ T` written through `q`, which `rw` does not unfold.
      erw [tensorAction_periodTensorMap (g := mulLeft ℤ_[p] (w g)) (by simp), ← map_sub]
      exact (hker (hinv.mp hv g)).left
    -- `σ z - z = (σ (Q v) - Q v) - σ (Q v - z) + (Q v - z)`
    simpa [σ] using add_mem (sub_mem h₁ (nsmulRange.map_mem σ hvz)) hvz
  -- `D q` is saturated because `A ⊗ T` is torsion free.
  have hsat (k : ℕ) (v : A ⊗[ℤ_[p]] T) (hv : p ^ k • v ∈ D q) : v ∈ D q :=
    fun g ↦ by simpa [NeZero.ne, -nsmul_eq_mul] using hv g
  -- In the limit, `δ ⊗ 1` is in the `A`-span of the invariants of `A ⊗ T`.
  have hδ_span : Q (δ ⊗ₜ 1) ∈ span A (D q : Set (A ⊗[ℤ_[p]] T)) :=
    mem_span_of_forall_mem_span_preimage (fun _ _ hv ↦ (hker hv).left) (fun k ↦ (hD (π k)).left)
      (fun k _ _ hkm hv ↦ hinv.mpr fun g ↦ (hker (hinv.mp hv g)).right k hkm) hclosed hsat hspan
  -- The equivariant map `t ↦ u () t * v` carries this to `δ ⊗ v`, and `δ` is a unit in `Bmax`.
  refine isAdmissible_of_one_tmul_mem_span fun v ↦
    (smul_mem_iff_of_isUnit _ hδ_unit).mp (span_subset_span A _ _ ?_)
  simpa [Q, periodTensorMap, Algebra.smul_def] using
    mapsTo_span (f := periodTensorMap A Bmax (applyVec (u ()).toLinearMap v))
      (fun y hy ↦ fixedPeriods.periodTensorMap_mem (by simp [hu]) hy) hδ_span

end New.Period

end CrystallineLimit
