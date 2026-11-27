import New.Determinant.Exchange.LargeTriple

/-!
# Change of point and sign, and descent of the exchange identity by removing hyperbolic planes

This file records how forms and theta integrals behave under passage to opposite signs and under
change of point. It also descends the exchange identity `New.Exchange.RowColExchangeIdentity`
between theta integrals from a pair of large spaces to the pair with hyperbolic planes removed. For
any number of planes there is a space with an adapted splitting over a given space `W`.

## Main definitions and results

* `New.Exchange.isForm_neg_iff_and_integral_neg`: passing to the opposite signs (`G.neg`, the
  identity on matrices) preserves forms of a given type and integrals over the quotient, if it
  matches the rational points of the two spaces.
* `New.Exchange.exists_thetaLarge_thetaSmall_eq_circle_mul`: triples of spaces with the same signs
  have the same integrals `thetaLarge` and `thetaSmall`, up to one translation and numbers of
  modulus one.
* `New.Exchange.RowColExchangeIdentity.cone`: the identity descends along one plane of adapted
  splittings, to the cone integral of the real vector, if `rk W` is even and `rk V ≥ rk W / 2`;
  `New.Exchange.RowColExchangeIdentity.dualCone` is the case `rk V < rk W / 2`, on the other side of
  Poisson's formula.
* `New.Exchange.exists_rowColExchangeIdentity_removing_planes`: the identity descends along the
  planes of an adapted splitting, if `rk W` is even and `V'` has as many more negative signs than
  `V` as planes.

Notions from other files:
* `New.Exchange.RowColExchangeIdentity W V U μ σ x y ℓ`: the real vectors `x`, `y` are Schwartz
  vectors (all their weighted norms are finite), and for every tame character `𝔠` of weight `μ` the
  theta integrals `thetaLarge` over `[U(V)]` and `thetaSmall` over `[U(U)]` are proportional on
  standard data, with a factor `c` such that `D |c| ^ 2` is
  `lValueProdInt 𝔠 (rk V - rk W / 2) * ℓ 𝔠` for a constant `D` that does not depend on `𝔠`. The
  bijection `σ : b ⊕ r ≃ n` of the index sets of `U`, `V`, `W` orders the rows of the standard data.
* `New.Space.Splitting`: a decomposition V = (lE^p ⊕ kE^p) ⊥ iV₀ over E: isotropic frames l, k with
  l*Jk = 1, an isometry i from V₀ orthogonal to both, and rk V = rk V₀ + 2p.
* `New.Exchange.realSlice A U x`: the slice at `x` of a real vector for `(W', U)` in the mixed model
  of the splitting `A` of `W'` over `W`, a real vector for `(W, U)`; at `x = 0` it is the zero term.
* `New.stdColDatum χ z`: the standard datum `y ↦ χ⁻¹(det (z y))`, supported on the integral `y` for
  which this determinant is a unit.

## Relation to the literature

See `Lib.Weil.DualPair.ThetaLiftConvergence` for sources.
-/

namespace New.Exchange

/-! ## Forms and theta integrals under change of point and sign -/

section ChangeOfSpace

open Matrix MeasureTheory Space G

variable {E : Type} [Field E] [CMType E] {n a : Type} [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a] {s : n → ℤˣ} {t : a → ℤˣ}

attribute [mk_iff] IsForm Space.IsAutomorphic

/-- `G.neg` carries the rational points of `W` onto those of the opposite space `W.neg`, whose point
is a scalar multiple of that of `W`. -/
lemma neg_mem_neg_Gamma_iff [WeilData E]
    (W : Space E n s) (g : G E s) : G.neg g ∈ W.neg.Γ ↔ g ∈ W.Γ := by
  simp [Space.neg, Space.mem_Gamma_iff_range]

/-- Let `W` and `S` be Hermitian spaces with opposite signs `s`, `-s`, and let `G.neg` carry the
rational points `W.Γ` onto `S.Γ`. Let `typeKernel l s` be the product over the infinite places `w`
of the discrete series kernels with doubled parameters `l w`. Then `F` is a form of type
`typeKernel l (-s)` on `S` if and only if its pull-back along `G.neg` is a form of type
`typeKernel l s` on `W`, and integrals over the two quotients agree under this pull-back. -/
lemma isForm_neg_iff_and_integral_neg (W : Space E n s) (S : Space E n (-s))
    (hΓ : ∀ g : G E s, G.neg g ∈ S.Γ ↔ g ∈ W.Γ) :
    -- (a) forms correspond under `G.neg`
    (∀ (l : NumberField.InfinitePlace E → n → ℤ) (F : G E (-s) → ℂ),
      W.IsForm (typeKernel l s) (fun g : G E s ↦ F (G.neg g)) ↔ S.IsForm (typeKernel l (-s)) F) ∧
    -- (b) so do the measures on the quotients
    ∀ F : G E (-s) → ℂ,
      ∫ g : G E (-s), F g ∂S.quotMeasure = ∫ g : G E s, F (G.neg g) ∂W.quotMeasure := by
  -- `U (signMatrix (-s))` is the same subgroup as `U (signMatrix s)`, with the same Haar measure.
  have h_group : U (signMatrix s : Matrix n n ℂ) = U (signMatrix (-s)) := by simp [U]
  -- This is stated for any proof `h_mem` that the subgroups agree, as that proof changes below.
  have h_haar (h_mem : ∀ g : GL n ℂ, g ∈ U (signMatrix s) ↔ g ∈ U (signMatrix (-s))) :
      MeasurePreserving (Equiv.subtypeEquivRight h_mem : USign s ≃ USign (-s)) :=
    measurePreserving_haarU 1 1 (-1) _ (by simp) (by simp)
  -- Both claims hold by definition once the subgroup and its measure are identified. To see this,
  -- unfold the notions that mention `s` until it enters only through these two and the relation
  -- `s i = s j`, which is the same for `-s`. Some occurrences are in types, so `delta` is used.
  simp_rw [isForm_iff, isAutomorphic_iff, quotMeasure]
  generalize W.Γ = Γ' at *
  delta HasLevel realConv typeKernel dsKernel formalDegree dsCoeff blockDiagPart flenstedJensen
    kTypeNormSq lowestKType haarK maxCompactU G.neg USign G GInf measureSpaceU at *
  simp_rw [Pi.neg_apply, neg_inj]
  -- The group occurs in types, so it is made a variable `H` (with the instance proofs about it)
  -- before it is replaced by the group for `-s`; then `G.neg` is the identity.
  generalize_proofs at *
  generalize U (signMatrix s) = H, haarU (signMatrix s) = μ' at *
  subst h_group
  obtain rfl : S.Γ = Γ' := Subgroup.ext hΓ
  obtain rfl : μ' = haarU (signMatrix (-s)) := Measure.map_id.symm.trans (h_haar (by simp)).map_eq
  exact ⟨fun _ _ ↦ Iff.rfl, fun _ ↦ rfl⟩

/-- Let the points `W.x`, `W₁.x` differ by a rational matrix `c` on the left and an adelic unitary
element `k` on the right, and likewise those of `V` and `V₁` by `c'` and `k'`. Then the rational
vectors (`ratVectors`) of the space `W.hom V` of `a × n` matrices are rational for `W₁`, `V₁` with
their points multiplied on the right by `k`, `k'` (`Space.move`). -/
lemma mem_ratVectors_hom_move {W W₁ : Space E n s} {V V₁ : Space E a t}
    {c : GL n E} {k : G E s} {c' : GL a E} {k' : G E t}
    (hk : W.x = (c.map toAdele)⁻¹ * W₁.x * k.toUnitary)
    (hk' : V.x = (c'.map toAdele)⁻¹ * V₁.x * k'.toUnitary)
    {y : a × n → 𝔸 E} (hy : y ∈ (W.hom V).ratVectors) :
    y ∈ ((W₁.move k).hom (V₁.move k')).ratVectors := by
  obtain ⟨x, hx⟩ : ∃ x : Matrix a n E, x.map toAdele = V.x.val * vecToMatrix y * W.x⁻¹.val :=
    mem_ratVectors_hom.1 hy
  -- The rational matrix `x` goes to `c' x c⁻¹`.
  refine mem_ratVectors_hom.2 ⟨c'.val * x * c⁻¹.val, ?_⟩
  calc (c'.val * x * c⁻¹.val).map toAdele
    _ = (c'.map toAdele).val * x.map toAdele * (c.map toAdele)⁻¹.val := by
      rw [Matrix.map_mul, Matrix.map_mul, ← map_inv]
      rfl
    _ = (V₁.move k').x.val * vecToMatrix y * (W₁.move k).x⁻¹.val := by
      simp only [hx, hk, hk', move, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc,
        ← (c'.map toAdele).val.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.one_mul]

variable [WeilData E]

/-- Let the points of `W` and `W₁` differ by a rational matrix `c` on the left and by `k` in the
adelic unitary group on the right, and let `V`, `V₁` have the same signs. Let the semilocal field
`F` be read off from the finite adeles at the places `A` by `π` (`ReadsAt`). For any characters `α`,
`β`, consider the datum with real part `v`, the function `Φ` of the components in `F`, and the
vacuum at the other places. Its theta integral for `(W, V)` at `g` is `u` times that for `(W₁, V₁)`
at `k * g`, where `u` has modulus one and does not depend on `v`, `Φ`, `g`. -/
lemma exists_circle_thetaIntegral_localDatum_eq_mul (W W₁ : Space E n s) (V V₁ : Space E a t)
    (c : GL n E) (k : G E s) (hk : W.x = (c.map toAdele)⁻¹ * W₁.x * k.toUnitary) (α β : AutChar E)
    {F : Type} [SemilocalField F] {A : Set (FinPlace E)} {π : 𝔸f E →+* F} (hπ : ReadsAt A π) :
    ∃ u : Circle, ∀ (v : PairFock E s t) (Φ : Matrix a n F → ℂ) (g : G E s),
      thetaIntegral W V α β (localDatum W V v Φ hπ) g =
        u * thetaIntegral W₁ V₁ α β (localDatum W₁ V₁ v Φ hπ) (k * g) := by
  -- Landherr's theorem gives `c'`, `k'` that move `V₁` to `V`. Left translation by `(k, k')`
  -- carries the theta kernel of `(W, V)` to that of `(W₁, V₁)`, up to the value
  -- `β (det k) / α (det k')` of the characters.
  obtain ⟨c', k', hc', hk', emb_conj⟩ :
      ∃ (c' : GL a E) (k' : G E t) (hc' : c'.valᴴ * V₁.J * c'.val = V.J),
        V.x = (c'.map toAdele)⁻¹ * V₁.x * k'.toUnitary ∧
        ∀ γ : U V.J, V₁.ratEmbed (U.conj c' hc' γ) = k' * V.ratEmbed γ * k'⁻¹ :=
    V₁.exists_x_eq_and_ratEmbed_conj_eq V
  -- A space enters `θ` only through its rational vectors.
  have θ_eq (f : 𝒮 ((W₁.move k).hom (V₁.move k'))) :
      (W.hom V).θ f = ((W₁.move k).hom (V₁.move k')).θ f := by
    simpa using theta_eq_theta_omega (g := 1)
      (fun y hy ↦ by simpa using mem_ratVectors_hom_move hk hk' hy) f
  let u : Circle := β.val k.det / α.val k'.det
  refine ⟨u, fun v Φ g ↦ ?_⟩
  let kernel₁ (h : G E t) : ℂ := pairTheta W₁ V₁ α β (localDatum W₁ V₁ v Φ hπ) (k * g, h)
  -- The datum and the Weil representation depend on the spaces only through their signs.
  have h_datum : localDatum W V v Φ hπ = localDatum W₁ V₁ v Φ hπ := by
    delta localDatum schrodingerOp
    rfl
  have kernel_eq (h : G E t) :
      pairTheta W V α β (localDatum W V v Φ hπ) (g, h) = u * kernel₁ (k' * h) :=
    calc pairTheta W V α β (localDatum W V v Φ hπ) (g, h)
      _ = pairTheta (W₁.move k) (V₁.move k') α β (localDatum W₁ V₁ v Φ hπ) (g, h) := by
        rw [h_datum]
        exact θ_eq (pairWeil W V α β (g, h) (localDatum W₁ V₁ v Φ hπ))
      _ = u * kernel₁ (k' * h) := by rw [pairTheta_move, Circle.coe_div, div_eq_mul_inv]
  -- Translation by `k'` identifies the quotients by `V.Γ` and by `V₁.Γ = k' V.Γ k'⁻¹`.
  have Γ_conj (γ : G E t) : γ ∈ V.Γ ↔ MulAut.conj k' γ ∈ V₁.Γ := by
    simp [Γ, reindex_equiv (U.conj _ hc'), emb_conj]
  have kernel₁_inv (γ : V₁.Γ) (h : G E t) : kernel₁ (γ • h) = kernel₁ h :=
    (pairThetaKer W₁ V₁ α β).swap.theta_rat_mul γ γ.property h
  have same_distrib : ProbabilityTheory.IdentDistrib (fun h : G E t ↦ kernel₁ (k' * h)) kernel₁
      V.quotMeasure V₁.quotMeasure :=
    identDistrib_orbitMeasure_comp (measurePreserving_count ((MulAut.conj k').subtypeEquiv Γ_conj))
      (measurePreserving_mul_left _ k') (by simp [Subgroup.smul_def, mul_assoc]) kernel₁_inv
  calc thetaIntegral W V α β (localDatum W V v Φ hπ) g
    _ = ∫ h, u * kernel₁ (k' * h) ∂V.quotMeasure := congrArg _ (funext kernel_eq)
    _ = u * thetaIntegral W₁ V₁ α β (localDatum W₁ V₁ v Φ hπ) (k * g) := by
      rw [integral_const_mul, same_distrib.integral_eq]
      rfl

/-- Let the points of `W` and `W₁` differ by a rational matrix `c` on the left and `k` in the adelic
unitary group on the right, and let `V`, `V₁` have the same signs. Let `𝔠` be a character of
`[U(1)]` of weight `μ` at the infinite places, tamely ramified at a finite set `𝔠.ramifiedPlaces`
of split places. For a vector `v` of the Fock space and a function `Φ` of matrices over the product
`LocProd` of the completions at these places, `thetaLarge W V 𝔠 v Φ` is the theta integral over
`[U(V)]` of the datum that is `v` at the infinite places, `Φ` at the ramified places and the vacuum
elsewhere. Its value at `g` is `u` times the value for `(W₁, V₁)` at `k * g`, where `u` has modulus
one and does not depend on `v`, `Φ`, `g`. -/
lemma exists_thetaLarge_eq_mul_thetaLarge (W W₁ : Space E n s) (V V₁ : Space E a t)
    (c : GL n E) (k : G E s) (hk : W.x = (c.map toAdele)⁻¹ * W₁.x * k.toUnitary)
    {μ : NumberField.InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ) :
    ∃ u : Circle, ∀ (v : PairFock E s t) (Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
      (g : G E s),
      thetaLarge W V 𝔠 v Φ g = u * thetaLarge W₁ V₁ 𝔠 v Φ (k * g) :=
  exists_circle_thetaIntegral_localDatum_eq_mul W W₁ V V₁ c k hk (rankTwist 𝔠.character⁻¹ n)
    (rankTwist 𝔠.character⁻¹ n) 𝔠.readsAt

/-- Let `W, W₁`, `V, V₁` and `V', V'₁` be pairs of Hermitian spaces with the same signs. For a split
tame character `𝔠` there are two theta integrals on the adelic unitary group `G E s` of `W`, of data
with real part a vector of the Fock space `PairFock`, a given function at `𝔠.ramifiedPlaces` and the
vacuum at other places. There is a point `γ` of `G E s`, depending on the spaces only, such that for
every `𝔠` the integrals `thetaLarge` for `(W₁, V₁)` and `thetaSmall` for `(W₁, V'₁)` at `g` are, up
to numbers of modulus one, those for `(W, V)` and `(W, V')` at `γ * g`. -/
theorem exists_thetaLarge_thetaSmall_eq_circle_mul (W W₁ : Space E n s) (V V₁ : Space E a t)
    {b : Type} [Fintype b] [DecidableEq b] {t' : b → ℤˣ} (V' V'₁ : Space E b t') :
    ∃ γ : G E s, ∀ {μ : NumberField.InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ),
      (∃ u : Circle, ∀ (v : PairFock E s t) (Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
        (g : G E s),
        thetaLarge W₁ V₁ 𝔠 v Φ g = u * thetaLarge W V 𝔠 v Φ (γ * g)) ∧
      ∃ u' : Circle, ∀ (v' : PairFock E s t') (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ)
        (g : G E s),
        thetaSmall W₁ V'₁ 𝔠 v' Ψ g = u' * thetaSmall W V' 𝔠 v' Ψ (γ * g) := by
  -- Landherr's theorem moves the point of `W` to that of `W₁`; then both integrals are cases of
  -- `exists_circle_thetaIntegral_localDatum_eq_mul`.
  obtain ⟨c, γ, -, hγ, -⟩ := W.exists_x_eq_and_ratEmbed_conj_eq W₁
  refine ⟨γ, fun 𝔠 ↦ ⟨exists_thetaLarge_eq_mul_thetaLarge W₁ W V₁ V c γ hγ 𝔠, ?_⟩⟩
  exact (exists_circle_thetaIntegral_localDatum_eq_mul W₁ W V'₁ V' c γ hγ (rankTwist 𝔠.character n)
    (WeilData.upsilonU1 ^ Fintype.card b) 𝔠.readsAt.star).imp
      fun u' h_move v' Ψ g ↦ h_move v' (fun y ↦ Ψ yᵀ) g

end ChangeOfSpace

/-!
## Descent of the exchange identity along hyperbolic planes

The identity passes from `(W ⊕ H, V ⊕ H, U)` to `(W, V, U)` by taking constant terms along the new
isotropic line. On the side of `U` only the zero vector contributes
(`integral_thetaSmall_lineRadical_eq_mul_thetaSmall`); on the side of `V ⊕ H` the constant term is a
cone integral. Throughout, `New.Exchange.realSlice A U 0` gives the zero term along `A` of real
data.
-/

section RemovingPlanes

open Matrix Fintype Space Splitting Fock MeasureTheory MixedModel

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r r' p b : Type} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r']
  [DecidableEq r'] [Fintype p] [DecidableEq p] [Fintype b] [DecidableEq b] {s : n → ℤˣ}
  {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} {u : b → ℤˣ} {W : Space E n s} {W' : Space E n' s'}

variable (p W) in
/-- Let the signs `t` have the rank and the number of minus signs (`negCount`) of `W` plus `card p`
hyperbolic planes. Then there is a space `W'` with signs `t` and a splitting of `W'` over `W` with
frames indexed by `p` that is adapted (orthonormal at the infinite places, integral at the finite
places). -/
lemma exists_isBaseAdapted (t : r → ℤˣ) (h_rank : card r = card n + 2 * card p)
    (h_neg : negCount t = card p + negCount s) :
    ∃ (W' : Space E r t) (A : W'.Splitting W p), IsBaseAdapted A := by
  -- Relabel `hyperbolicSum p W` along a bijection of index sets that matches the signs.
  obtain ⟨ε, hε⟩ : ∃ ε : r ≃ (p ⊕ p) ⊕ n, (hyperbolicSigns p ⊕ᵥ s) ∘ ε = t :=
    exists_equiv_comp_eq_of_negCount_eq (by simpa +arith)
      (by simpa [negCount_sumElim, negCount_one_and_neg_one])
  let W' : Space E r t := (hyperbolicSum p W).reindex ε.symm hε
  let A : W'.Splitting W p := splittingOfGram (submatrix 1 ε id) (by simp [W']) h_rank
  -- The frame of `A` is that of `removePlanes` with the rows permuted.
  refine ⟨W', A,
    ⟨.of_eq_submatrix_mul .one ε.symm (IsBaseAdapted.isOrthoIntegral (D := removePlanes p W)) ?_⟩⟩
  simp [W', A, ← ext_iff, Matrix.mul_apply, lAdelic, kAdelic, iAdelic, Space.ratMap, removePlanes,
    splittingOfGram, Space.reindex, val_reindexGL_apply, reindex_equiv ε.symm, Matrix.one_apply]

/-- Let `A`, `B` be adapted splittings of `W'` over `W`, and suppose that (`hBA`) the isotropic
frame `B.k` consists of the columns `e` of `A.k` and the inclusions `B.i`, `A.i` of `W` are equal.
Then `A`, `B` have the same zero term (`realSlice` at `0`) on real vectors for `(W', U)`. -/
lemma realSlice_zero_congr (U : Space E b u) (A : W'.Splitting W p) [IsBaseAdapted A]
    {B : W'.Splitting W r} {e : r → p} (hBA : B.k = A.k.submatrix id e ∧ B.i = A.i)
    [IsBaseAdapted B] :
    realSlice A U 0 = realSlice B U 0 := by
  -- The columns of `B.k` are columns of the isotropic frame `A.k`, so `B.k` is orthogonal to `A.k`.
  obtain ⟨h_frame, h_incl⟩ := hBA
  have h_orth : B.kᴴ * W'.J * A.k = 0 := by
    rw [h_frame]
    exact congrArg (·.submatrix e id) A.gram_kk
  simp [realSlice, matrixToVec_zero, ← Pi.zero_def, IsAdapted.mixedModel,
    A.zeroTerm_homSource_congr U h_orth h_incl]

/-- Let `A` split `card p` hyperbolic planes off `W'`, with complement `W`, and let `B` split
`card r` planes off `W`, with complement `V'`, both adapted. For a vector `y` of the Fock space of
`(W', U)`, the zero term along the composite splitting is the zero term along `B` of its zero term
along `A`. -/
lemma realSlice_zero_comp (U : Space E b u) (V' : Space E r' t') (A : W'.Splitting W p)
    (B : W.Splitting V' r) [IsBaseAdapted A] [IsBaseAdapted B] (y : PairFock E s' u) :
    realSlice (A.comp B) U 0 y = realSlice B U 0 (realSlice A U 0 y) := by
  -- Compare the adelic data with these real parts; for adelic data zero terms compose.
  refine eq_of_integrated_zeroTerm_eq (isAdapted_homSource (A.comp B) U) fun f ↦
    (zeroTerm_integrated (isAdapted_homSource (A.comp B) U) y f).symm.trans ?_
  -- The zero term of a datum with the vacuum as real part has the vacuum as real part.
  have h_vac : (A.homSource U).zeroTerm ((W'.hom U).projReal f) =
      (W.hom U).projReal ((A.homSource U).zeroTerm ((W'.hom U).projReal f)) := by
    simpa [slice_vac] using zeroTerm_integrated (isAdapted_homSource A U) Fock.vacVector f
  rw [zeroTerm_homSource_comp, zeroTerm_homSource_comp,
    zeroTerm_integrated (isAdapted_homSource A U), zeroTerm_integrated (isAdapted_homSource B U),
    ← h_vac]
  simp only [realSlice, matrixToVec_zero, Pi.zero_apply, Prod.fst_zero, ← Pi.zero_def]

section OnePlane

omit [WeilData E] in
/-- Let `A` split a hyperbolic plane off `W'`, with complement `W`, and let `dualI` be the matrix of
the projection to `W` in the frame of `A` read at the ramified places `𝔠.ramifiedPlaces` of `𝔠`
(`adaptedFrame`). For an integral matrix `z` at these places the function equal to
`𝔠.semilocalChar⁻¹(det (z dualI wᵀ))` at integral `w` with this determinant a unit, and zero
elsewhere, that is the standard datum of `z dualI` read on transposes, is a Schwartz–Bruhat function
supported on the matrices of full rank. -/
lemma stdColDatum_mul_transpose_mem_schwartzBruhat (A : W'.Splitting W Unit) [IsBaseAdapted A]
    {μ : NumberField.InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ)
    {z : Matrix b n (LocProd 𝔠.ramifiedPlaces)} (hz : IsIntMatrix SemilocalField.O z) :
    (fun w : Matrix b n' (LocProd 𝔠.ramifiedPlaces) ↦
      stdColDatum 𝔠.semilocalChar (z * (adaptedFrame 𝔠.readsAt A).dualI) wᵀ) ∈
      schwartzBruhat {w : Matrix b n' (LocProd 𝔠.ramifiedPlaces) | HasLeftInv wᵀ} :=
  (stdColDatum_mem_schwartzBruhat 𝔠.semilocalChar
    (hz.mul (adaptedFrame 𝔠.readsAt
      A).blockRelations.isIntMatrix_dualI)).transpose_mem_schwartzBruhat

open scoped Classical in
/-- Let `A` split one hyperbolic plane off `W'`, with complement `W`, and let `z` be an integral
matrix at the ramified places of the tame character `𝔠`. Take the datum for `(W', U)` with real part
`y` and the standard datum of `z ∘ pr_W`, read on transposes at the conjugates of these places. Its
slice along `A` at `WeilData.scaleIdele E • x` vanishes unless the finite part of `x` is integral.
In that case it is the nonzero constant `vacuumFactor` of `A`, by which slices multiply the vacuum,
times the datum for `(W, U)` with real part the slice of `y` at `x` and the standard datum of `z`,
read in the same way. -/
lemma homSlice_localDatum_stdColDatum (U : Space E b u) (A : W'.Splitting W Unit)
    [IsBaseAdapted A] {μ : NumberField.InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ)
    (y : PairFock E s' u) {z : Matrix b n (LocProd 𝔠.ramifiedPlaces)}
    (hz : IsIntMatrix SemilocalField.O z) (x : Matrix b Unit (𝔸 E)) :
    A.homSlice U (WeilData.scaleIdele E • x)
        (localDatum W' U y (fun w : Matrix b n' (LocProd 𝔠.ramifiedPlaces) ↦
          stdColDatum 𝔠.semilocalChar (z * (adaptedFrame 𝔠.readsAt A).dualI) wᵀ) 𝔠.readsAt.star) =
      (if IsIntMatrix (Ô E) (x.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))) then
          (vacuumFactor (isAdapted_homSource A U)).val else 0) •
        localDatum W U (realSlice A U x y)
          (fun w : Matrix b n (LocProd 𝔠.ramifiedPlaces) ↦ stdColDatum 𝔠.semilocalChar z wᵀ)
            𝔠.readsAt.star := by
  -- The projection to `W` read at `𝔠.ramifiedPlaces` is the transpose of the inclusion read at the
  -- conjugates.
  have h_frame : (adaptedFrame 𝔠.readsAt A).dualI = (adaptedFrame 𝔠.readsAt.star A).Iᵀ := by
    ext i j w : 3
    simp [adaptedFrame, iCoord, stdForm, evalPlaces_apply, starRingEnd_apply, finAdele_star_apply]
  have h_int {m : Type} (w : Matrix b m (LocProd 𝔠.ramifiedPlaces)) :
      IsIntMatrix SemilocalField.O wᵀ ↔ IsIntMatrix SemilocalField.O w := forall_comm
  -- In the frame of `A` the datum reads only the block of columns along `W`.
  let blockDatum (w : Matrix b (Unit ⊕ n) (LocProd 𝔠.ramifiedPlaces)) : ℂ :=
    invOnUnits 𝔠.semilocalChar (z * w.toCols₂ᵀ).det
  have h_std (w : Matrix b n' (LocProd 𝔠.ramifiedPlaces)) :
      stdColDatum 𝔠.semilocalChar (z * (adaptedFrame 𝔠.readsAt A).dualI) wᵀ =
        (adaptedFrame 𝔠.readsAt.star A).stdDatum blockDatum w := by
    simp only [blockDatum, stdColDatum, IntegralFrame.stdDatum, h_int, h_frame, mul_fromCols,
      toCols₂_fromCols, transpose_mul, Matrix.mul_assoc]
  rw [𝔠.readsAt.star.homSlice_localDatum A U
    (stdColDatum_mul_transpose_mem_schwartzBruhat A 𝔠 hz) x y fun w _ ↦ h_std w]
  simp only [blockDatum, stdColDatum, h_int, toCols₂_fromCols]

/-- Let `X` split a hyperbolic plane off `U`, with complement `U₀`, and let `z` be an integral
matrix at the ramified places of the tame character `𝔠`. The standard datum `stdColDatum χ z`, for
the character `χ = 𝔠.semilocalChar` at these places, sends an integral `w` with `det (z w)` a unit
to `χ⁻¹ (det (z w))` and any other `w` to zero, so it lives on matrices of full rank. Take the datum
for `(W, U)` with real part `v` and this function on transposes, read at the conjugate places
(`𝔠.readsAt.star`), and translate it by `(g, h)` in the Weil representation with characters `α`,
`β`. The theta functional of `Hom(W, U₀)` vanishes on its zero term along the isotropic line `X.k`,
the datum for `(W, U₀)` whose theta function is the mean over adelic translations along this line,
modulo rational ones. -/
lemma theta_zeroTerm_stdColDatum_eq_zero (U : Space E b u) {μ : NumberField.InfinitePlace E → ℤ}
    {m : Type} [Fintype m] [DecidableEq m] {u₀ : m → ℤˣ} {U₀ : Space E m u₀}
    (X : U.Splitting U₀ Unit) (𝔠 : SplitTameChar E μ) {z : Matrix b n (LocProd 𝔠.ramifiedPlaces)}
    (hz : IsIntMatrix SemilocalField.O z) (α β : AutChar E) (g : G E s) (h : G E u)
    (v : PairFock E s u) :
    θ (W.hom U₀) ((X.homTarget W).zeroTerm (pairWeil W U α β (g, h)
      (localDatum W U v (fun w : Matrix b n (LocProd 𝔠.ramifiedPlaces) ↦
        stdColDatum 𝔠.semilocalChar z wᵀ) 𝔠.readsAt.star))) = 0 := by
  -- The functional `ℓ` is invariant under the translations along `x = h⁻¹ X.kAdelic`, so it kills
  -- data supported on matrices that do not annihilate `x`.
  let ℓ : 𝒮 (W.hom U) →L[ℂ] ℂ :=
    θ (W.hom U₀) ∘L (X.homTarget W).zeroTerm ∘L pairWeil W U α β (g, h)
  let x : Matrix b Unit (𝔸 E) := h⁻¹.adeleMatrix * X.kAdelic
  have h_inv (a : Unit × n → 𝔸 E) (f : 𝒮 (W.hom U)) :
      ℓ (ϱ (W.hom U) (shiftMatrix s x 1 *ᵥ a) f) = ℓ f := by
    -- `(g, h)` turns the translation along `x` into one along the isotropic line of `X`.
    let a' := matrixToVec (vecToMatrix a * stdForm E s * g⁻¹.adeleMatrix * W.dualFrame.inv)
    have h_shift : pairWeil W U α β (g, h) (ϱ (W.hom U) (shiftMatrix s x 1 *ᵥ a) f) =
        ϱ (W.hom U) ((X.homTarget W).kAdelic *ᵥ a') (pairWeil W U α β (g, h) f) := by
      simp [x, a', rho_pairWeil, homTarget_kAdelic, kronecker_mulVec_eq_matrixToVec,
        vecToMatrix_matrixToVec, G.adeleMatrix, Matrix.mul_assoc]
    simp only [ℓ, ContinuousLinearMap.comp_apply, h_shift, zeroTerm_rho_kAdelic]
  let π : 𝔸f E →+* LocProd 𝔠.ramifiedPlaces :=
    (evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E))
  let Ψ (w : b × n → 𝔸f E) : ℂ := stdColDatum 𝔠.semilocalChar z ((vecToMatrix w).map π)ᵀ
  have hπ : ReadsAt (star ⁻¹' 𝔠.ramifiedPlaces) π := 𝔠.readsAt.star
  have h_mem : (fun w ↦ stdColDatum 𝔠.semilocalChar z wᵀ) ∈
      schwartzBruhat {w : Matrix b n (LocProd 𝔠.ramifiedPlaces) | HasLeftInv wᵀ} :=
    (stdColDatum_mem_schwartzBruhat 𝔠.semilocalChar hz).transpose_mem_schwartzBruhat
  -- A matrix in the support has full rank, so it does not annihilate `x ≠ 0`.
  have h_supp (w : b × n → 𝔸f E) (hw : Ψ w ≠ 0) :
      (x.map (RingHom.snd _ _))ᴴ *
        (vecToMatrix w * (1 : Matrix n n (𝔸 E)).map (RingHom.snd _ _)) ≠ 0 := by
    obtain ⟨-, -, h_subset⟩ := h_mem
    have h_ne : X.k ≠ 0 := fun h_zero ↦ by simpa [h_zero] using X.gram_lk
    exact U.coordMatrix_mul_ne_zero (by simpa using h_ne) 1 (h_subset hw)
  have h_kill (f : 𝒮 (W.hom U)) :
      ℓ (Space.schrodingerOp (W.hom U) (star ⁻¹' 𝔠.ramifiedPlaces) Ψ f) = 0 :=
    map_schrodingerOp_eq_zero_of_invariant hπ.disjoint_star (hΨ := hπ.isSchwartzBruhat h_mem) x 1
      h_inv
      h_supp f
  -- The datum is `Ψ` at the conjugates of the places `𝔠.ramifiedPlaces`, tensored with `v` and
  -- vacuum elsewhere.
  change ℓ (localDatum W U v (fun w ↦ stdColDatum 𝔠.semilocalChar z wᵀ) hπ) = 0
  simpa [Ψ, localDatum, integrated_schrodingerOp] using h_kill _

/-- One plane, the side of `U`. Let `A` split one hyperbolic plane off `W'`, with complement `W`,
and be adapted. Let `y` be a real Schwartz vector and `z` an integral matrix at the ramified places
of `𝔠`. The constant term along `A`, at the point `(1, g)` of the Levi subgroup, of the theta
integral for `(W', U)` of `y` and the standard datum of `z ∘ pr_W` is the constant `vacuumFactor`
times the theta integral for `(W, U)` of the zero term `realSlice A U 0 y` and the standard datum of
`z`. -/
lemma integral_thetaSmall_lineRadical_eq_mul_thetaSmall (U : Space E b u) (A : W'.Splitting W Unit)
    [IsBaseAdapted A]
    {μ : NumberField.InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ) {y : PairFock E s' u}
    (hy : IsSchwartzVector y) {z : Matrix b n (LocProd 𝔠.ramifiedPlaces)}
    (hz : IsIntMatrix SemilocalField.O z) (g : G E s) :
    ∫ q : Matrix n Unit (𝔸 E) × Matrix Unit Unit (𝔸 E),
      thetaSmall W' U 𝔠 y (stdColDatum 𝔠.semilocalChar (z * (adaptedFrame 𝔠.readsAt A).dualI))
        (lineRadical A q * A.levi (1, g)) ∂radicalMeasure =
      (vacuumFactor (isAdapted_homSource A U)).val *
        thetaSmall W U 𝔠 (realSlice A U 0 y) (stdColDatum 𝔠.semilocalChar z) g := by
  classical
  -- The constant term is a sum over rational vectors `x` of `U`, of which only the isotropic ones
  -- contribute. The term `x = 0` is the right side; the others vanish, since the standard datum
  -- lives on matrices of full rank. Both sides are integrals over `[U(U)]`; compare at `h`.
  let f' : 𝒮 (W'.hom U) := localDatum W' U y
    (fun w ↦ stdColDatum 𝔠.semilocalChar (z * (adaptedFrame 𝔠.readsAt A).dualI) wᵀ) 𝔠.readsAt.star
  simp only [thetaSmall, rankTwist_eq_mul_of_splitting A]
  have h_bounded : IsTargetBounded W' U f' :=
    𝔠.readsAt.star.isTargetBounded hy (stdColDatum_mul_transpose_mem_schwartzBruhat A 𝔠 hz)
  rw [integral_thetaIntegral_lineRadical A _ _ h_bounded, thetaIntegral, ← integral_const_mul]
  congr with h
  let α : AutChar E := rankTwist 𝔠.character n
  let β : AutChar E := WeilData.upsilonU1 ^ card b
  let F : 𝒮 (W'.hom U) := pairWeil W' U (α * WeilData.upsilonU1 ^ card Unit) β (A.levi (1, g), h) f'
  have h_levi (x : Matrix b Unit (𝔸 E)) :
      A.homSlice U x F = pairWeil W U α β (g, h) (A.homSlice U (h⁻¹.adeleMatrix * x) f') := by
    rw [A.homSlice_levi]
    simp
  -- The slices of `f'` are multiples of data for `(W, U)` with the standard datum of `z`.
  have h_slice (x : Matrix b Unit (𝔸 E)) : ∃ (c : ℂ) (v : PairFock E s u), A.homSlice U x f' =
      c • localDatum W U v (fun w ↦ stdColDatum 𝔠.semilocalChar z wᵀ) 𝔠.readsAt.star := by
    rw [← smul_inv_smul (WeilData.scaleIdele E) x]
    exact ⟨_, _, homSlice_localDatum_stdColDatum U A 𝔠 y hz _⟩
  have h_nonzero (x : b → E) (hx : x ≠ 0) : constTermAt A (replicateCol Unit x) F = 0 := by
    -- `constTermAt` is zero by definition at an anisotropic vector.
    by_cases! h_iso : (replicateCol Unit x)ᴴ * U.J * replicateCol Unit x ≠ 0
    · exact ite_eq_right h_iso
    -- An isotropic `x` is the frame of a splitting `X` of `U`.
    obtain ⟨m, s₀, U₀, X, hX⟩ := exists_splitting U (.of_ne_zero hx) h_iso
    have h_term : constTermAt A X.k F =
        θ (W.hom U₀) ((X.homTarget W).zeroTerm (A.homSlice U X.kAdelic F)) := by
      simpa [lineTerm] using constTermAt_smul_k A X one_ne_zero (f := F)
    obtain ⟨c, v, h_eq⟩ := h_slice (h⁻¹.adeleMatrix * X.kAdelic)
    simp only [← hX, h_term, h_levi, h_eq, map_smul, theta_zeroTerm_stdColDatum_eq_zero U X 𝔠 hz,
      smul_zero]
  refine (tsum_eq_single 0 h_nonzero).trans ?_
  have h_zero : A.homSlice U 0 f' = (vacuumFactor (isAdapted_homSource A U)).val •
      localDatum W U (realSlice A U 0 y) (fun w ↦ stdColDatum 𝔠.semilocalChar z wᵀ)
        𝔠.readsAt.star := by
    simpa [f', IsIntMatrix] using homSlice_localDatum_stdColDatum U A 𝔠 y hz 0
  rw [replicateCol_zero, constTermAt_zero, h_levi, Matrix.mul_zero, h_zero]
  simp [α, β, pairTheta]

/-- The exchange identity `RowColExchangeIdentity W V U μ σ x y ℓ` says that `x`, `y` are Schwartz
vectors of the Fock spaces of `(W, V)`, `(W, U)` and that there is a real `D` such that, for every
tame character `𝔠` of `[U(1)]` of weight `μ`, the theta integral of `(W, V)` at `x` is `c` times
that of `(W, U)` at `y` on standard data (rows ordered by the bijection `σ`), where
`D |c| ^ 2 = L(rk V - rk W / 2) ℓ(𝔠)` and `L = lValueProdInt 𝔠` is a product of `L`-values of `𝔠`.
It depends on `V` only through its signs: the theta integrals of two spaces `V`, `V₁` with the same
signs differ by a factor of modulus one. -/
lemma RowColExchangeIdentity.congr_second_space (U : Space E b u)
    {μ : NumberField.InfinitePlace E → ℤ}
    {ℓ : SplitTameChar E μ → ℝ} {V : Space E r t} (V₁ : Space E r t) {σ : b ⊕ r ≃ n}
    {x : PairFock E s t} {y : PairFock E s u} (h_rel : RowColExchangeIdentity W V U μ σ x y ℓ) :
    RowColExchangeIdentity W V₁ U μ σ x y ℓ := by
  obtain ⟨hx, hy, D, h_rel⟩ := h_rel
  refine ⟨hx, hy, D, fun 𝔠 ↦ ?_⟩
  obtain ⟨a, h_move⟩ : ∃ a : Circle, ∀ (v : PairFock E s t)
      (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ) (g : G E s),
      thetaLarge W V₁ 𝔠 v Φ g = a * thetaLarge W V 𝔠 v Φ g := by
    simpa using exists_thetaLarge_eq_mul_thetaLarge W W V₁ V 1 1 (by simp) 𝔠
  -- The factor `c` for `V` is replaced by `a * c`, which has the same modulus.
  obtain ⟨c, h_norm, h_eq⟩ := h_rel 𝔠
  refine ⟨a * c, by simpa [Circle.norm_coe] using h_norm, fun z hz ↦ funext fun g ↦ ?_⟩
  simp [h_move, h_eq z hz, mul_assoc]

/-- The exchange identity `RowColExchangeIdentity W V U μ σ x y ℓ` says: for every split tame
character `𝔠` of `[U(1)]` of weight `μ`, the theta integral `thetaLarge` of `(W, V)` at the Fock
vector `x` is `c` times the theta integral of `(W, U)` at `y` on standard data, with
`D |c| ^ 2 = L(rk V - rk W / 2) ℓ(𝔠)` for a `D` independent of `𝔠` and the product of `L`-values
`L = lValueProdInt 𝔠`. The standard datum `stdRowDatum σ χ w` is `χ⁻¹ ∘ det` of the matrix with the
rows of `w` and of the argument, ordered by `σ`, where that matrix is integrally invertible over the
product `LocProd` of the completions at the ramified places, and zero elsewhere.

Let `A` and `X` be splittings `W' = W ⊕ H` and `V' = V ⊕ H`, where `H` is a hyperbolic plane, both
adapted (frames orthonormal at infinite, integral at finite places). Suppose that for every `𝔠` the
constant term along `A` of the theta integral of `(W', V')` (`planeConstantTerm`) is `γ ≠ 0` times
the theta integral of `(W, V)` at the cone integral of `x` with exponent `z > 0` on the side `β` of
Poisson's formula (the integral of `coneIntegrand` over the maximal compact subgroup for `V'` and
the torus at the infinite places: `β = true` gives `cone`, `β = false` gives `dualCone`), where
`|γ| ^ 2 L(e) = C L(e + 1)` for `e = rk V - rk W / 2`. The constant term is formed from the standard
datum of `w dualI` (`dualI` is the projection to `W`) at `(1, g)`, the other side from that of `w`
at `g`, for integral matrices `w` and adelic unitary `g`. Then the identity for `(W', V', U)` at
`x`, `y` gives the identity for `(W, V, U)`, with the same `ℓ`, at the cone integral of `x` and the
zero term `realSlice A U 0 y`, the value of `y` at `0` in the mixed model of `A`. -/
lemma RowColExchangeIdentity.of_planeConstantTerm_eq (U : Space E b u) {V' : Space E r' t'}
    (A : W'.Splitting W Unit) [IsBaseAdapted A] {μ : NumberField.InfinitePlace E → ℤ}
    {ℓ : SplitTameChar E μ → ℝ} {V : Space E r t}
    (X : V'.Splitting V Unit) [IsBaseAdapted X] (σ : b ⊕ r ≃ n) {σ' : b ⊕ r' ≃ n'} {β : Bool}
    {z : ℝ} (hz_pos : 0 < z) {C : ℝ} {x : PairFock E s' t'} {y : PairFock E s' u}
    (h_term : ∀ 𝔠 : SplitTameChar E μ, ∃ γ ≠ (0 : ℂ),
      ‖γ‖ ^ 2 * lValueProdInt 𝔠 (card r - card n / 2) =
        C * lValueProdInt 𝔠 (card r - card n / 2 + 1) ∧
      ∀ w : Matrix b n (LocProd 𝔠.ramifiedPlaces), IsIntMatrix SemilocalField.O w → ∀ g : G E s,
        planeConstantTerm 𝔠 V' A σ' x w 1 g =
          γ * thetaLarge W V 𝔠
            (∫ q : maxCompact E t' × (NumberField.InfinitePlace E → ℂ)ˣ,
              coneIntegrand A X μ β z x q ∂.prod .haar .haar)
            (stdRowDatum σ 𝔠.semilocalChar w) g)
    (h_rel : RowColExchangeIdentity W' V' U μ σ' x y ℓ) :
    RowColExchangeIdentity W V U μ σ
      (∫ q : maxCompact E t' × (NumberField.InfinitePlace E → ℂ)ˣ,
        coneIntegrand A X μ β z x q ∂.prod .haar .haar)
      (realSlice A U 0 y) ℓ := by
  obtain ⟨hx, hy, D, h_rel⟩ := h_rel
  let κ : ℂˣ := vacuumFactor (isAdapted_homSource A U)
  refine ⟨isSchwartzVector_integral_coneIntegrand A X μ β hz_pos hx,
    isSchwartzVector_slice _ _ hy, D * C / ‖κ.val‖ ^ 2, fun 𝔠 ↦ ?_⟩
  obtain ⟨γ, hγ_ne, hγ, h_const⟩ := h_term 𝔠
  obtain ⟨c, hc : D * ‖c‖ ^ 2 = lValueProdInt 𝔠 (card r' - card n' / 2) * ℓ 𝔠, h_eq⟩ := h_rel 𝔠
  refine ⟨c * κ / γ, ?_, fun w hw ↦ funext fun g ↦ mul_left_cancel₀ hγ_ne ?_⟩
  · have h_rank : (card r' - card n' / 2 : ℤ) = card r - card n / 2 + 1 := by
      grind [A.card_eq, X.card_eq, card_unit]
    calc D * C / ‖κ.val‖ ^ 2 * ‖c * κ / γ‖ ^ 2 = C * (D * ‖c‖ ^ 2) / ‖γ‖ ^ 2 := by simp [field]
      _ = C * lValueProdInt 𝔠 (card r - card n / 2 + 1) * ℓ 𝔠 / ‖γ‖ ^ 2 := by
          rw [hc, h_rank, mul_assoc]
      _ = lValueProdInt 𝔠 (card r - card n / 2) * ℓ 𝔠 := by
          rw [← hγ]
          field
  · -- Take constant terms along `A` of the identity for `(W', V', U)`.
    rw [← h_const w hw g]
    calc planeConstantTerm 𝔠 V' A σ' x w 1 g
      _ = c * ∫ q, thetaSmall W' U 𝔠 y
          (stdColDatum 𝔠.semilocalChar (w * (adaptedFrame 𝔠.readsAt A).dualI))
          (lineRadical A q * A.levi (1, g)) ∂radicalMeasure := by
        simp only [planeConstantTerm, Pi.smul_apply, smul_eq_mul, integral_const_mul, map_one,
          h_eq _ (hw.mul (adaptedFrame 𝔠.readsAt A).blockRelations.isIntMatrix_dualI)]
      _ = c * (κ * thetaSmall W U 𝔠 (realSlice A U 0 y) (stdColDatum 𝔠.semilocalChar w) g) := by
        rw [integral_thetaSmall_lineRadical_eq_mul_thetaSmall U A 𝔠 hy hw]
      _ = γ * ((c * κ / γ) •
          thetaSmall W U 𝔠 (realSlice A U 0 y) (stdColDatum 𝔠.semilocalChar w)) g := by
        rw [Pi.smul_apply, smul_eq_mul]
        field

/-- Removing a plane by the cone integral. Let `W` have even rank, let `A` and `X` be splittings
`W' = W ⊕ H` and `V' = V ⊕ H` with a hyperbolic plane `H`, both adapted, and let
`rk V - rk W / 2 = z` be a natural number. The identity for `(W', V', U)` at `x`, `y` gives the
identity for `(W, V, U)`, with the same `ℓ`, at the cone integral of `x` with exponent `z + 1` and
the zero term of `y`, its value at `0` in the mixed model of `A`. -/
theorem RowColExchangeIdentity.cone (U : Space E b u) {V' : Space E r' t'} (A : W'.Splitting W Unit)
    [IsBaseAdapted A] {μ : NumberField.InfinitePlace E → ℤ} {ℓ : SplitTameChar E μ → ℝ}
    {V : Space E r t} (X : V'.Splitting V Unit) [IsBaseAdapted X] (σ : b ⊕ r ≃ n)
    {σ' : b ⊕ r' ≃ n'} (hn_even : 2 ∣ card n) {z : ℕ} (h_rank : (card r - card n / 2 : ℤ) = z)
    {x : PairFock E s' t'} {y : PairFock E s' u}
    (h_rel : RowColExchangeIdentity W' V' U μ σ' x y ℓ) :
    RowColExchangeIdentity W V U μ σ (cone A X μ (z + 1) x) (realSlice A U 0 y) ℓ := by
  obtain ⟨C, hC_pos, h_plane⟩ :=
    exists_planeConstantTerm_eq_thetaLarge_cone A X σ' σ hn_even μ h_rank
  -- `cone` is the integral of `coneIntegrand` on the side `β = true`.
  unfold Exchange.cone
  refine h_rel.of_planeConstantTerm_eq U A X σ (β := true) (by positivity) (C := C ^ 2) fun 𝔠 ↦ ?_
  obtain ⟨γ, hγ : ‖γ‖ = C * lSharp 𝔠 (z + 1), h_term⟩ := h_plane 𝔠
  have h_const (w : Matrix b n (LocProd 𝔠.ramifiedPlaces)) (hw : IsIntMatrix SemilocalField.O w)
      (g : G E s) :
      planeConstantTerm 𝔠 V' A σ' x w 1 g =
        γ * thetaLarge W V 𝔠 (Exchange.cone A X μ (z + 1) x) (stdRowDatum σ 𝔠.semilocalChar w) g :=
    h_term x h_rel.left w hw 1 g (.inl rfl)
  have hγ_pos : 0 < ‖γ‖ := (mul_pos hC_pos (lSharp_pos 𝔠 (by simp))).trans_eq hγ.symm
  refine ⟨γ, norm_pos_iff.1 hγ_pos, ?_, h_const⟩
  rw [h_rank, hγ, lValueProdInt_succ]
  ring

/-- Removing a plane by the cone integral on the other side of Poisson's formula. Let `W` have even
rank, let `A`, `X` be splittings `W' = W ⊕ H`, `V' = V ⊕ H` with a hyperbolic plane `H`, both
adapted, and let `rk V - rk W / 2 = -z - 1 < 0`. The identity for `(W', V', U)` at `x`, `y` gives
the identity for `(W, V, U)`, with the same `ℓ`, at `dualCone A X μ (z + 1) x` and the zero term
`realSlice A U 0 y` of `y`, its value at `0` in the mixed model of `A`. -/
theorem RowColExchangeIdentity.dualCone (U : Space E b u) {V' : Space E r' t'}
    (A : W'.Splitting W Unit) [IsBaseAdapted A] {μ : NumberField.InfinitePlace E → ℤ}
    {ℓ : SplitTameChar E μ → ℝ} {V : Space E r t} (X : V'.Splitting V Unit) [IsBaseAdapted X]
    (σ : b ⊕ r ≃ n) {σ' : b ⊕ r' ≃ n'} (hn_even : 2 ∣ card n) {z : ℕ}
    (h_rank : (card r - card n / 2 : ℤ) = -(z + 1)) {x : PairFock E s' t'} {y : PairFock E s' u}
    (h_rel : RowColExchangeIdentity W' V' U μ σ' x y ℓ) :
    RowColExchangeIdentity W V U μ σ (dualCone A X μ (z + 1) x) (realSlice A U 0 y) ℓ := by
  obtain ⟨C, hC_pos, h_plane⟩ :=
    exists_planeConstantTerm_eq_thetaLarge_dualCone A X σ' σ hn_even μ h_rank
  -- `dualCone` is the integral of `coneIntegrand` on the side `β = false`.
  refine h_rel.of_planeConstantTerm_eq U A X σ (β := false) (by positivity) (C := C ^ 2) fun 𝔠 ↦ ?_
  obtain ⟨γ, hγ : ‖γ‖ = C * lSharp 𝔠 (z + 1), h_term⟩ := h_plane 𝔠
  have h_const (w : Matrix b n (LocProd 𝔠.ramifiedPlaces)) (hw : IsIntMatrix SemilocalField.O w)
      (g : G E s) :
      planeConstantTerm 𝔠 V' A σ' x w 1 g =
        γ * thetaLarge W V 𝔠 (Exchange.dualCone A X μ (z + 1) x) (stdRowDatum σ 𝔠.semilocalChar w)
          g :=
    h_term x h_rel.left w hw 1 g (.inl rfl)
  have hγ_pos : 0 < ‖γ‖ := (mul_pos hC_pos (lSharp_pos 𝔠 (by simp))).trans_eq hγ.symm
  refine ⟨γ, norm_pos_iff.1 hγ_pos, ?_, h_const⟩
  have h_ratio : ‖γ‖ ^ 2 * lValueProdInt 𝔠 (-(z + 1)) = C ^ 2 * lValueProdInt 𝔠 (-z) := by
    rw [hγ, lValueProdInt_neg]
    ring
  simpa [h_rank] using h_ratio

/-- Removing a plane. Let `W` have even rank, let `A` be a splitting `W' = W ⊕ H` with a hyperbolic
plane `H` that is adapted, let `V'` have one negative sign more than `V`, and let the bijections
`σ`, `σ'`, which order the rows of the data, say that `rk U + rk V = rk W` and
`rk U + rk V' = rk W'`. The identity for `(W', V', U)` at `x`, `y` gives the identity for
`(W, V, U)`, with the same `ℓ`, at some `x₀` and the zero term of `y`, its value at `0` in the mixed
model of `A`. -/
lemma exists_rowColExchangeIdentity_removing_plane (U : Space E b u) (V' : Space E r' t')
    (A : W'.Splitting W Unit) [IsBaseAdapted A] {μ : NumberField.InfinitePlace E → ℤ}
    {ℓ : SplitTameChar E μ → ℝ} (V : Space E r t) (σ : b ⊕ r ≃ n) {σ' : b ⊕ r' ≃ n'}
    (h_negCount : negCount t' = 1 + negCount t) (hn_even : 2 ∣ card n) {x : PairFock E s' t'}
    {y : PairFock E s' u} (h_rel : RowColExchangeIdentity W' V' U μ σ' x y ℓ) :
    ∃ x₀ : PairFock E s t, RowColExchangeIdentity W V U μ σ x₀ (realSlice A U 0 y) ℓ := by
  -- Replace `V'` by a space `V₁` with the same signs that splits over `V`.
  have h_card : card r' = card r + 2 * card Unit := by
    grind [A.card_eq, card_congr σ, card_congr σ', card_sum]
  obtain ⟨V₁, X, _⟩ := exists_isBaseAdapted Unit V t' h_card (by simp [h_negCount])
  -- The sign of `rk V - rk W / 2` decides on which side of Poisson's formula the cone is formed.
  obtain ⟨z, hz | hz⟩ : ∃ z : ℕ,
      (card r - card n / 2 : ℤ) = z ∨ (card r - card n / 2 : ℤ) = -(z + 1) := by
    cases (card r - card n / 2 : ℤ) <;> simp [Int.negSucc_eq]
  · exact ⟨_, (h_rel.congr_second_space U V₁).cone U A X σ hn_even hz⟩
  · exact ⟨_, (h_rel.congr_second_space U V₁).dualCone U A X σ hn_even hz⟩

end OnePlane

/-- Removing `card p ≥ 1` planes. Let `W` have even rank, let `A` split `W'` as `W` plus `card p`
hyperbolic planes and be adapted, let `V'` have `card p` more negative signs than `V`, and let the
bijections `σ`, `σ'`, which order the rows of the data, say that `rk U + rk V = rk W` and
`rk U + rk V' = rk W'`. The identity for `(W', V', U)` at `x`, `y` gives the identity for
`(W, V, U)`, with the same `ℓ`, at some `x₀` and the zero term `realSlice A U 0 y` of `y`, its value
at `0` in the mixed model of `A`. -/
lemma exists_rowColExchangeIdentity_removing_planes (U : Space E b u) (V' : Space E r' t')
    (A : W'.Splitting W p) [IsBaseAdapted A] [Nonempty p] {μ : NumberField.InfinitePlace E → ℤ}
    {ℓ : SplitTameChar E μ → ℝ} (V : Space E r t) (σ : b ⊕ r ≃ n) {σ' : b ⊕ r' ≃ n'}
    (h_negCount : negCount t' = card p + negCount t) (hn_even : 2 ∣ card n) {x : PairFock E s' t'}
    {y : PairFock E s' u} (h_rel : RowColExchangeIdentity W' V' U μ σ' x y ℓ) :
    ∃ x₀ : PairFock E s t, RowColExchangeIdentity W V U μ σ x₀ (realSlice A U 0 y) ℓ := by
  -- Strong induction on the number of planes.
  induction' hd : card p using Nat.strongRec with d ih generalizing p n n' r r'
  obtain _ | _ | d := d
  · cases card_ne_zero hd
  · -- One plane: index it by `Unit`.
    let e : Unit ≃ p := equivOfCardEq (by simp [hd])
    obtain ⟨B, _, hBA⟩ := exists_isBaseAdapted_reindex A e
    rw [realSlice_zero_congr U A hBA]
    exact exists_rowColExchangeIdentity_removing_plane U V' B V σ (by simp [h_negCount, hd]) hn_even
      h_rel
  · -- `B` removes `d + 1` planes, down to `W` plus one plane; `removePlanes` removes the last one.
    let e : Fin (d + 1) ⊕ Fin 1 ≃ p := finSumFinEquiv.trans (equivFinOfCardEq hd).symm
    obtain ⟨B, _, hBA⟩ : ∃ B : W'.Splitting (hyperbolicSum (Fin 1) W) (Fin (d + 1)),
        IsBaseAdapted B ∧ (B.comp (removePlanes (Fin 1) W)).k = A.k.submatrix id e ∧
          (B.comp (removePlanes (Fin 1) W)).i = A.i :=
      exists_isBaseAdapted_comp_removePlanes A e
    -- The partner of `W` plus one plane is `Y`, the space `V` plus one plane.
    let Y := hyperbolicSum (Fin 1) V
    let τ : b ⊕ (Fin 1 ⊕ Fin 1) ⊕ r ≃ (Fin 1 ⊕ Fin 1) ⊕ n :=
      equivOfCardEq (by simp +arith [← card_congr σ])
    have h_neg : negCount (hyperbolicSigns (Fin 1) ⊕ᵥ t) = card (Fin 1) + negCount t := by
      simp [negCount_sumElim, negCount_one_and_neg_one]
    obtain ⟨x₁, h_above⟩ : ∃ x₁ : PairFock E (hyperbolicSigns (Fin 1) ⊕ᵥ s)
      (hyperbolicSigns (Fin 1) ⊕ᵥ t),
        RowColExchangeIdentity (hyperbolicSum (Fin 1) W) Y U μ τ x₁ (realSlice B U 0 y) ℓ :=
      ih (d + 1) (by simp) V' B Y τ (by simp +arith [h_negCount, hd, h_neg])
        (by simpa using hn_even.add (dvd_refl 2)) h_rel
        (card_fin _)
    rw [realSlice_zero_congr U A hBA, realSlice_zero_comp]
    exact ih 1 (by simp) Y (removePlanes (Fin 1) W) V σ h_neg hn_even h_above (card_fin _)

end RemovingPlanes

end New.Exchange
