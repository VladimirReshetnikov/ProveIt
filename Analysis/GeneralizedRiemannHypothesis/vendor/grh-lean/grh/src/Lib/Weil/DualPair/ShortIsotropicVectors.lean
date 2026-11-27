import Lib.Adelic.Reduction.FirstMinimumShortBases
import Lib.Weil.DualPair.Defs

/-!
# Short isotropic vectors and means of theta functionals over isotropic subspaces

This file prepares the rapid decay of theta kernels under a support condition on Ψ, on the data
space of Hom(S, T), which carries the representation `New.pairWeil`. The datum v ⊗ Ψ ⊗ f₀ is
`integrated _ v (schrodingerOp _ P Ψ f₀)`, with v in Fock space, Ψ Schwartz–Bruhat above a set P
of finite places disjoint from its conjugate (`New.IsSchwartzBruhat`), and f₀ in the finite part
`New.Space.finitePart`. The argument is the one for cusp forms. At a point of large height the
lattice has a short isotropic vector, and θ is invariant under the rational maps of rank one
through it. The mean over the adelic maps of this kind vanishes by the support condition on Ψ
(`New.map_schrodingerOp_eq_zero_of_invariant`), and θ is close to this mean because the maps are
short (`New.Space.exists_norm_sub_subspaceMean_le`).

## Main definitions and results

* `New.Space.exists_short_isotropic`: If the height of `g` exceeds `2`, then the lattice of `S` at
  `g` contains a nonzero isotropic vector, written as a matrix with one column, of length at most
  `2 / height g` (`latticeBall`).
* `New.Space.exists_norm_sub_subspaceMean_le`: for vectors `z i` of the lattice at `g` of lengths
  at most `δ` spanning an isotropic subspace `Z`, a bounded functional invariant under the
  Heisenberg operators of `Z` is close, on data with finite part `f₀`, to its mean
  `New.Space.subspaceMean` over the adelic points of `Z` modulo the rational ones.

Notions from other files:
* `New.G`: The adelic unitary group G = G_∞ × G_f for signs s at the infinite places and the
  identity matrix at the finite places.
* `New.Space`: A hermitian space with a point: a matrix J over E and x in GL_n(𝔸) with xᴴJx equal to
  diag(s) at the infinite places and 1 at the finite places; Γ = x⁻¹U(J)(E)x.

## Relation to the literature

Known; see `Lib.Weil.DualPair.KernelDecay` for sources.
-/

noncomputable section

namespace New

section KernelDecay

open MeasureTheory Matrix Kronecker
  Fock WeilData Space Prod G IsDualFamily Heisenberg ENNReal

variable {E : Type} [Field E] [CMType E] {n n' p q : Type} [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s')
  (a b : AutChar E) (g : G E s) (c : Matrix n q E)

/-! ### Rational matrices in adelic coordinates, short vectors -/

/-- The coordinates at an adelic point `g` of a matrix `c` over `E`: the adelic matrix `g⁻¹ x⁻¹ c`,
where `x = S.x` carries the form of `S` to the standard form. -/
noncomputable def Space.coordMatrix : Matrix n q (𝔸 E) :=
  g⁻¹.adeleMatrix * (S.x⁻¹.val * c.map toAdele)

variable {g c} {R : Type*} [CommRing R] [Nontrivial R] {φ : 𝔸f E →+* R} [Fintype p] [DecidableEq p]

/-- Let `c ≠ 0` be a matrix over `E` with coordinates `c'` at `g`, let `X` be an invertible adelic
matrix, and let `M` be a finite adelic matrix that has a left inverse after a ring map `φ` from the
finite adeles to a nonzero ring. Then the product of the finite part of `Xᴴ`, of `M` and of the
finite part of `c'` is not zero. -/
lemma Space.mul_coordMatrix_ne_zero (hc : c ≠ 0) (X : GL p (𝔸 E)) {M : Matrix p n (𝔸f E)}
    (hM : HasLeftInv (M.map φ)) :
    (X.val.map snd)ᴴ * (M * (S.coordMatrix g c).map snd) ≠ 0 := by
  -- Apply `φ`. Then `Xᴴ`, `M` and the inverse of `S.x * g` all have left inverses and cancel, and
  -- what is left is the image of `c` under an injective map out of the field `E`.
  obtain ⟨L, hL⟩ : ∃ L : Matrix n p R, L * M.map φ = 1 := hM
  intro h_zero
  let ψ : 𝔸 E →+* R := φ.comp (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))
  let u : GL n R := (S.x * g.toUnitary.val).map ψ
  let Y : GL p R := (star X).map ψ
  let c' : Matrix n q R := c.map (ψ.comp toAdele)
  have h_coord : ((S.coordMatrix g c).map snd).map φ = u⁻¹.val * c' := by
    change (S.coordMatrix g c).map ψ = (S.x * g.toUnitary.val)⁻¹.val.map ψ * (c.map toAdele).map ψ
    rw [← Matrix.map_mul, coordMatrix, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
    rfl
  have h_star : (X.val.map snd)ᴴ.map φ = Y.val := rfl
  have h_map : Y.val * (M.map φ * (u⁻¹.val * c')) = 0 := by
    rw [← h_coord, ← h_star, ← Matrix.map_mul, ← Matrix.map_mul, h_zero,
      Matrix.map_zero _ φ.map_zero]
  have h_c : c' = 0 :=
    calc c' = u.val * (L * (Y⁻¹.val * (Y.val * (M.map φ * (u⁻¹.val * c'))))) := by
          simp only [← Matrix.mul_assoc Y⁻¹.val, ← Matrix.mul_assoc L, ← Matrix.mul_assoc u.val,
            Units.inv_mul, Units.mul_inv, hL, Matrix.one_mul]
      _ = 0 := by simp only [h_map, Matrix.mul_zero]
  exact hc (map_injective (ψ.comp toAdele).injective (by simpa [c'] using h_c))

/-- Let `c ≠ 0` be a matrix over `E` with coordinates `c'` at `g`, let `X` be an invertible adelic
matrix, and let `M` be a finite adelic matrix that has a right inverse after a ring map `φ` from the
finite adeles to a nonzero ring. Then the product of the finite part of `c'ᴴ`, of `M` and of the
finite part of `X` is not zero. -/
lemma Space.coordMatrix_mul_ne_zero (hc : c ≠ 0) (X : GL p (𝔸 E)) {M : Matrix n p (𝔸f E)}
    (hM : HasLeftInv (M.map φ)ᵀ) :
    ((S.coordMatrix g c).map snd)ᴴ * (M * X.val.map snd) ≠ 0 := by
  -- The conjugate transpose of `mul_coordMatrix_ne_zero`, for `φ` composed with conjugation.
  have hM' : HasLeftInv (Mᴴ.map (φ.comp starRingAut.toRingHom)) := by
    simpa [conjTranspose, Function.comp_def, transpose_map] using hM
  have h_ne : ((X.val.map snd)ᴴ * (Mᴴ * (S.coordMatrix g c).map snd))ᴴ ≠ 0 :=
    conjTranspose_eq_zero.ne.2 (S.mul_coordMatrix_ne_zero hc X hM')
  simpa [Matrix.mul_assoc] using h_ne

/-- If the height of `g` exceeds `2`, then the lattice of `S` at `g` contains a nonzero isotropic
vector, written as a matrix with one column, of length at most `2 / height g` (`latticeBall`). -/
lemma Space.exists_short_isotropic (h_ht : 2 < S.height g) :
    ∃ x : Matrix n Unit E, x ≠ 0 ∧ xᴴ * S.J * x = 0 ∧
      ∀ j : Unit, x.col j ∈ (S.move g).latticeBall (2 / S.height g) := by
  have h_pos : 0 < (S.move g).firstMinimum := (S.move g).firstMinimum_pos
  have h_small : 2 * (S.move g).firstMinimum < 1 := by simpa [height, field] using h_ht
  -- `2 * firstMinimum` is below the cut-off `1` and exceeds `firstMinimum`, so it is not a lower
  -- bound for the lengths of the nonzero lattice vectors.
  obtain ⟨x, hx, hx_ne, hx_short⟩ : ∃ x ∈ (S.move g).baseLattice,
      x ≠ 0 ∧ ‖(S.move g).archCoords x‖ < 2 * (S.move g).firstMinimum := by
    simpa [le_firstMinimum_iff, h_small.le] using (lt_two_mul_self h_pos).not_ge
  -- A lattice vector of length less than `1` is isotropic.
  have hx_iso : star x ⬝ᵥ S.J *ᵥ x = 0 :=
    (S.move g).form_eq_zero_of_norm_mul_lt_one hx hx (by simp [← sq, hx_short.trans h_small])
  have hx_le : ‖(S.move g).archCoords x‖ ≤ 2 / S.height g :=
    hx_short.le.trans_eq (by simp [height])
  have h_gram : (replicateCol Unit x)ᴴ * S.J * replicateCol Unit x = 0 :=
    Matrix.ext fun _ _ ↦ (dotProduct_mulVec (star x) S.J x).symm.trans hx_iso
  exact ⟨replicateCol Unit x, by simpa using hx_ne, h_gram, fun _ ↦ ⟨hx, hx_le⟩⟩

variable [WeilData E] [Fintype q] {S T}

/-- The function x ↦ θ(ϱ(x)f) has the same value at a rational vector as at 0. -/
@[simp]
lemma apply_vecAtPoint (f : 𝒮 S) (γ : n → E) : f (S.vecAtPoint γ) = f 0 := by
  simp [← S.apply_vecAtPoint_add f γ 0]

/-! ### Supports -/

/-- Let `Ψ` be Schwartz–Bruhat above a set `P` of finite places disjoint from its conjugate, `I` a
submodule of the adelic vectors of `V`, and `A` a bounded linear map on `𝒮 V` that is invariant
under the Heisenberg operators `ϱ z` for `z` in `I`. If no `y` with `Ψ y ≠ 0` is orthogonal to the
finite part of `I`, then `A` kills `Ψ ⊗ f` (`schrodingerOp`). -/
theorem Space.map_eq_zero_of_support_not_orthogonal {E n X : Type*} [Field E] [CMType E]
    [WeilData E] [Fintype n] [DecidableEq n] [NormedAddCommGroup X] [NormedSpace ℂ X] {s : n → ℤˣ}
    {V : Space E n s} {P : Set (FinPlace E)} (hP : Set.IsConjDisjoint P)
    {Ψ : (n → 𝔸f E) → ℂ} [hΨ : IsSchwartzBruhat P Ψ] (I : Submodule (𝔸 E) (n → 𝔸 E))
    {A : 𝒮 V →L[ℂ] X} (hA : ∀ z ∈ I, ∀ f : 𝒮 V, A (V.ϱ z f) = A f)
    (h_supp : ∀ y : n → 𝔸f E, Ψ y ≠ 0 → ∃ z ∈ I, star (fun k : n ↦ (z k).2) ⬝ᵥ y ≠ 0)
    (f : 𝒮 V) : A (V.schrodingerOp P Ψ f) = 0 := by
  classical
  -- It is enough to kill the indicators of small cosets near a point `y` of the support. Some
  -- `ϱ z`, with `z` in `I` above the conjugate of `P`, multiplies them by a constant other than
  -- `1`, while `A` is invariant under it.
  refine hΨ.mem_of_cosets ((A ∘L .apply ℂ _ f).ker.comap (V.schrodingerOp P)) fun y hy ↦ ?_
  obtain ⟨z, hz, h_ne⟩ := h_supp y hy
  let u (k : n) : 𝔸f E := (z k).2
  -- By self-duality of `Ô E`, the character is not trivial on the multiples of `u* y`.
  let χ (c : 𝔸f E) (x : n → 𝔸f E) : ℂ := stdLattice.selfDualAddChar E (star (c • u) ⬝ᵥ x)
  obtain ⟨c, hc⟩ : ∃ c : 𝔸f E, χ c y ≠ 1 := by
    by_contra! h_one
    refine h_ne <| eq_zero_of_forall_mul_integral fun a ↦
      (stdLattice.forall_selfDualAddChar_mul_eq_one_iff _).1 fun b _ ↦ ?_
    simpa [χ, mul_right_comm] using h_one (star (a * b))
  -- The part of `c • u` above the conjugate of `P` comes from a multiple of `z`.
  have h_inv (F : 𝒮 V) : A (V.ϱ (finVec (idem P.conjClosure • star (idem P) • c • u)) F) = A F := by
    let a : 𝔸 E := (0, α.val * idem P.conjClosure * star (idem P) * c)
    have h_vec : finVec (idem P.conjClosure • star (idem P) • c • u) = a • z := by
      ext1 k
      ext1 <;> simp [a, u, finVec, mul_assoc]
    rw [h_vec, hA _ (I.smul_mem a hz)]
  -- The neighbourhood of `y` is where the locally constant multiplier keeps its value.
  refine ⟨{x : n → 𝔸f E | χ c x = χ c y},
    (isLocallyConstant_selfDualAddChar.comp_continuous (by fun_prop)).eventually_eq y,
      fun t w _ h_coset ↦ ?_⟩
  have h_const : (fun x : n → 𝔸f E ↦ χ c (idem P • x) * cosetIndicator P t w x) =
      χ c y • cosetIndicator P t w :=
    funext fun x ↦ mul_eq_mul_right_iff.2 (or_not.imp (h_coset x) fun hx ↦ ite_eq_right hx)
  -- That operator multiplies the function in `schrodingerOp` by the character above.
  let F : 𝒮 V := V.schrodingerOp P (cosetIndicator P t w) f
  have h_eigen : χ c y • A F = A F := by
    nth_rw 2 [← h_inv]
    rw [rho_schrodingerOp hP, IsSchwartzBruhat.schrodingerAct_star_idem_smul hP, h_const]
    simp [F]
  have h_sub : (χ c y - 1) • A F = 0 := by rw [sub_smul, h_eigen, one_smul, sub_self]
  exact (smul_eq_zero_iff_right (sub_ne_zero.2 hc)).1 h_sub

section Supports

variable {S : Space E n s} {T : Space E n' s'}

/-- The matrix of the map `z ↦ X z Yᴴ ε` on matrices written as vectors, where `ε` is the standard
form of signs `s`. -/
noncomputable abbrev shiftMatrix (s : n → ℤˣ) (X : Matrix n' p (𝔸 E)) (Y : Matrix n q (𝔸 E)) :
    Matrix (n' × n) (p × q) (𝔸 E) :=
  X ⊗ₖ (Yᴴ * stdForm E s)ᵀ

/-- Let `Ψ` be Schwartz–Bruhat above a set `P` of finite places disjoint from its conjugate. Let
`ℓ` be a bounded functional on the data space of Hom(S, T) that is invariant under the Heisenberg
operators `ϱ (X z Yᴴ ε)` for all adelic `z` (`shiftMatrix`; `ε` is the standard form). If the finite
part of `Xᴴ y Y` is not zero for every `y` with `Ψ y ≠ 0`, then `ℓ` kills `Ψ ⊗ f`
(`schrodingerOp`). -/
lemma map_schrodingerOp_eq_zero_of_invariant {P : Set (FinPlace E)} (hP : Set.IsConjDisjoint P)
    {Ψ : (n' × n → 𝔸f E) → ℂ} [hΨ : IsSchwartzBruhat P Ψ]
    (X : Matrix n' p (𝔸 E)) (Y : Matrix n q (𝔸 E)) {ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ}
    (hℓ : ∀ (z : p × q → 𝔸 E) (f : 𝒮 (S.hom T)), ℓ (ϱ (S.hom T) (shiftMatrix s X Y *ᵥ z) f) = ℓ f)
    (h_supp : ∀ y : n' × n → 𝔸f E, Ψ y ≠ 0 → (X.map snd)ᴴ * (vecToMatrix y * Y.map snd) ≠ 0)
    (f : 𝒮 (S.hom T)) : ℓ (schrodingerOp (S.hom T) P Ψ f) = 0 := by
  classical
  -- The entries of `Xᴴ y Y` are the pairings of `y` with the columns of `shiftMatrix s X Y`.
  refine map_eq_zero_of_support_not_orthogonal hP (LinearMap.range (shiftMatrix s X Y).mulVecLin)
    (Set.forall_mem_range.2 hℓ) (fun y hy ↦ ?_) f
  let K (i : p) (j : q) (x : n' × n) : 𝔸f E := (X x.1 i * star (Y x.2 j)).2
  obtain ⟨i, j, h_ne⟩ : ∃ (i : p) (j : q), star (K i j) ⬝ᵥ y ≠ 0 := by
    simpa [← ext_iff, K, dotProduct, Fintype.sum_prod_type, mul_apply, vecToMatrix,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using h_supp y hy
  have h_col : (fun x : n' × n ↦ ((shiftMatrix s X Y *ᵥ Pi.single (i, j) 1) x).2) = K i j :=
    funext fun x ↦ by simp [K, shiftMatrix, stdForm]
  exact ⟨shiftMatrix s X Y *ᵥ Pi.single (i, j) 1, ⟨Pi.single (i, j) 1, rfl⟩, by rwa [h_col]⟩

end Supports

/-! ### Short isotropic vectors -/

section AdelicPoints

variable {E n ι : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Fintype ι] {s : n → ℤˣ}
  (V : Space E n s)

/-- The adelic points of a subspace `Z` of `V`: the span over the adeles of the adelic vectors of
the elements of `Z`. -/
noncomputable def Space.adelicPoints (Z : Submodule E (n → E)) : Submodule (𝔸 E) (n → 𝔸 E) :=
  Submodule.span (𝔸 E) (V.vecAtPoint '' Z)

/-- The rational points among the adelic points of a subspace `Z` of `V`: the adelic vectors of the
elements of `Z`. -/
noncomputable def Space.ratPoints (Z : Submodule E (n → E)) : AddSubgroup (V.adelicPoints Z) where
  carrier := {x : V.adelicPoints Z | ∃ γ ∈ Z, V.vecAtPoint γ = x}
  add_mem' := by
    rintro x y ⟨γ, hγ, hx⟩ ⟨η, hη, hy⟩
    exact ⟨γ + η, add_mem hγ hη, by simp [hx, hy]⟩
  zero_mem' := ⟨0, zero_mem Z, map_zero _⟩
  neg_mem' := by
    rintro x ⟨γ, hγ, hx⟩
    exact ⟨-γ, neg_mem hγ, by simp [hx]⟩

/-- The adelic points of the span of finitely many vectors `z i` are the adelic combinations of the
adelic vectors of the `z i`. -/
lemma Space.mem_adelicPoints_span_range_iff {E n ι : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] [Fintype ι] {s : n → ℤˣ} (V : Space E n s) (z : ι → n → E) (x : n → 𝔸 E) :
    x ∈ V.adelicPoints (Submodule.span E (Set.range z)) ↔
      ∃ c : ι → 𝔸 E, ∑ i : ι, c i • V.vecAtPoint (z i) = x := by
  let W : Submodule (𝔸 E) (n → 𝔸 E) := .span (𝔸 E) (Set.range fun i : ι ↦ V.vecAtPoint (z i))
  have h_le : Submodule.span E (Set.range z) ≤ W.comap V.vecAtPoint :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun i ↦ Submodule.subset_span ⟨i, rfl⟩)
  have h_span : V.adelicPoints (Submodule.span E (Set.range z)) = W := by
    refine le_antisymm (Submodule.span_le.2 (Set.image_subset_iff.2 h_le)) (Submodule.span_mono ?_)
    exact Set.range_subset_iff.2 fun i ↦ ⟨z i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  rw [h_span, Submodule.mem_span_range_iff_exists_fun]

/-- There is `R > 0` such that, for every nonzero natural number `M`, every adele is congruent
modulo `E` to `M` times an adele with integral finite part and infinite components of modulus at
most `R`. -/
lemma exists_toAdele_add_eq_nsmul (E : Type) [Field E] [CMType E] :
    ∃ R : ℝ, 0 < R ∧ ∀ M : ℕ, M ≠ 0 → ∀ c : 𝔸 E,
      ∃ (a : E) (w : 𝔸 E), toAdele a + c = M • w ∧ ‖w.1‖ ≤ R ∧ w.2 ∈ Ô E := by
  -- `F` is a fundamental domain for `E` in its adeles, inside a ball of radius `R` times `Ô E`.
  obtain ⟨R, hR, -, F, h_box, -, -, h_fund⟩ := exists_hasFundDomain_toAdele (E := E)
  refine ⟨R, hR, fun M hM c ↦ ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : E, toAdele a + toAdele (M : E)⁻¹ * c ∈ F := (h_fund _).exists
  obtain ⟨h_ball, h_int⟩ := h_box ha
  refine ⟨M * a, toAdele a + toAdele (M : E)⁻¹ * c, ?_, mem_closedBall_zero_iff.1 h_ball, h_int⟩
  rw [nsmul_eq_mul, ← map_natCast (toAdele (E := E)), mul_add, ← mul_assoc, ← map_mul, ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, one_mul]

/-- The map `c ↦ ∑ c i • z i` from adelic coefficients to the adelic points of the span of the
vectors `z i`. -/
noncomputable def Space.adelicCombination (z : ι → n → E) :
    (ι → 𝔸 E) →+ V.adelicPoints (Submodule.span E (Set.range z)) :=
  .mk' (fun c : ι → 𝔸 E ↦ ⟨∑ i : ι, c i • V.vecAtPoint (z i),
      (V.mem_adelicPoints_span_range_iff z _).2 ⟨c, rfl⟩⟩)
    fun c c' ↦ Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])

lemma Space.continuous_adelicCombination {E n ι : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] [Fintype ι] {s : n → ℤˣ} (V : Space E n s) (z : ι → n → E) :
    Continuous (V.adelicCombination z) :=
  Continuous.subtype_mk (by fun_prop) _

/-- Every adelic point of the span of the `z i` is an adelic combination of the `z i`. -/
lemma Space.adelicCombination_surjective {E n ι : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] [Fintype ι] {s : n → ℤˣ} (V : Space E n s) (z : ι → n → E) :
    Function.Surjective (V.adelicCombination z) := by
  intro x
  obtain ⟨c, hc⟩ := (V.mem_adelicPoints_span_range_iff z x).1 x.prop
  exact ⟨c, Subtype.ext hc⟩

/-- The map `c ↦ ∑ c i • z i` carries rational coefficients to rational points of the span. -/
lemma Space.ratVectors_le_comap_adelicCombination {E n ι : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] [Fintype ι] {s : n → ℤˣ} (V : Space E n s) (z : ι → n → E) :
    New.ratVectors E ι ≤
      (V.ratPoints (Submodule.span E (Set.range z))).comap (V.adelicCombination z) := by
  rintro _ ⟨a, rfl⟩
  refine ⟨∑ i : ι, a i • z i, (Submodule.mem_span_range_iff_exists_fun E).2 ⟨a, rfl⟩, ?_⟩
  simp [adelicCombination, LinearMap.map_smulₛₗ]

/-- The adelic points of a subspace `Z` of `V` modulo the rational ones form a compact group. -/
lemma Space.compactSpace_adelicPoints_quotient {E n : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] {s : n → ℤˣ} (V : Space E n s) (Z : Submodule E (n → E)) :
    CompactSpace (V.adelicPoints Z ⧸ V.ratPoints Z) := by
  -- For generators `z i` of `Z`, the map `c ↦ ∑ c i • z i` makes it a quotient of `𝔸 ^ m ⧸ E ^ m`.
  obtain ⟨m, z, rfl⟩ : ∃ (m : ℕ) (z : Fin m → n → E), Submodule.span E (Set.range z) = Z :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian Z)
  let Z : Submodule E (n → E) := Submodule.span E (Set.range z)
  let ψ : (Fin m → 𝔸 E) ⧸ New.ratVectors E (Fin m) →+ V.adelicPoints Z ⧸ V.ratPoints Z :=
    QuotientAddGroup.map _ _ (V.adelicCombination z) (V.ratVectors_le_comap_adelicCombination z)
  have hψ_onto : Function.Surjective ψ :=
    (QuotientAddGroup.mk_surjective.comp (V.adelicCombination_surjective z)).of_comp
      (g := QuotientAddGroup.mk)
  exact hψ_onto.compactSpace <| QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.1
    (QuotientAddGroup.continuous_mk.comp (V.continuous_adelicCombination z))

/-- The mean of a function `F` on adelic vectors over the adelic points of a subspace `Z` of `V`
modulo the rational ones, for the Haar probability measure of this compact group. It is meant for
`F` periodic under the rational points. -/
noncomputable def Space.subspaceMean (Z : Submodule E (n → E)) (F : (n → 𝔸 E) → ℂ) : ℂ :=
  haveI : CompactSpace (V.adelicPoints Z ⧸ V.ratPoints Z) := V.compactSpace_adelicPoints_quotient Z
  quotMean (V.ratPoints Z) fun x : V.adelicPoints Z ↦ F x

/-- The mean over the adelic points of the span of vectors `z i` may be computed in the coordinates
`c ↦ ∑ c i • z i`, as a mean over adelic `c` modulo rational `c`, if the function is continuous and
periodic under the rational points. -/
lemma Space.subspaceMean_span_range {E n ι : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] [Fintype ι] {s : n → ℤˣ} (V : Space E n s) (z : ι → n → E) {F : (n → 𝔸 E) → ℂ}
    (hF : IsContPeriodic (V.ratPoints (Submodule.span E (Set.range z)))
      fun x : V.adelicPoints (Submodule.span E (Set.range z)) ↦ F x) :
    V.subspaceMean (Submodule.span E (Set.range z)) F =
      quotMean (New.ratVectors E ι) fun c : ι → 𝔸 E ↦ F (∑ i : ι, c i • V.vecAtPoint (z i)) := by
  have := V.compactSpace_adelicPoints_quotient (Submodule.span E (Set.range z))
  exact (quotMean_comp (New.ratVectors E ι) (V.adelicCombination z) hF
    (V.ratVectors_le_comap_adelicCombination z) (V.adelicCombination_surjective z)
    (V.continuous_adelicCombination z)).symm

end AdelicPoints

section IsotropicShifts

/-- On the adelic points of an isotropic subspace `Z` of `V`, the Heisenberg operators compose
without a cocycle. -/
lemma Space.rho_add_of_mem_adelicPoints {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s} {Z : Submodule E (n → E)}
    (h_iso : ∀ γ ∈ Z, ∀ η ∈ Z, star γ ⬝ᵥ V.J *ᵥ η = 0) {x y : n → 𝔸 E}
    (hx : x ∈ V.adelicPoints Z) (hy : y ∈ V.adelicPoints Z) (f : 𝒮 V) :
    V.ϱ (x + y) f = V.ϱ x (V.ϱ y f) := by
  -- The form vanishes on rational points, hence by sesquilinearity on their adelic span.
  have h_form : star y ⬝ᵥ stdForm E s *ᵥ x = 0 := by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem _ _ hx hy =>
      obtain ⟨η, hη, rfl⟩ := hx
      obtain ⟨γ, hγ, rfl⟩ := hy
      rw [V.stdForm_vecAtPoint, h_iso γ hγ η hη, map_zero]
    | _ => simp [mulVec_add, mulVec_smul, *]
  have h_beta : (adelicHeisenberg E s).β x y = 1 := by simp [adelicHeisenberg, h_form]
  rw [V.heisenbergRep.mul, h_beta, one_smul]

/-- Let `Z` be an isotropic subspace of `V` and `Λ` a bounded functional that is invariant under the
Heisenberg operators of `Z`. Then `x ↦ Λ (ϱ x f)` is continuous on the adelic points of `Z` and
periodic under the rational ones. -/
lemma Space.isContPeriodic_ratPoints {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s} {Z : Submodule E (n → E)}
    (h_iso : ∀ γ ∈ Z, ∀ η ∈ Z, star γ ⬝ᵥ V.J *ᵥ η = 0) {Λ : 𝒮 V →L[ℂ] ℂ}
    (h_inv : ∀ γ ∈ Z, ∀ f : 𝒮 V, Λ (V.ϱ (V.vecAtPoint γ) f) = Λ f) (f : 𝒮 V) :
    IsContPeriodic (V.ratPoints Z) fun x : V.adelicPoints Z ↦ Λ (V.ϱ x f) := by
  refine ⟨by fun_prop, ?_⟩
  rintro y ⟨γ, hγ, hy⟩ x
  simp only [Submodule.coe_add, rho_add_of_mem_adelicPoints h_iso y.prop x.prop]
  rw [← hy, h_inv γ hγ]

/-- Let `V` be a hermitian space over the CM field `E` with Weil data. Let `Z` be a subspace of
`E^n` that is isotropic for the form `J` of `V`. Let `Λ` be a bounded (continuous linear) functional
on the Schwartz space `𝒮 V` with `Λ (V.ϱ (V.vecAtPoint γ) f) = Λ f` for every rational vector
`γ ∈ Z`, where `V.ϱ x` is the Heisenberg operator of the adelic vector `x`. Then the mean
(`V.subspaceMean Z`) of `x ↦ Λ (V.ϱ x f)` over the adelic points of `Z` modulo the rational ones is,
as a function of `f`, again a bounded functional `Λ₀` on `𝒮 V`. -/
lemma Space.exists_eq_subspaceMean {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s} {Z : Submodule E (n → E)}
    (h_iso : ∀ γ ∈ Z, ∀ η ∈ Z, star γ ⬝ᵥ V.J *ᵥ η = 0) {Λ : 𝒮 V →L[ℂ] ℂ}
    (h_inv : ∀ γ ∈ Z, ∀ f : 𝒮 V, Λ (V.ϱ (V.vecAtPoint γ) f) = Λ f) :
    ∃ Λ₀ : 𝒮 V →L[ℂ] ℂ, ∀ f : 𝒮 V, Λ₀ f = V.subspaceMean Z fun x : n → 𝔸 E ↦ Λ (V.ϱ x f) := by
  have := V.compactSpace_adelicPoints_quotient Z
  let A (q : V.adelicPoints Z ⧸ V.ratPoints Z) : 𝒮 V →L[ℂ] ℂ := Λ ∘L V.ϱ (q.out : V.adelicPoints Z)
  exact ⟨strongIntegral (Measure.addHaarMeasure ⊤) A, strongIntegral_apply _ A
    fun f ↦ (isContPeriodic_ratPoints h_iso h_inv f).integrable_out⟩

/-- Let `Z` be an isotropic subspace of `V`, `Λ` a bounded functional that is invariant under the
Heisenberg operators of `Z`, and `Λ₀` the mean of `Λ ∘ ϱ x` over the adelic points `x` of `Z` modulo
the rational ones. Then `Λ₀` is invariant under `ϱ y` for all adelic points `y` of `Z`. -/
lemma Space.subspaceMean_rho {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s} {Z : Submodule E (n → E)}
    (h_iso : ∀ γ ∈ Z, ∀ η ∈ Z, star γ ⬝ᵥ V.J *ᵥ η = 0) {Λ Λ₀ : 𝒮 V →L[ℂ] ℂ}
    (h_inv : ∀ γ ∈ Z, ∀ f : 𝒮 V, Λ (V.ϱ (V.vecAtPoint γ) f) = Λ f)
    (h_mean : ∀ f : 𝒮 V, Λ₀ f = V.subspaceMean Z fun x : n → 𝔸 E ↦ Λ (V.ϱ x f))
    {y : n → 𝔸 E} (hy : y ∈ V.adelicPoints Z) (f : 𝒮 V) : Λ₀ (V.ϱ y f) = Λ₀ f := by
  have := V.compactSpace_adelicPoints_quotient Z
  have h_shift (x : V.adelicPoints Z) : V.ϱ x (V.ϱ y f) = V.ϱ (x + y) f :=
    (rho_add_of_mem_adelicPoints h_iso x.prop hy f).symm
  simp only [h_mean, subspaceMean, h_shift]
  exact quotMean_translate (isContPeriodic_ratPoints h_iso h_inv f) ⟨y, hy⟩

/-- Let `f₀` lie in the finite part of `𝒮 V`. There is a nonzero natural number `M` such that, for
every adelic vector `u` with integral finite part, the Heisenberg operator of the finite part of
`M • u` fixes `f₀`. -/
lemma Space.exists_rho_nsmul_eq_self {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s} {f₀ : 𝒮 V}
    (hf₀ : f₀ ∈ V.finitePart) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ u : n → 𝔸 E, (∀ k : n, (u k).2 ∈ Ô E) →
      V.ϱ (fun k : n ↦ (0, ((M • u) k).2)) f₀ = f₀ := by
  -- The map `x ↦ ϱ (finVec x) f₀` is locally constant, and `finVec` multiplies by `α`; some `M`
  -- carries the compact set `α⁻¹ Ô ^ n` into the neighbourhood of `0` where it is constant.
  obtain ⟨M, hM, h_near⟩ : ∃ M : ℕ, M ≠ 0 ∧
      ∀ x ∈ (fun x : n → 𝔸f E ↦ (α (E := E))⁻¹.val • x) '' stdLattice E n,
        V.ϱ (finVec ((M : 𝔸f E) • x)) f₀ = V.ϱ (finVec 0) f₀ :=
    exists_natCast_smul_mem_of_isCompact E
      (stdLattice.isCompact_stdLattice.image (continuous_const_smul _))
      ((V.isLocallyConstant_rho_finVec hf₀).eventually_eq 0)
  refine ⟨M, hM, fun u hu ↦ ?_⟩
  have h_vec : (fun k : n ↦ (0, ((M • u) k).2)) =
      finVec ((M : 𝔸f E) • (α (E := E))⁻¹.val • fun k : n ↦ (u k).2) :=
    funext fun k ↦ by simp [finVec, mul_left_comm (α (E := E)).val]
  have h_zero : finVec (0 : n → 𝔸f E) = 0 := funext fun k ↦ by simp [finVec]
  rw [h_vec, h_near _ ⟨fun k ↦ (u k).2, hu, rfl⟩, h_zero, Rep.rho_zero_apply]

/-- Let `f₀` lie in the finite part of `𝒮 V` and let `ι` be a finite index type. There is `C` as
follows. Let the vectors `z i` lie in the lattice at `g` with lengths at most `δ ≥ 0`
(`latticeBall`). Then every adelic point `x` of their span has a rational translate `γ + x` such
that `ϱ (g⁻¹ (γ + x))` acts on the data `v ⊗ f₀` (`integrated`) as a real translation of `v`
(`realHeisenbergOp`) by a vector whose coordinates have modulus at most `C δ`. -/
lemma Space.exists_rho_eq_realHeisenbergOp {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s} {f₀ : 𝒮 V} (hf₀ : f₀ ∈ V.finitePart)
    (ι : Type) [Fintype ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : G E s) (δ : ℝ) (z : ι → n → E), 0 ≤ δ →
      (∀ i : ι, z i ∈ (V.move g).latticeBall δ) →
      ∀ x ∈ V.adelicPoints (Submodule.span E (Set.range z)),
      ∃ γ ∈ Submodule.span E (Set.range z), ∃ y : NumberField.InfinitePlace E × n → ℂ,
        ‖y‖ ≤ C * δ ∧
        ∀ v : fockSpace (realSigns E s),
          V.ϱ (g⁻¹.adeleMatrix *ᵥ (V.vecAtPoint γ + x)) (V.integrated v f₀) =
            V.integrated (realHeisenbergOp y v) f₀ := by
  obtain ⟨M, hM, h_fix⟩ : ∃ M : ℕ, M ≠ 0 ∧ ∀ u : n → 𝔸 E, (∀ k : n, (u k).2 ∈ Ô E) →
      V.ϱ (fun k : n ↦ (0, ((M • u) k).2)) f₀ = f₀ := exists_rho_nsmul_eq_self hf₀
  obtain ⟨R, hR, h_reduce⟩ := exists_toAdele_add_eq_nsmul E
  let σ : NumberField.InfinitePlace E → ℂ := fst (scaleIdele E).val
  refine ⟨M * Fintype.card ι * R * ‖σ⁻¹‖, by positivity, fun g δ z hδ hz x hx ↦ ?_⟩
  -- Write `x = ∑ c i • z i` and reduce the coefficients modulo `E` to `M • w i`.
  obtain ⟨c, rfl⟩ := (V.mem_adelicPoints_span_range_iff z x).1 hx
  have h_coeff (i : ι) :
      ∃ (a : E) (w : 𝔸 E), toAdele a + c i = M • w ∧ ‖w.1‖ ≤ R ∧ w.2 ∈ Ô E := h_reduce M hM (c i)
  choose a w h_eq hw_le hw_int using h_coeff
  obtain ⟨hz_int, hz_le⟩ : (∀ i : ι, z i ∈ (V.move g).baseLattice) ∧
      ∀ i : ι, ‖(V.move g).archCoords (z i)‖ ≤ δ := forall_and.1 hz
  let u : n → 𝔸 E := ∑ i : ι, w i • (V.move g).vecAtPoint (z i)
  have h_point : g⁻¹.adeleMatrix *ᵥ (V.vecAtPoint (∑ i : ι, a i • z i) +
      ∑ i : ι, c i • V.vecAtPoint (z i)) = M • u := by
    simp only [u, map_sum, LinearMap.map_smulₛₗ, ← Finset.sum_add_distrib, ← add_smul, h_eq,
      vecAtPoint_move, mulVec_sum, mulVec_smul, Finset.smul_sum, smul_assoc]
  have hu_int (k : n) : (u k).2 ∈ Ô E := by
    simp only [u, Finset.sum_apply, Prod.snd_sum]
    exact sum_mem fun i _ ↦ mul_mem (hw_int i) (hz_int i k)
  have hu_le (τ : NumberField.InfinitePlace E) (k : n) :
      ‖(u k).1 τ‖ ≤ Fintype.card ι * (R * δ) := by
    have h_term (i : ι) : ‖(w i).1 τ * ((V.move g).vecAtPoint (z i) k).1 τ‖ ≤ R * δ := by
      have h_coord : ‖((V.move g).vecAtPoint (z i) k).1 τ‖ ≤ ‖(V.move g).archCoords (z i)‖ :=
        PiLp.norm_apply_le ((V.move g).archCoords (z i)) (τ, k)
      grw [norm_mul, norm_le_pi_norm (w i).1 τ, hw_le i, h_coord, hz_le i]
    simpa [u, Finset.sum_apply, Prod.fst_sum] using
      norm_sum_le_of_le Finset.univ fun i _ ↦ h_term i
  have h_size : ‖realCoord (M • u)‖ ≤ M * Fintype.card ι * R * ‖σ⁻¹‖ * δ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ⟨τ, k⟩ ↦ ?_
    calc ‖realCoord (M • u) (τ, k)‖
      _ = M * ‖(u k).1 τ‖ * ‖σ⁻¹ τ‖ := by simp [σ, realCoord, div_eq_mul_inv]
      _ ≤ M * (Fintype.card ι * (R * δ)) * ‖σ⁻¹‖ := by grw [hu_le τ k, norm_le_pi_norm σ⁻¹ τ]
      _ = _ := by ring
  refine ⟨∑ i : ι, a i • z i, (Submodule.mem_span_range_iff_exists_fun E).2 ⟨a, rfl⟩,
    realCoord (M • u), h_size, fun v ↦ ?_⟩
  rw [h_point, rho_integrated_realCoord, h_fix u hu_int]

/-- The Heisenberg operator of `x` passes through the Weil operator `ω g` as that of `g⁻¹ x`. -/
lemma Space.rho_omega {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
    {s : n → ℤˣ} (V : Space E n s) (g : G E s) (x : n → 𝔸 E) (f : 𝒮 V) :
    V.ϱ x (V.ω g f) = V.ω g (V.ϱ (g⁻¹.adeleMatrix *ᵥ x) f) := by
  rw [omega_rho, mulVec_mulVec, ← adeleMatrix_mul, mul_inv_cancel, adeleMatrix_one, one_mulVec]

/-- Differencing along short isotropic vectors. Let `f₀` lie in the finite part of `𝒮 V`, let `l` be
a natural number and `ι` a finite index type. There is `C` as follows. Let the vectors `z i` of the
lattice at `g` have lengths at most `δ ≥ 0` and span an isotropic subspace `Z`. Let `Λ` be a bounded
functional that is invariant under the Heisenberg operators `ϱ` of `Z`. Suppose that, for all `f`,
a bound for the differences `‖Λ (ω g f) - Λ (ϱ x (ω g f))‖` at all adelic points `x` of `Z` bounds
`‖Λ (ω g f)‖`. Then `‖Λ (ω g (v ⊗ f₀))‖ ≤ C ‖Λ ∘ ω g‖ δ ^ l ‖v‖_l` for all `v` whose moment `‖v‖_l`
(`fockMoment`) is finite. Here `v ⊗ f₀` is `V.integrated v f₀`. -/
lemma Space.exists_norm_le_of_differences {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s} {f₀ : 𝒮 V} (hf₀ : f₀ ∈ V.finitePart)
    (l : ℕ) (ι : Type) [Fintype ι] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : G E s) (δ : ℝ) (z : ι → n → E) (Z : Submodule E (n → E)) (Λ : 𝒮 V →L[ℂ] ℂ),
      0 ≤ δ → (∀ i : ι, z i ∈ (V.move g).latticeBall δ) →
      Submodule.span E (Set.range z) = Z →
      (∀ γ ∈ Z, ∀ η ∈ Z, star γ ⬝ᵥ V.J *ᵥ η = 0) →
      (∀ γ ∈ Z, ∀ f : 𝒮 V, Λ (V.ϱ (V.vecAtPoint γ) f) = Λ f) →
      (∀ (f : 𝒮 V) (B : ℝ),
        (∀ x ∈ V.adelicPoints Z, ‖Λ (V.ω g f) - Λ (V.ϱ x (V.ω g f))‖ ≤ B) → ‖Λ (V.ω g f)‖ ≤ B) →
      ∀ v : fockSpace (realSigns E s), fockMoment l v ≠ ⊤ →
      ‖Λ (V.ω g (V.integrated v f₀))‖ ≤ C * ‖Λ ∘L V.ω g‖ * δ ^ l * (fockMoment l v).toReal := by
  -- Modulo `Z`, the shifts `ϱ (g⁻¹ x)` act on `v ⊗ f₀` by real translations of size at most `C₀ δ`.
  -- On Fock space each derivative along them gains this factor and costs one moment of `v`.
  obtain ⟨C, h_fock⟩ := exists_enorm_le_mul_fockMoment_of_norm_sub_le (ε := realSigns E s) l
  obtain ⟨C₀, hC₀, h_real⟩ := exists_rho_eq_realHeisenbergOp hf₀ ι
  let J : fockSpace (realSigns E s) →L[ℂ] 𝒮 V := V.integrated.flip f₀
  refine ⟨C * ‖J‖ * C₀ ^ l, by positivity, ?_⟩
  rintro g δ z _ Λ hδ hz rfl h_iso h_inv h_shifts v hv
  let L : 𝒮 V →L[ℂ] ℂ := Λ ∘L V.ω g
  have h_diff (v : fockSpace (realSigns E s)) (B : ℝ)
      (hB : ∀ y : NumberField.InfinitePlace E × n → ℂ, ‖y‖ ≤ C₀ * δ →
        ‖(L ∘L J) v - (L ∘L J) (realHeisenbergOp y v)‖ ≤ B) :
      ‖(L ∘L J) v‖ ≤ B := by
    refine h_shifts (J v) B fun x hx ↦ ?_
    obtain ⟨γ, hγ, y, hy, h_eq⟩ := h_real g δ z hδ hz x hx
    have h_value : Λ (V.ϱ x (V.ω g (J v))) = (L ∘L J) (realHeisenbergOp y v) := by
      change Λ (V.ϱ x (V.ω g (V.integrated v f₀))) =
        Λ (V.ω g (V.integrated (realHeisenbergOp y v) f₀))
      rw [← h_eq, ← rho_omega,
        rho_add_of_mem_adelicPoints h_iso (Submodule.subset_span ⟨γ, hγ, rfl⟩) hx, h_inv γ hγ]
    rw [h_value]
    exact hB y hy
  have h_enorm : ‖(L ∘L J) v‖ₑ ≤ ENNReal.ofReal (C * ‖L ∘L J‖ * (C₀ * δ) ^ l) * fockMoment l v :=
    h_fock _ (L ∘L J) (by positivity) fun _ ↦ h_diff
  calc ‖(L ∘L J) v‖
    _ ≤ C * ‖L ∘L J‖ * (C₀ * δ) ^ l * (fockMoment l v).toReal := by
      rw [← toReal_enorm, ← toReal_ofReal_mul _ _ (by positivity)]
      exact toReal_mono (mul_ne_top ofReal_ne_top hv) h_enorm
    _ ≤ C * (‖L‖ * ‖J‖) * (C₀ * δ) ^ l * (fockMoment l v).toReal := by grw [L.opNorm_comp_le]
    _ = _ := by ring

/-- Let `f₀` lie in the finite part of `𝒮 V`, let `l` be a natural number and `ι` a finite index
type. There is `C` as follows. Let `g` be an adelic point of the unitary group, `δ ≥ 0`, and let the
vectors `z i` of the lattice at `g` have lengths at most `δ` (`latticeBall`) and span an isotropic
subspace `Z` of `V`. Let `Λ` be a bounded functional on `𝒮 V` that is invariant under the Heisenberg
operators `ϱ` of `Z`, and `Λ₀` the mean of `Λ ∘ ϱ x` over the adelic points `x` of `Z` modulo the
rational ones (it exists by `exists_eq_subspaceMean`). Then `‖(Λ - Λ₀) (ω g (v ⊗ f₀))‖ ≤ C ‖Λ ∘ ω g‖
δ ^ l ‖v‖_l` for all `v` in Fock space whose moment `‖v‖_l` (`fockMoment`) is finite. Here `ω` is
the Weil representation and `v ⊗ f₀` is `V.integrated v f₀`. -/
theorem Space.exists_norm_sub_subspaceMean_le {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s} {f₀ : 𝒮 V} (hf₀ : f₀ ∈ V.finitePart)
    (l : ℕ) (ι : Type) [Fintype ι] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : G E s) (δ : ℝ) (z : ι → n → E) (Z : Submodule E (n → E)) (Λ Λ₀ : 𝒮 V →L[ℂ] ℂ),
      0 ≤ δ → (∀ i : ι, z i ∈ (V.move g).latticeBall δ) →
      Submodule.span E (Set.range z) = Z →
      (∀ γ ∈ Z, ∀ η ∈ Z, star γ ⬝ᵥ V.J *ᵥ η = 0) →
      (∀ γ ∈ Z, ∀ f : 𝒮 V, Λ (V.ϱ (V.vecAtPoint γ) f) = Λ f) →
      (∀ f : 𝒮 V, Λ₀ f = V.subspaceMean Z fun x : n → 𝔸 E ↦ Λ (V.ϱ x f)) →
      ∀ v : fockSpace (realSigns E s), fockMoment l v ≠ ⊤ →
      ‖(Λ - Λ₀) (V.ω g (V.integrated v f₀))‖ ≤
        C * ‖Λ ∘L V.ω g‖ * δ ^ l * (fockMoment l v).toReal := by
  -- The functional `Λ - Λ₀` has mean zero, so it is the mean of its differences, and
  -- `‖(Λ - Λ₀) ∘ ω g‖ ≤ 2 ‖Λ ∘ ω g‖` because the operators `ϱ` preserve norms.
  obtain ⟨C, hC, h_differences⟩ := exists_norm_le_of_differences hf₀ l ι
  refine ⟨2 * C, by positivity, fun g δ z Z Λ Λ₀ hδ hz hZ h_iso h_inv h_mean v hv ↦ ?_⟩
  have := V.compactSpace_adelicPoints_quotient Z
  have h_norm_mean : ‖Λ₀ ∘L V.ω g‖ ≤ ‖Λ ∘L V.ω g‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f ↦ ?_
    have h_term (x : V.adelicPoints Z) : ‖Λ (V.ϱ x (V.ω g f))‖ ≤ ‖Λ ∘L V.ω g‖ * ‖f‖ := by
      rw [rho_omega, ← V.heisenbergRep.norm_map (g⁻¹.adeleMatrix *ᵥ x) f]
      exact (Λ ∘L V.ω g).le_opNorm _
    rw [ContinuousLinearMap.comp_apply, h_mean]
    exact norm_quotMean_le _ h_term
  have h_norm : ‖(Λ - Λ₀) ∘L V.ω g‖ ≤ 2 * ‖Λ ∘L V.ω g‖ := by
    grw [ContinuousLinearMap.sub_comp, norm_sub_le, h_norm_mean, two_mul]
  have h_mean_inv {x : n → 𝔸 E} (hx : x ∈ V.adelicPoints Z) (f : 𝒮 V) : Λ₀ (V.ϱ x f) = Λ₀ f :=
    subspaceMean_rho h_iso h_inv h_mean hx f
  have h_inv_sub (γ : n → E) (hγ : γ ∈ Z) (f : 𝒮 V) :
      (Λ - Λ₀) (V.ϱ (V.vecAtPoint γ) f) = (Λ - Λ₀) f := by
    simp only [_root_.sub_apply, h_inv γ hγ, h_mean_inv (Submodule.subset_span ⟨γ, hγ, rfl⟩)]
  have h_as_mean (f : 𝒮 V) : (Λ - Λ₀) f = quotMean (V.ratPoints Z)
      fun x : V.adelicPoints Z ↦ (Λ - Λ₀) f - (Λ - Λ₀) (V.ϱ x f) := by
    simp only [_root_.sub_apply, h_mean_inv (Submodule.coe_mem _), sub_sub_sub_cancel_right]
    rw [h_mean, subspaceMean, quotMean, quotMean,
      integral_sub (integrable_const _) (isContPeriodic_ratPoints h_iso h_inv f).integrable_out]
    simp
  have h_shifts (f : 𝒮 V) (B : ℝ) (hB : ∀ x ∈ V.adelicPoints Z,
      ‖(Λ - Λ₀) (V.ω g f) - (Λ - Λ₀) (V.ϱ x (V.ω g f))‖ ≤ B) : ‖(Λ - Λ₀) (V.ω g f)‖ ≤ B := by
    rw [h_as_mean]
    exact norm_quotMean_le _ fun x ↦ hB x (Submodule.coe_mem x)
  calc ‖(Λ - Λ₀) (V.ω g (V.integrated v f₀))‖
    _ ≤ C * ‖(Λ - Λ₀) ∘L V.ω g‖ * δ ^ l * (fockMoment l v).toReal :=
      h_differences g δ z Z (Λ - Λ₀) hδ hz hZ h_iso h_inv_sub h_shifts v hv
    _ ≤ C * (2 * ‖Λ ∘L V.ω g‖) * δ ^ l * (fockMoment l v).toReal := by gcongr
    _ = _ := by ring

end IsotropicShifts

end KernelDecay

end New

end
