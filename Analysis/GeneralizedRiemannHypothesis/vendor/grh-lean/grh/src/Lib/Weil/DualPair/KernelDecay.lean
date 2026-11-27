import Lib.Weil.DualPair.ShortIsotropicVectors
import Lib.Weil.DualPair.ThetaLiftConvergence

/-!
# Rapid decay of theta kernels of unitary dual pairs under support conditions

This file proves that the theta kernel `New.pairTheta` of the dual pair U(S) × U(T), acting on
data on Hom(S, T) through `New.pairWeil`, decays rapidly under support conditions on the finite
datum `Ψ`. The kernel is `(g, h) ↦ θ (ω (g, h) φ)`, with `g` in the adelic group of `S` and `h` in
that of `T`. At a point of large height the proof uses short pairs of rational matrices
(`New.IsShortPair`) and the rational maps of rank one `dᵢ ⟨cⱼ, ·⟩` that they span.
`New.modDatum S T 𝔪 Ψ v` is the datum `v ⊗ Ψ ⊗ vac` on `Hom(S, T)`, where `Ψ` is a function on
matrices modulo an ideal `𝔪` prime to its conjugate (`New.Modulus`), and `New.pairTheta` is its
theta kernel on `U(S) × U(T)`.

## Main definitions and results

* `New.pairTheta_decay_of_onto`: rapid decay of the theta kernel on U(T) when Ψ is supported on
  surjective maps.
* `New.pairTheta_decay_of_injective`: rapid decay of the theta kernel on U(S) when Ψ is supported on
  injective maps.
* `New.pairTheta_modDatum_decay`: suppose some place divides `𝔪` and `Ψ` is supported on left
  invertible matrices. Then the kernel decays rapidly in the height of `g`, with polynomial growth
  in the height of `h`.

Notions from other files:
* `New.Space`: A hermitian space with a point: a matrix J over E and x in GL_n(𝔸) with xᴴJx equal to
  diag(s) at the infinite places and 1 at the finite places; Γ = x⁻¹U(J)(E)x.
* `New.Space.IsAutomorphic`, `New.Space.IsRapid`: a function F is automorphic if it is continuous,
  left Γ-invariant and right invariant under an open subgroup of G_f; it is rapid if |F(g)|·ht(g)^B
  is bounded for every B, and moderate (`New.Space.IsModerate`) if |F(g)| ≤ C·ht(g)^A for some C and
  A.
* `New.Modulus.liftFn`: A function Ψ of vectors modulo 𝔪 read on finite adelic vectors x: Ψ of the
  reduction of the components of x at the places dividing 𝔪 if these are integral, else 0.
* `New.Space.coordMatrix` (in `Lib.Weil.DualPair.ShortIsotropicVectors`): the coordinates
  `g⁻¹ x⁻¹ c` at an adelic point `g` of a matrix `c` over `E`.
* `New.Space.adelicPoints` (in `Lib.Weil.DualPair.ShortIsotropicVectors`): the span over the
  adeles of the adelic vectors of the elements of a subspace `Z` of `V`.

## Relation to the literature

Theta kernels of unitary dual pairs, with functoriality, seesaw, growth and rapid decay, are known.
Here both spaces are hermitian and act on the maps between them. Decay is proved for data
supported on maps of full rank at split places, using small shifts along a short isotropic vector
instead of Siegel sets. Source: S. Kudla, Seesaw dual reductive pairs, Progr. Math. 46 (1984);
Harris, Kudla, Sweet, Theta dichotomy for unitary groups, J. Amer. Math. Soc. 9 (1996), section 1;
for decay, Kudla, Rallis, A regularized Siegel-Weil formula: the first term identity, Ann. Math. 140
(1994).
-/

noncomputable section

namespace New

section KernelDecay

open MeasureTheory Matrix Kronecker
  Fock WeilData Space Prod G IsDualFamily Heisenberg ENNReal

variable {E : Type} [Field E] [CMType E] {n n' p q : Type} [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s')
  (a b : AutChar E) (g : G E s) (c : Matrix n q E)

variable {g c} {R : Type*} [CommRing R] [Nontrivial R] {φ : 𝔸f E →+* R} [Fintype p] [DecidableEq p]

variable [WeilData E] [Fintype q] {S T}

/-! ### Short pairs -/

/-- The matrix of the map `z ↦ d z cᴴ S.J` on matrices written as vectors. Its columns are the
rational maps `dᵢ ⟨cⱼ, ·⟩`, where `dᵢ` and `cⱼ` are the columns of `d` and `c` and `⟨·, ·⟩` is the
form of `S`. -/
noncomputable abbrev Space.rankOneMaps (S : Space E n s) (d : Matrix n' p E) (c : Matrix n q E) :
    Matrix (n' × n) (p × q) E :=
  d ⊗ₖ (cᴴ * S.J)ᵀ

/-- The conditions of the decay estimate at a point `(g, h)`, with `g` in the group of
`S : Space E n s` and `h` in that of `T : Space E n' s'`, on rational matrices `d` for `T` and `c`
for `S`, for a functional `ℓ` and a function `Ψ` on finite adelic maps. Below `d'` and `c'` are the
coordinates `Space.coordMatrix` of `d` at `h` and of `c` at `g`. -/
structure IsShortPair (g : G E s) (h : G E s') (ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ)
    (Ψ : (n' × n → 𝔸f E) → ℂ) (d : Matrix n' p E) (c : Matrix n q E) (x y t : ℝ) : Prop where
  /-- The columns of `d` are vectors of length at most `x` in the lattice at `h`. -/
  short_target : ∀ i : p, d.col i ∈ (T.move h).latticeBall x
  /-- The columns of `c` are vectors of length at most `y` in the lattice at `g`. -/
  short_source : ∀ j : q, c.col j ∈ (S.move g).latticeBall y
  /-- The product of the two length bounds is at most `t`. -/
  mul_le : x * y ≤ t
  /-- The columns of `d`, or those of `c`, span an isotropic subspace. -/
  isotropic : dᴴ * T.J * d = 0 ∨ cᴴ * S.J * c = 0
  /-- `ℓ` is invariant under the Heisenberg operators of the rational maps `z cᴴ S.J`. -/
  invariant : ∀ (z : Matrix n' q E) (f : 𝒮 (S.hom T)),
    ℓ (ϱ (S.hom T) (matrixToVec (T.ratMap S (z * cᴴ * S.J))) f) = ℓ f
  /-- Either the finite part of `d'ᴴ u c'` is not zero whenever `Ψ u ≠ 0`, or the mean of `ℓ ∘ ϱ u`
  over the adelic points `u` of the span of the maps `dᵢ ⟨cⱼ, ·⟩` is zero. -/
  ne_zero_or_mean_eq_zero :
    (∀ u : n' × n → 𝔸f E, Ψ u ≠ 0 →
      ((T.coordMatrix h d).map snd)ᴴ * (vecToMatrix u * (S.coordMatrix g c).map snd) ≠ 0) ∨
    ∀ f : 𝒮 (S.hom T),
      (S.hom T).subspaceMean (Submodule.span E (Set.range (S.rankOneMaps d c).col))
        (fun u : n' × n → 𝔸 E ↦ ℓ (ϱ (S.hom T) u f)) = 0

variable {E : Type} [Field E] [CMType E] {n n' p q : Type} [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} {R : Type*} [CommRing R] [Nontrivial R]
  [Fintype p] [WeilData E] [Fintype q]

section ShortPair

variable {S : Space E n s} {T : Space E n' s'} {g : G E s} {h : G E s'} {d : Matrix n' p E}
  {c : Matrix n q E}

omit [WeilData E] [Fintype q] in
/-- The coordinates at `g` of a column of `c` form the column of `Space.coordMatrix`. -/
lemma Space.move_vecAtPoint_col (j : q) :
    (S.move g).vecAtPoint (c.col j) = (S.coordMatrix g c).col j :=
  S.vecAtPoint_move g (c.col j)

omit [WeilData E] in
/-- The adelic points of the span of the columns of `c` are the vectors `g c' w`, where `c'` is the
matrix of coordinates of `c` at `g` (`Space.coordMatrix`) and `w` is an adelic vector. -/
lemma Space.mem_adelicPoints_span_col_iff (g : G E s) (u : n → 𝔸 E) :
    u ∈ S.adelicPoints (Submodule.span E (Set.range c.col)) ↔
      ∃ w : q → 𝔸 E, g.adeleMatrix *ᵥ S.coordMatrix g c *ᵥ w = u := by
  have h_sum (w : q → 𝔸 E) :
      ∑ j : q, w j • S.vecAtPoint (c.col j) = g.adeleMatrix *ᵥ S.coordMatrix g c *ᵥ w := by
    have h_cancel : g.adeleMatrix * S.coordMatrix g c = S.x⁻¹.val * c.map toAdele := by
      rw [coordMatrix, ← Matrix.mul_assoc, ← adeleMatrix_mul, mul_inv_cancel, adeleMatrix_one,
        Matrix.one_mul]
    have h_col (j : q) : S.vecAtPoint (c.col j) = (S.x⁻¹.val * c.map toAdele).col j := rfl
    ext1 i
    rw [mulVec_mulVec, h_cancel]
    simp [h_col, mulVec, dotProduct, mul_comm]
  simp only [mem_adelicPoints_span_range_iff, h_sum]

omit [WeilData E] [Fintype p] [Fintype q] in
/-- At the point `(g, h)` the maps `dᵢ ⟨cⱼ, ·⟩` have the coordinates `d'ᵢ c'ⱼᴴ ε`, where `d'` and
`c'` are the coordinates of `d` at `h` and of `c` at `g`, and `ε` is the standard form. -/
lemma coordMatrix_rankOneMaps :
    (S.hom T).coordMatrix (onHom (g, h)) (S.rankOneMaps d c) =
      shiftMatrix s (T.coordMatrix h d) (S.coordMatrix g c) := by
  have h_form : g⁻¹.adeleMatrixᴴ * stdForm E s = stdForm E s * g.adeleMatrix :=
    calc g⁻¹.adeleMatrixᴴ * stdForm E s
      _ = g⁻¹.adeleMatrixᴴ * stdForm E s * (g⁻¹.adeleMatrix * g.adeleMatrix) := by
        rw [← adeleMatrix_mul, inv_mul_cancel, adeleMatrix_one, Matrix.mul_one]
      _ = stdForm E s * g.adeleMatrix := by
        rw [← Matrix.mul_assoc, conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix]
  have h_source : (cᴴ * S.J).map toAdele * S.x.val * g.adeleMatrix =
      (S.coordMatrix g c)ᴴ * stdForm E s := by
    simp [coordMatrix, S.map_J, h_form, Matrix.mul_assoc]
  have h_point : (S.hom T).x⁻¹.val = T.x⁻¹.val ⊗ₖ S.x.valᵀ := rfl
  have h_map : (S.rankOneMaps d c).map toAdele = d.map toAdele ⊗ₖ ((cᴴ * S.J).map toAdele)ᵀ :=
    Matrix.ext fun _ _ ↦ map_mul toAdele _ _
  rw [coordMatrix, ← map_inv, adeleMatrix_onHom, h_point, h_map, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← transpose_mul, ← transpose_mul, Prod.fst_inv, inv_inv, h_source]
  rfl

omit [WeilData E] [Fintype p] [Fintype q] in
/-- If the columns `dᵢ` and `cⱼ` are vectors of lengths at most `x` and `y` in the lattices at `h`
and `g`, then the map `dᵢ ⟨cⱼ, ·⟩` has length at most `x y` and lies in the lattice of Hom(S, T) at
`(g, h)`. -/
lemma col_rankOneMaps_mem_latticeBall {i : p} {j : q} {x y : ℝ}
    (hd : d.col i ∈ (T.move h).latticeBall x) (hc : c.col j ∈ (S.move g).latticeBall y) :
    (S.rankOneMaps d c).col (i, j) ∈ ((S.hom T).move (onHom (g, h))).latticeBall (x * y) := by
  obtain ⟨hd_int, hd_le⟩ := hd
  obtain ⟨hc_int, hc_le⟩ := hc
  set u : n' → 𝔸 E := (T.move h).vecAtPoint (d.col i) with hu
  set w : n → 𝔸 E := (S.move g).vecAtPoint (c.col j) with hw
  have h_entry (k : n' × n) :
      ((S.hom T).move (onHom (g, h))).vecAtPoint ((S.rankOneMaps d c).col (i, j)) k =
        u k.1 * (star (w k.2) * stdForm E s k.2 k.2) := by
    simp only [hu, hw, move_vecAtPoint_col, coordMatrix_rankOneMaps]
    simp [stdForm]
  refine ⟨fun k ↦ ?_, ?_⟩
  · simpa [h_entry, stdForm] using mul_mem (hd_int k.1) (star_mem_Ô (hc_int k.2))
  -- At each infinite place the squared length of the map is the product of those of `u` and `w`,
  -- and that of `w` at one place is at most its total squared length.
  have h_place (τ : NumberField.InfinitePlace E) :
      ∑ k : n, ‖(w k).1 τ‖ ^ 2 ≤ ‖(S.move g).archCoords (c.col j)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    exact Finset.single_le_sum
      (f := fun τ' : NumberField.InfinitePlace E ↦ ∑ k : n, ‖(w k).1 τ'‖ ^ 2)
      (fun _ _ ↦ by positivity) (Finset.mem_univ τ)
  refine le_of_sq_le_sq ?_ (mul_nonneg ((norm_nonneg _).trans hd_le) ((norm_nonneg _).trans hc_le))
  calc ‖((S.hom T).move (onHom (g, h))).archCoords ((S.rankOneMaps d c).col (i, j))‖ ^ 2
    _ = ∑ τ : NumberField.InfinitePlace E, ∑ k' : n',
        ‖(u k').1 τ‖ ^ 2 * ∑ k : n, ‖(w k).1 τ‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, archCoords, h_entry, stdForm,
        abs_unit_intCast, mul_pow, Finset.mul_sum]
    _ ≤ ∑ τ : NumberField.InfinitePlace E, ∑ k' : n',
        ‖(u k').1 τ‖ ^ 2 * ‖(S.move g).archCoords (c.col j)‖ ^ 2 := by grw [h_place]
    _ = ‖(T.move h).archCoords (d.col i)‖ ^ 2 * ‖(S.move g).archCoords (c.col j)‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq ((T.move h).archCoords _), Fintype.sum_prod_type,
        Finset.sum_mul]
      rfl
    _ ≤ (x * y) ^ 2 := by grw [hd_le, hc_le, mul_pow]

omit [WeilData E] in
/-- If the columns of `d`, or those of `c`, span an isotropic subspace, then the maps `dᵢ ⟨cⱼ, ·⟩`
span an isotropic subspace of Hom(S, T). -/
lemma isotropic_span_rankOneMaps (h_iso : dᴴ * T.J * d = 0 ∨ cᴴ * S.J * c = 0) :
    ∀ γ ∈ Submodule.span E (Set.range (S.rankOneMaps d c).col),
    ∀ η ∈ Submodule.span E (Set.range (S.rankOneMaps d c).col),
      star γ ⬝ᵥ (S.hom T).J *ᵥ η = 0 := by
  have h_source : (cᴴ * S.J)ᵀᴴ * S.J⁻¹ᵀ * (cᴴ * S.J)ᵀ = (cᴴ * S.J * c)ᴴᵀ := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, ← transpose_mul,
      ← Matrix.mul_assoc, conjTranspose_mul (cᴴ * S.J),
      mul_nonsing_inv_cancel_right _ _ ((isUnit_iff_isUnit_det _).1 S.isUnit_J)]
  have h_gram : (S.rankOneMaps d c)ᴴ * (S.hom T).J * S.rankOneMaps d c = 0 := by
    rw [hom_J, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, h_source]
    rcases h_iso with h_zero | h_zero <;> simp [h_zero]
  rw [← range_mulVecLin]
  rintro _ ⟨γ, rfl⟩ _ ⟨η, rfl⟩
  simp only [mulVecLin_apply, star_mulVec_dotProduct, mulVec_mulVec, ← Matrix.mul_assoc, h_gram,
    zero_mulVec, dotProduct_zero]

omit [WeilData E] in
/-- If `d` is invertible, the maps `dᵢ ⟨cⱼ, ·⟩` span the space of all maps `z cᴴ S.J`. -/
lemma mem_span_rankOneMaps_iff {d : Matrix n' n' E} (hd : IsUnit d) {c : Matrix n q E}
    (γ : n' × n → E) :
    γ ∈ Submodule.span E (Set.range (S.rankOneMaps d c).col) ↔
      ∃ z : Matrix n' q E, matrixToVec (z * (cᴴ * S.J)) = γ := by
  obtain ⟨d, rfl⟩ := hd
  rw [← range_mulVecLin]
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨d.val * vecToMatrix ξ, by simp [kronecker_mulVec_eq_matrixToVec]⟩
  · rintro ⟨z, rfl⟩
    use matrixToVec (d⁻¹.val * z)
    simp [kronecker_mulVec_eq_matrixToVec, ← Matrix.mul_assoc]

/-- For a short pair `d`, `c`, the functional `ℓ` is invariant under the Heisenberg operators of the
span of the maps `dᵢ ⟨cⱼ, ·⟩`. -/
lemma IsShortPair.invariant_span {ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ} {Ψ : (n' × n → 𝔸f E) → ℂ} {x y t : ℝ}
    (h_pair : IsShortPair g h ℓ Ψ d c x y t) :
    ∀ γ ∈ Submodule.span E (Set.range (S.rankOneMaps d c).col), ∀ f : 𝒮 (S.hom T),
      ℓ (ϱ (S.hom T) ((S.hom T).vecAtPoint γ) f) = ℓ f := by
  rw [← range_mulVecLin]
  rintro _ ⟨ξ, rfl⟩ f
  rw [mulVecLin_apply, kronecker_mulVec_eq_matrixToVec, vecAtPoint_hom, ← Matrix.mul_assoc]
  exact h_pair.invariant (d * vecToMatrix ξ) f

end ShortPair

/-- Let `E` be a CM field with Weil data, `a`, `b` automorphic characters, `Ψ` Schwartz–Bruhat above
a set `P` of finite places disjoint from its conjugate, `f₀` in the finite part of the data space of
Hom(S, T), and `l` a natural number. There is `C ≥ 0`, independent of `g`, `h`, `ℓ`, `d`, `c`, `x`,
`y`, `t`, with the following property. Whenever `IsShortPair g h ℓ Ψ d c x y t` holds (the
conditions of the decay estimate at `(g, h)` on rational matrices `d` for `T` and `c` for `S`, the
functional `ℓ`, `Ψ` and reals `x`, `y`, `t`), every Fock-space vector `v` with finite moment
`fockMoment l v` satisfies `‖ℓ (ω (g, h) (v ⊗ Ψ⊗ f₀))‖ ≤ C ‖ℓ ∘ ω (g, h)‖ |t| ^ l ‖v‖_l`, where
`ω = pairWeil S T a b`, `Ψ⊗` is `schrodingerOp` and `v ⊗ ·` is `integrated`. -/
lemma exists_norm_schrodingerOp_le_of_isShortPair {S : Space E n s} {T : Space E n' s'}
    (a b : AutChar E) {P : Set (FinPlace E)} (hP : Set.IsConjDisjoint P)
    (Ψ : (n' × n → 𝔸f E) → ℂ) [IsSchwartzBruhat P Ψ] {f₀ : 𝒮 (S.hom T)}
    (hf₀ : f₀ ∈ finitePart (S.hom T)) (l : ℕ) (p q : Type) [Fintype p] [Fintype q] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : G E s) (h : G E s') (ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ) (d : Matrix n' p E) (c : Matrix n q E)
        (x y t : ℝ),
      IsShortPair g h ℓ Ψ d c x y t →
      ∀ v : fockSpace (realSigns E (homSigns s s')), fockMoment l v ≠ ⊤ →
      ‖ℓ (pairWeil S T a b (g, h) (integrated (S.hom T) v (schrodingerOp (S.hom T) P Ψ f₀)))‖ ≤
        C * ‖ℓ ∘L pairWeil S T a b (g, h)‖ * |t| ^ l * (fockMoment l v).toReal := by
  classical
  -- The maps `dᵢ ⟨cⱼ, ·⟩` are short vectors of Hom(S, T) with isotropic span `Z`, and the mean over
  -- `Z` vanishes at `ω (g, h) (v ⊗ Ψ ⊗ f₀)`, by the support condition or by assumption.
  obtain ⟨C, hC, h_short⟩ :=
    exists_norm_sub_subspaceMean_le (schrodingerOp_mem_finitePart P Ψ hf₀) l (p × q)
  refine ⟨C, hC, fun g h ℓ d c x y t h_pair v hv ↦ ?_⟩
  let k : G E (homSigns s s') := onHom (g, h)
  let Z : Submodule E (n' × n → E) := Submodule.span E (Set.range (S.rankOneMaps d c).col)
  let Λ : 𝒮 (S.hom T) →L[ℂ] ℂ := pairChar a b (g, h) • ℓ
  set F : 𝒮 (S.hom T) := integrated (S.hom T) v (schrodingerOp (S.hom T) P Ψ f₀) with hF
  have hΛ : ℓ ∘L pairWeil S T a b (g, h) = Λ ∘L (S.hom T).ω k := by
    ext f
    simp [Λ, k, pairWeil_apply]
  have h_ball (i : p × q) : (S.rankOneMaps d c).col i ∈ ((S.hom T).move k).latticeBall |t| :=
    (col_rankOneMaps_mem_latticeBall (h_pair.short_target i.1) (h_pair.short_source i.2)).imp_right
      fun h_le ↦ h_le.trans (h_pair.mul_le.trans (le_abs_self t))
  have h_iso : ∀ γ ∈ Z, ∀ η ∈ Z, star γ ⬝ᵥ (S.hom T).J *ᵥ η = 0 :=
    isotropic_span_rankOneMaps h_pair.isotropic
  have h_inv : ∀ γ ∈ Z, ∀ f : 𝒮 (S.hom T), Λ (ϱ (S.hom T) ((S.hom T).vecAtPoint γ) f) = Λ f :=
    fun γ hγ f ↦ by rw [_root_.smul_apply, _root_.smul_apply, h_pair.invariant_span γ hγ f]
  obtain ⟨Λ₀, h_mean⟩ : ∃ Λ₀ : 𝒮 (S.hom T) →L[ℂ] ℂ, ∀ f : 𝒮 (S.hom T),
      Λ₀ f = (S.hom T).subspaceMean Z fun u : n' × n → 𝔸 E ↦ Λ (ϱ (S.hom T) u f) :=
    exists_eq_subspaceMean h_iso h_inv
  have h_zero : Λ₀ ((S.hom T).ω k F) = 0 := by
    rcases h_pair.ne_zero_or_mean_eq_zero with h_ne | h_mean_zero
    · rw [hF, integrated_schrodingerOp]
      refine map_schrodingerOp_eq_zero_of_invariant hP _ _ (ℓ := Λ₀ ∘L (S.hom T).ω k) (fun w f ↦ ?_)
        h_ne _
      rw [ContinuousLinearMap.comp_apply, omega_rho, ← coordMatrix_rankOneMaps]
      exact subspaceMean_rho h_iso h_inv h_mean
        ((mem_adelicPoints_span_col_iff k _).2 ⟨w, rfl⟩) _
    · have := (S.hom T).compactSpace_adelicPoints_quotient Z
      rw [h_mean]
      exact (quotMean_const_mul _ _).trans (mul_eq_zero_of_right _ (h_mean_zero _))
  have h_bound : ‖(Λ - Λ₀) ((S.hom T).ω k F)‖ ≤
      C * ‖Λ ∘L (S.hom T).ω k‖ * |t| ^ l * (fockMoment l v).toReal :=
    h_short k |t| _ Z Λ Λ₀ (abs_nonneg t) h_ball rfl h_iso h_inv h_mean v hv
  rwa [_root_.sub_apply, h_zero, sub_zero, ← ContinuousLinearMap.comp_apply, ← hΛ] at h_bound

/-- Decay estimate. Let `Ψ` be Schwartz–Bruhat above a set `P` of finite places disjoint from its
conjugate, and let `f₀` lie in the finite part of 𝒮(Hom(S,T)), the span of the finite Heisenberg
translates of the vacuum. Then there is C, independent of `v`, `g`, `h`, `ℓ`, `ρ`, `H`, with the
following property: if ρ ≥ 1, H > 0, the moment
‖v‖_{N+A} = `fockMoment (N + A) v` = ∫(1+‖y‖)^{N+A}|v(y)| dy is finite, L = ℓ ∘ ω(g, h)
(ω = `pairWeil S T a b`) satisfies ‖L f‖ ≤ Y ‖f‖ (ρH)^A for all f, and for H > 2 there are rational
matrices d (n' × p), c (n × q) and reals x, y with `IsShortPair g h ℓ Ψ d c x y (Z ρ (2 / H))`, then
‖L(v ⊗ Ψ ⊗ f₀)‖ H^N ≤ C ‖v‖_{N+A} ρ^{N+2A}, where v ⊗ Ψ ⊗ f₀ = ∫ v(y) ϱ(y)(Ψ⊗ f₀) dy. -/
lemma exists_norm_pairWeil_schrodingerOp_mul_pow_le {S : Space E n s} {T : Space E n' s'}
    (a b : AutChar E) {P : Set (FinPlace E)} (hP : Set.IsConjDisjoint P) {Ψ : (n' × n → 𝔸f E) → ℂ}
    [IsSchwartzBruhat P Ψ] {f₀ : 𝒮 (S.hom T)} (hf₀ : f₀ ∈ finitePart (S.hom T)) (N A : ℕ)
    (Y Z : ℝ) :
    ∃ C : ℝ, ∀ (v : fockSpace (realSigns E (homSigns s s'))) (g : G E s) (h : G E s')
        (ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ) (ρ H : ℝ),
      fockMoment (N + A) v ≠ ⊤ → 1 ≤ ρ → 0 < H →
      (∀ f : 𝒮 (S.hom T), ‖ℓ (pairWeil S T a b (g, h) f)‖ ≤ Y * ‖f‖ * (ρ * H) ^ A) →
      (2 < H → ∃ (d : Matrix n' p E) (c : Matrix n q E) (x y : ℝ),
        IsShortPair g h ℓ Ψ d c x y (Z * ρ * (2 / H))) →
      ‖ℓ (pairWeil S T a b (g, h) (integrated (S.hom T) v (schrodingerOp (S.hom T) P Ψ f₀)))‖ *
        H ^ N ≤ C * (fockMoment (N + A) v).toReal * ρ ^ (N + 2 * A) := by
  -- For `H > 2` the short pair gains the factor `|Z ρ (2 / H)| ^ (N + A)` over the norm of `L`. For
  -- `H ≤ 2` the norm of `L` suffices.
  obtain ⟨C, hC, h_pair⟩ := exists_norm_schrodingerOp_le_of_isShortPair a b hP Ψ hf₀ (N + A) p q
  -- `J v = v ⊗ Ψ ⊗ f₀`.
  let J : fockSpace (realSigns E (homSigns s s')) →L[ℂ] 𝒮 (S.hom T) :=
    (integrated (S.hom T)).flip (schrodingerOp (S.hom T) P Ψ f₀)
  let C' : ℝ := C * |Z| ^ (N + A) + ‖J‖
  refine ⟨C' * |Y| * 2 ^ (N + A), fun v g h ℓ ρ H hv hρ hH h_growth h_short ↦ ?_⟩
  let L : 𝒮 (S.hom T) →L[ℂ] ℂ := ℓ ∘L pairWeil S T a b (g, h)
  let m : ℝ := (fockMoment (N + A) v).toReal
  have hm : 0 ≤ m := toReal_nonneg
  have hL : ‖L‖ ≤ |Y| * (ρ * H) ^ A :=
    L.opNorm_le_bound (by positivity) fun f ↦
      (h_growth f).trans (by grw [le_abs_self Y, mul_right_comm])
  have h_gain : ‖L (J v)‖ ≤ C' * ‖L‖ * (ρ * (2 / H)) ^ (N + A) * m := by
    rcases lt_or_ge 2 H with hH_large | hH_small
    · obtain ⟨d, c, x, y, h_dc⟩ := h_short hH_large
      calc ‖L (J v)‖
        _ ≤ C * ‖L‖ * |Z * ρ * (2 / H)| ^ (N + A) * m := h_pair g h ℓ d c x y _ h_dc v hv
        _ = C * |Z| ^ (N + A) * ‖L‖ * (ρ * (2 / H)) ^ (N + A) * m := by
          rw [mul_assoc Z, abs_mul, abs_of_nonneg (a := ρ * (2 / H)) (by positivity)]
          ring
        _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_right (norm_nonneg J)
    · have h_moment : ‖v‖ ≤ m := by
        rw [← toReal_enorm, ← fockMoment_zero]
        refine toReal_mono hv (lintegral_mono fun y ↦ ?_)
        gcongr <;> simp
      have h_one : 1 ≤ (ρ * (2 / H)) ^ (N + A) :=
        one_le_pow₀ (one_le_mul_of_one_le_of_one_le hρ ((one_le_div hH).2 hH_small))
      calc ‖L (J v)‖
        _ ≤ ‖J‖ * ‖L‖ * 1 * ‖v‖ := by
          grw [L.le_opNorm, J.le_opNorm, mul_one, mul_comm ‖J‖ ‖L‖, mul_assoc]
        _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)
  calc ‖L (J v)‖ * H ^ N
    _ ≤ C' * (|Y| * (ρ * H) ^ A) * (ρ * (2 / H)) ^ (N + A) * m * H ^ N := by grw [h_gain, hL]
    _ = C' * |Y| * 2 ^ (N + A) * m * ρ ^ (N + 2 * A) := by
      simp [mul_pow, div_pow, pow_add, two_mul, field]

/-- Data on surjective maps decay rapidly on the target group. Let `Ψ` be Schwartz–Bruhat above a
set `P` of finite places disjoint from its conjugate. Suppose that every map `y` with `Ψ y ≠ 0` has
a right inverse after the ring map `φ` to a nonzero ring (for evaluation at a place `w`: `y` is
surjective at `w`). Then the theta kernel of `v ⊗ Ψ ⊗ vac` at `(g, k)`, times the `N`-th power of
the height of `k`, is at most a constant times a moment of `v` (`fockMoment`) times a power of the
height of `g`. -/
lemma pairTheta_decay_of_onto (S : Space E n s) (T : Space E n' s') (a b : AutChar E)
    (φ : 𝔸f E →+* R) {P : Set (FinPlace E)} (hP : Set.IsConjDisjoint P)
    {Ψ : (n' × n → 𝔸f E) → ℂ} (hΨ : IsSchwartzBruhat P Ψ)
    (h_onto : ∀ y : n' × n → 𝔸f E, Ψ y ≠ 0 → HasLeftInv ((vecToMatrix y).map φ)ᵀ) (N : ℕ) :
    ∃ (B M : ℕ) (C : ℝ), ∀ (v : fockSpace (realSigns E (homSigns s s'))) (g : G E s) (k : G E s'),
      fockMoment M v ≠ ⊤ →
      ‖pairTheta S T a b (integrated (S.hom T) v (schrodingerOp (S.hom T) P Ψ (vacElem (S.hom T))))
          (g, k)‖ * T.height k ^ N ≤
        C * (fockMoment M v).toReal * S.height g ^ B := by
  -- `exists_norm_pairWeil_schrodingerOp_mul_pow_le` for `ℓ = θ`, `ρ = height g`, `H = height k`,
  -- with a short isotropic vector of `T` and a short basis of `S`.
  obtain ⟨Y, A, h_growth⟩ : ∃ (Y : ℝ) (A : ℕ), ∀ (g : G E s) (k : G E s') (f : 𝒮 (S.hom T)),
      ‖θ (S.hom T) (pairWeil S T a b (g, k) f)‖ ≤ Y * ‖f‖ * (S.height g * T.height k) ^ A :=
    (pairThetaKer S T a b).moderate_growth
  obtain ⟨Z, h_basis⟩ : ∃ Z : ℕ, ∀ g : G E s, ∃ c : GL n E, ∀ j : n,
      c.val.col j ∈ (S.move g).latticeBall (Z * S.height g) := S.exists_short_basis_matrix
  have h_pair (g : G E s) (k : G E s') (hk : 2 < T.height k) :
      ∃ (d : Matrix n' Unit E) (c : Matrix n n E) (x y : ℝ),
        IsShortPair g k (θ (S.hom T)) Ψ d c x y (Z * S.height g * (2 / T.height k)) := by
    obtain ⟨d, hd_ne, hd_iso, hd_short⟩ : ∃ d : Matrix n' Unit E, d ≠ 0 ∧ dᴴ * T.J * d = 0 ∧
        ∀ j : Unit, d.col j ∈ (T.move k).latticeBall (2 / T.height k) :=
      T.exists_short_isotropic hk
    obtain ⟨c, hc_short⟩ := h_basis g
    -- The coordinates of the basis form the invertible matrix `(S.x * g)⁻¹ c`.
    let X : GL n (𝔸 E) := g⁻¹.toUnitary.val * (S.x⁻¹ * c.map toAdele)
    have h_coord : S.coordMatrix g c.val = X.val := rfl
    have h_ne (y : n' × n → 𝔸f E) (hy : Ψ y ≠ 0) :
        ((T.coordMatrix k d).map snd)ᴴ * (vecToMatrix y * (S.coordMatrix g c.val).map snd) ≠ 0 := by
      simpa only [h_coord] using T.coordMatrix_mul_ne_zero hd_ne X (h_onto y hy)
    exact ⟨d, c, 2 / T.height k, Z * S.height g,
      { short_target := hd_short
        short_source := hc_short
        mul_le := (mul_comm _ _).le
        isotropic := .inl hd_iso
        invariant := by simp [← vecAtPoint_hom]
        ne_zero_or_mean_eq_zero := .inl h_ne }⟩
  obtain ⟨C, h_decay⟩ := exists_norm_pairWeil_schrodingerOp_mul_pow_le (p := Unit) (q := n) (S := S)
    (T := T)
    (Ψ := Ψ) a b hP vacElem_mem_finitePart N A Y Z
  exact ⟨N + 2 * A, N + A, C, fun v g k hv ↦ h_decay v g k (θ (S.hom T)) (S.height g) (T.height k)
    hv (one_le_height g) (height_pos k) (h_growth g k) (h_pair g k)⟩

/-- Data on injective maps decay rapidly on the source group. Let `Ψ` be Schwartz–Bruhat above a
set `P` of finite places disjoint from its conjugate. Suppose that every map `y` with `Ψ y ≠ 0` has
a left inverse after the ring map `φ` to a nonzero ring (for evaluation at a place `w`: `y` is
injective at `w`). Then the theta kernel of `v ⊗ Ψ ⊗ vac` at `(g, k)`, times the `N`-th power of
the height of `g`, is at most a constant times a moment of `v` (`fockMoment`) times a power of the
height of `k`. -/
lemma pairTheta_decay_of_injective (S : Space E n s) (T : Space E n' s') (a b : AutChar E)
    (φ : 𝔸f E →+* R) {P : Set (FinPlace E)} (hP : Set.IsConjDisjoint P)
    {Ψ : (n' × n → 𝔸f E) → ℂ} (hΨ : IsSchwartzBruhat P Ψ)
    (h_inj : ∀ y : n' × n → 𝔸f E, Ψ y ≠ 0 → HasLeftInv ((vecToMatrix y).map φ)) (N : ℕ) :
    ∃ (B M : ℕ) (C : ℝ), ∀ (v : fockSpace (realSigns E (homSigns s s'))) (g : G E s) (k : G E s'),
      fockMoment M v ≠ ⊤ →
      ‖pairTheta S T a b (integrated (S.hom T) v (schrodingerOp (S.hom T) P Ψ (vacElem (S.hom T))))
          (g, k)‖ * S.height g ^ N ≤
        C * (fockMoment M v).toReal * T.height k ^ B := by
  -- `exists_norm_pairWeil_schrodingerOp_mul_pow_le` for `ℓ = θ`, `ρ = height k`, `H = height g`,
  -- with a short basis of `T` and a short isotropic vector of `S`.
  obtain ⟨Y, A, h_growth⟩ : ∃ (Y : ℝ) (A : ℕ), ∀ (k : G E s') (g : G E s) (f : 𝒮 (S.hom T)),
      ‖θ (S.hom T) (pairWeil S T a b (g, k) f)‖ ≤ Y * ‖f‖ * (T.height k * S.height g) ^ A :=
    (pairThetaKer S T a b).swap.moderate_growth
  obtain ⟨Z, h_basis⟩ : ∃ Z : ℕ, ∀ k : G E s', ∃ d : GL n' E, ∀ j : n',
      d.val.col j ∈ (T.move k).latticeBall (Z * T.height k) := T.exists_short_basis_matrix
  have h_pair (g : G E s) (k : G E s') (hg : 2 < S.height g) :
      ∃ (d : Matrix n' n' E) (c : Matrix n Unit E) (x y : ℝ),
        IsShortPair g k (θ (S.hom T)) Ψ d c x y (Z * T.height k * (2 / S.height g)) := by
    obtain ⟨d, hd_short⟩ := h_basis k
    obtain ⟨c, hc_ne, hc_iso, hc_short⟩ : ∃ c : Matrix n Unit E, c ≠ 0 ∧ cᴴ * S.J * c = 0 ∧
        ∀ j : Unit, c.col j ∈ (S.move g).latticeBall (2 / S.height g) :=
      S.exists_short_isotropic hg
    -- The coordinates of the basis form the invertible matrix `(T.x * k)⁻¹ d`.
    let X : GL n' (𝔸 E) := k⁻¹.toUnitary.val * (T.x⁻¹ * d.map toAdele)
    have h_coord : T.coordMatrix k d.val = X.val := rfl
    have h_ne (y : n' × n → 𝔸f E) (hy : Ψ y ≠ 0) :
        ((T.coordMatrix k d.val).map snd)ᴴ * (vecToMatrix y * (S.coordMatrix g c).map snd) ≠ 0 := by
      simpa only [h_coord] using S.mul_coordMatrix_ne_zero hc_ne X (h_inj y hy)
    exact ⟨d, c, Z * T.height k, 2 / S.height g,
      { short_target := hd_short
        short_source := hc_short
        mul_le := le_rfl
        isotropic := .inr hc_iso
        invariant := by simp [← vecAtPoint_hom]
        ne_zero_or_mean_eq_zero := .inl h_ne }⟩
  obtain ⟨C, h_decay⟩ := exists_norm_pairWeil_schrodingerOp_mul_pow_le (p := n') (q := Unit)
    (S := S) (T := T)
    (Ψ := Ψ) a b hP vacElem_mem_finitePart N A Y Z
  exact ⟨N + 2 * A, N + A, C, fun v g k hv ↦ h_decay v g k (θ (S.hom T)) (T.height k) (S.height g)
    hv (one_le_height k) (height_pos g) (h_growth k g) (h_pair g k)⟩

end KernelDecay

section ModularDataDecay

open Rows NumberField Function Matrix Fock Space IsLocalRing

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (𝔪 : Modulus E)

/-- For a place w dividing 𝔪, the reduction map from O_E/𝔪 to the residue field at w. -/
noncomputable def Rows.modulusResidue {w : FinPlace E} (h : w ∈ 𝔪.places) :
    𝔪.ResidueRing →+* ResField w :=
  Ideal.Quotient.lift 𝔪.ideal (algebraMap (𝓞 E) (ResField w)) fun _ hx ↦
    algebraMap_ResField_eq_zero.2 (h hx)

@[simp]
lemma Rows.modulusResidue_reduction {w : FinPlace E} (h : w ∈ 𝔪.places) (x : Ô E) :
    modulusResidue 𝔪 h (𝔪.reduction x) = reduceAt w x :=
  𝔪.apply_reduction_eq_of_algebraMap x fun a ↦ by simp [modulusResidue]

end

variable {E n n' : Type} [Field E] [CMType E] {𝔪 : Modulus E} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s')

omit [DecidableEq n'] in
/-- Suppose Ψ(y) ≠ 0 forces the matrix of entries of y arranged by e to have a left inverse
modulo 𝔪. Then wherever the adelic lift of Ψ is nonzero, the matrix so arranged is primitive
over O_w at each w dividing 𝔪. -/
lemma Rows.isPrimitiveMatrix_of_liftFn_ne_zero {ι : Type*} {Ψ : (ι → 𝔪.ResidueRing) → ℂ}
    (e : Matrix n' n ι) (h_inv : ∀ y : ι → 𝔪.ResidueRing, Ψ y ≠ 0 → HasLeftInv (e.map y))
    ⦃w : FinPlace E⦄ ⦃x : ι → 𝔸f E⦄ (hw : w ∈ 𝔪.places) (h_ne : 𝔪.liftFn Ψ x ≠ 0) :
    IsPrimitiveMatrix (LocInt w).toSubring ((e.map x).map (evalAt w)) := by
  -- Reduce a left inverse `L` modulo `𝔪` to the residue field at `w` and lift it to the local ring:
  -- the lift times the matrix is invertible, since it is `1` in the residue field.
  obtain ⟨h_int, hΨ⟩ :
      ∃ h : ∀ i : ι, idem 𝔪.places * x i ∈ Ô E, Ψ (fun i ↦ 𝔪.reduction ⟨_, h i⟩) ≠ 0 := by
    simpa only [Modulus.liftFn_apply, dite_ne_right_iff] using h_ne
  obtain ⟨L, hL⟩ := h_inv _ hΨ
  let r : 𝔪.ResidueRing →+* ResidueField (LocInt w) := modulusResidue 𝔪 hw
  let L' : Matrix n n' (LocInt w) := L.map (surjInv residue_surjective ∘ r)
  let Y : Matrix n' n (LocInt w) := e.map fun i ↦ ⟨_, mem_Ô.1 (h_int i) w⟩
  have hL' : L'.map (residue _) = L.map r := Matrix.ext fun _ _ ↦ surjInv_eq ..
  have hY : Y.map (residue _) = (e.map fun i ↦ 𝔪.reduction ⟨_, h_int i⟩).map r :=
    Matrix.ext fun _ _ ↦ (modulusResidue_reduction 𝔪 hw ⟨_, h_int _⟩).symm
  have h_unit : IsUnit (L' * Y) := isUnit_of_mapMatrix (residue _) <| by
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, hL', hY, ← Matrix.map_mul, hL]
    simp
  obtain ⟨U, hU⟩ : ∃ U : Matrix n n (LocInt w), U * (L' * Y) = 1 := h_unit.exists_left_inv
  -- The idempotent `idem 𝔪.places` in the entries of `Y` is `1` at `w`.
  have hY_coe : Y.map (LocInt w).subtype = (e.map x).map (evalAt w) := by
    ext
    simp [Y, hw]
  refine ⟨fun _ _ ↦ idem_mul_mem_Ô.1 (h_int _) w hw, (U * L').map (LocInt w).subtype,
    by simp [IsIntMatrix], ?_⟩
  rw [← hY_coe, ← Matrix.map_mul, Matrix.mul_assoc, hU, Matrix.map_one _ (map_zero _) (map_one _)]

/-- The height on the orthogonal sum of `S` and `T` is at most the product of the heights. -/
lemma Space.height_sum_le (g : G E s) (h : G E s') :
    (S.sum T).height (G.sum (g, h)) ≤ S.height g * T.height h := by
  simp [height, field, firstMinimum_pos, inf_le_firstMinimum_sum.trans']

variable [WeilData E]

/-- The datum is linear in `Ψ`: it is the combination of the data of the indicator functions of
single matrices. -/
lemma modDatum_eq_sum (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))) :
    modDatum S T 𝔪 Ψ v = ∑ x : Matrix n' n 𝔪.ResidueRing,
      Ψ x • modDatum S T 𝔪 (Pi.single x 1) v := by
  have h_sum : Ψ ∘ vecToMatrix = ∑ x, Ψ x • Pi.single x 1 ∘ vecToMatrix := by
    simp [funext_iff, Pi.single_apply]
  simp [modDatum, h_sum]

/-- Let `E` be a CM field with Weil data, `a`, `b` automorphic characters in `AutChar E`, and `Ψ` a
function on `n' × n` matrices modulo `𝔪` supported on left invertible matrices, with some place
dividing `𝔪`. Let `K` be the theta kernel `pairTheta S T a b` of `modDatum S T 𝔪 Ψ v`, the datum
`v ⊗ Ψ ⊗ vac` that is the Fock vector `v` at the infinite places, `Ψ` at the places dividing `𝔪`,
and the vacuum at the other finite places. For each exponent `M` there are `B`, `N`, `C`,
independent of `v`, `g`, `h`, such that for every `v` with finite moment
`fockMoment N v` = ∫ (1 + ‖y‖)^N |v(y)| dy, we have
`‖K (g, h)‖ S.height g ^ M ≤ C (fockMoment N v) T.height h ^ B`. -/
lemma pairTheta_modDatum_decay (a b : AutChar E) {Ψ : Matrix n' n 𝔪.ResidueRing → ℂ}
    (h_ne : Nonempty 𝔪.places) (hΨ : Ψ.support ⊆ {y : Matrix n' n 𝔪.ResidueRing | HasLeftInv y})
    (M : ℕ) :
    ∃ (B N : ℕ) (C : ℝ), ∀ (v : fockSpace (realSigns E (homSigns s s'))) (h : G E s') (g : G E s),
      fockMoment N v ≠ ⊤ →
      ‖pairTheta S T a b (modDatum S T 𝔪 Ψ v) (g, h)‖ * S.height g ^ M ≤
        C * (fockMoment N v).toReal * T.height h ^ B := by
  -- At a place `w` of `𝔪`, the finite adelic maps in the support of the lift of `Ψ` are left
  -- invertible, so `pairTheta_decay_of_injective` applies.
  obtain ⟨w, hw⟩ := h_ne
  have h_inj (y : n' × n → 𝔸f E) (hy : 𝔪.liftFn (Ψ ∘ vecToMatrix) y ≠ 0) :
      HasLeftInv ((vecToMatrix y).map (evalAt w)) := by
    obtain ⟨-, L, -, hL⟩ :=
      isPrimitiveMatrix_of_liftFn_ne_zero (of Prod.mk) (fun _ hx ↦ hΨ hx) hw hy
    exact ⟨L, hL⟩
  obtain ⟨B, N, C, h_decay⟩ := pairTheta_decay_of_injective S T a b (evalAt w)
    𝔪.isConjDisjoint_places (𝔪.isSchwartzBruhat_liftFn (Ψ ∘ vecToMatrix)) h_inj M
  exact ⟨B, N, C, fun v h g hv ↦ h_decay v g h hv⟩

/-- Let `E` be a CM field with Weil data, `a`, `b` automorphic characters in `AutChar E`, and `Ψ` a
function on `n' × n` matrices modulo `𝔪` supported on right invertible matrices (the transpose has a
left inverse), with some place dividing `𝔪`. Let `K` be the theta kernel `pairTheta S T a b` of
`modDatum S T 𝔪 Ψ v`, the datum `v ⊗ Ψ ⊗ vac` that is the Fock vector `v` at the infinite places,
`Ψ` at the places dividing `𝔪`, and the vacuum at the other finite places. For each exponent `M`
there are `B`, `N`, `C`, independent of `v`, `g`, `h`, such that for every `v` with finite moment
`fockMoment N v` = ∫ (1 + ‖y‖)^N |v(y)| dy, we have
`‖K (g, h)‖ T.height h ^ M ≤ C (fockMoment N v) S.height g ^ B`. -/
lemma pairTheta_modDatum_decay_of_rightInv (a b : AutChar E) {Ψ : Matrix n' n 𝔪.ResidueRing → ℂ}
    (h_ne : Nonempty 𝔪.places) (hΨ : Ψ.support ⊆ {y : Matrix n' n 𝔪.ResidueRing | HasLeftInv yᵀ})
    (M : ℕ) :
    ∃ (B N : ℕ) (C : ℝ), ∀ (v : fockSpace (realSigns E (homSigns s s'))) (g : G E s) (h : G E s'),
      fockMoment N v ≠ ⊤ →
      ‖pairTheta S T a b (modDatum S T 𝔪 Ψ v) (g, h)‖ * T.height h ^ M ≤
        C * (fockMoment N v).toReal * S.height g ^ B := by
  -- At a place `w` of `𝔪`, the finite adelic maps in the support of the lift of `Ψ` are right
  -- invertible, so `pairTheta_decay_of_onto` applies.
  obtain ⟨w, hw⟩ := h_ne
  have h_onto (y : n' × n → 𝔸f E) (hy : 𝔪.liftFn (Ψ ∘ vecToMatrix) y ≠ 0) :
      HasLeftInv ((vecToMatrix y).map (evalAt w))ᵀ := by
    obtain ⟨-, L, -, hL⟩ := isPrimitiveMatrix_of_liftFn_ne_zero
      (of fun (j : n) (i : n') ↦ (i, j)) (fun _ hx ↦ hΨ hx) hw hy
    exact ⟨L, hL⟩
  exact pairTheta_decay_of_onto S T a b (evalAt w) 𝔪.isConjDisjoint_places
    (𝔪.isSchwartzBruhat_liftFn (Ψ ∘ vecToMatrix)) h_onto M

end ModularDataDecay

end New

end
