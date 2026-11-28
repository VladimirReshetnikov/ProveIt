import Lib.SiegelWeil.Tower.RealConeIntegral

/-!
# The test vector of the zeta integral

Let `H` be a hyperbolic plane over the CM field `E`. At each infinite place the Fock space
`New.PairFock` of `Hom(H, H)` has two positive coordinates, the diagonal ones. The test vector is
the Fock vector of the product of their `m w`-th powers. Its cone integrand for the pair `(H, H)`
over `(0, 0)` is the vacuum times the integrand of a zeta integral: the test function
`∏ conj (a w) ^ (2 m w) exp (-|a w|²)` times a character and a power of `|a|`.

* `New.Exchange.tateVector`: the test vector.
* `New.Exchange.realPairWeil_tateVector`: the maximal compact subgroup of the target group fixes it.
* `New.Exchange.coneIntegrand_tateVector`: its cone integrand, in either model, is an explicit
  positive function times the vacuum.

Notions from other files:
* `New.Fock.polyVector`: the Fock vector x ↦ P(ζ(x))·exp(−|x|²/2) of a polynomial P, where ζ(x)_i is
  x̄_i at positive and x_i at negative coordinates.
* `New.Fock.MixedModel`: a decomposition y = La + Iw + Kb of the large space, with a map `slice a`
  from the large Fock space to the small one.
* `Splitting.IsAdapted 1 b`: the adelic frame `D.frameAt 1 b = (l b*⁻¹, k b, ι)` of a splitting
  `D` has orthonormal columns at the infinite places and integral entries at the finite ones.
* `New.Exchange.coneIntegrand`: the integrand of the cone integral, `lineTermReal A X β a` applied
  to the translate of a vector by the compact part, times a character and a power of `|a|`.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.

Part of a known result: analytic continuation and functional equation of Hecke `L`-functions. See
`Lib.SiegelWeil.Tower.FunctionalEquation`. Up to a scaling of the variable the test function is that
of J. Tate, Fourier analysis in number fields and Hecke's zeta-functions (thesis, 1950), §2.5.
-/

noncomputable section

namespace New.Exchange

open Matrix MeasureTheory Complex WeilData Fock Space Splitting MvPolynomial Finset Fintype
  Heisenberg IsVacuum MixedModel Prod

open NumberField (InfinitePlace)

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] {s : n → ℤˣ} {s' : n' → ℤˣ}
  {W : Space E n s} {W' : Space E n' s'} {D : W.Splitting W' r}

section Frame

variable {b : GL r (𝔸 E)}

omit [WeilData E] in
/-- Let `D` split `W` as `W'` plus hyperbolic planes indexed by `r`, and let it be adapted at `1`
to `b`: at each infinite place `w` the frame `D.frameAt 1 b` of `W` has orthonormal columns (and it
is integral at the finite places). This frame is square, so its rows are orthonormal as well. -/
lemma frameAt_real_mul_conjTranspose (h : D.IsAdapted 1 b) (w : InfinitePlace E) :
    atRealPlace (D.frameAt 1 b) w * (atRealPlace (D.frameAt 1 b) w)ᴴ = 1 := by
  obtain ⟨h_orthonormal, -⟩ : IsOrthoIntegral (D.frameAt 1 b) := h
  exact (mul_eq_one_comm_of_card_eq ((r ⊕ r) ⊕ n') n ℂ (by simp +arith [D.card_eq])).1
    (h_orthonormal w)

omit [WeilData E] in
/-- Let `D` split `W` as `W'` plus hyperbolic planes indexed by `r`, with an adapted frame
`F = D.frameAt 1 b`. At an infinite place `w`, with `S` the diagonal matrix of the signs `s` of
`W`, we have `S F = F T`, where `T` is the block diagonal matrix of the exchange of the two lines of
each plane and of the signs `s'` of `W'`. -/
lemma signMatrix_mul_frameAt_real (h : D.IsAdapted 1 b) (w : InfinitePlace E) :
    signMatrix s * atRealPlace (D.frameAt 1 b) w = atRealPlace (D.frameAt 1 b) w *
      fromBlocks (n := r ⊕ r) (fromBlocks 0 1 1 0) 0 0 (signMatrix s') := by
  have h_gram : (atRealPlace (D.frameAt 1 b) w)ᴴ * signMatrix s * atRealPlace (D.frameAt 1 b) w =
      fromBlocks (n := r ⊕ r) (fromBlocks 0 1 1 0) 0 0 (signMatrix s') := by
    rw [gram_atRealPlace, gram_frameAt]
    simp [stdForm, signMatrix, fromBlocks_map]
  simp [← h_gram, ← Matrix.mul_assoc, frameAt_real_mul_conjTranspose h]

omit [Fintype n] in
/-- The projection `posProj s` on the coordinates of sign `1` is `(1 + signMatrix s) / 2`, where
`signMatrix s` is the diagonal matrix of the signs. -/
lemma posProj_eq : posProj s = (2⁻¹ : ℂ) • (1 + signMatrix s) := by
  rw [signMatrix_eq_posProj_sub]
  module

/-- The vector `L a + I z + K c` with coordinates `a`, `z`, `c` in the directions `L`, `I`, `K` of
the real mixed model of a splitting `D` adapted at `1` to `b`. -/
def framePoint (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ) (z : InfinitePlace E × n' → ℂ)
    (c : InfinitePlace E × r → ℂ) : InfinitePlace E × n → ℂ :=
  h.mixedModel.L *ᵥ a + h.mixedModel.I *ᵥ z + h.mixedModel.K *ᵥ c

/-- Let `D.frameAt 1 b` be an adapted frame. The point `framePoint h a z c`, which is
`L a + I z + K c`, is the image under the infinite components `realMatrix` of this frame of its
three blocks of coordinates, put side by side at each place in the order `a`, `c`, `z`. -/
lemma framePoint_eq_mulVec (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (z : InfinitePlace E × n' → ℂ) (c : InfinitePlace E × r → ℂ) :
    framePoint h a z c = realMatrix (D.frameAt 1 b) *ᵥ
      fun ((w, i) : InfinitePlace E × ((r ⊕ r) ⊕ n')) ↦
        (vecToMatrix a w ⊕ᵥ vecToMatrix c w ⊕ᵥ vecToMatrix z w) i := by
  ext ⟨w, i⟩
  simp [vecToMatrix, framePoint, IsAdapted.mixedModel, mulVec, dotProduct, sum_prod_type,
    Splitting.frameAt, realMatrix, blockDiagonal, G.adeleMatrix_one, add_right_comm]

/-- At the infinite place `w`, the point `framePoint h a z c`, which is `L a + I z + K c`, is the
image under the component at `w` of the adapted frame `D.frameAt 1 b` of the three blocks of
coordinates at `w`. -/
lemma framePoint_apply (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (z : InfinitePlace E × n' → ℂ) (c : InfinitePlace E × r → ℂ) (w : InfinitePlace E) (l : n) :
    framePoint h a z c (w, l) =
      (atRealPlace (D.frameAt 1 b) w *ᵥ (vecToMatrix a w ⊕ᵥ vecToMatrix c w ⊕ᵥ vecToMatrix z w))
        l := by
  rw [framePoint_eq_mulVec h]
  simp [realMatrix, mulVec, dotProduct, blockDiagonal, sum_prod_type]

/-- The projection `posProj` on the positive coordinates sends the point `L a + I z + K c`
(`framePoint h a z c`) to the point with `a` and `c` replaced by their midpoint and `z` by its
positive projection, because the matrix of signs exchanges `L` and `K`. -/
lemma posProj_mulVec_framePoint (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (z : InfinitePlace E × n' → ℂ) (c : InfinitePlace E × r → ℂ) :
    posProj (realSigns E s) *ᵥ framePoint h a z c =
      framePoint h (midpoint ℂ a c) (posProj (realSigns E s') *ᵥ z) (midpoint ℂ a c) := by
  ext ⟨w, l⟩
  let T : Matrix ((r ⊕ r) ⊕ n') ((r ⊕ r) ⊕ n') ℂ :=
    fromBlocks (n := r ⊕ r) (fromBlocks 0 1 1 0) 0 0 (signMatrix s')
  let x : (r ⊕ r) ⊕ n' → ℂ := vecToMatrix a w ⊕ᵥ vecToMatrix c w ⊕ᵥ vecToMatrix z w
  -- At the place `w` the projection `(1 + signMatrix s) / 2` is `(1 + T) / 2` in the frame.
  have h_mul : posProj s * atRealPlace (D.frameAt 1 b) w =
      atRealPlace (D.frameAt 1 b) w * (2⁻¹ : ℂ) • (1 + T) := by
    simp [posProj_eq, T, Matrix.add_mul, Matrix.mul_add, signMatrix_mul_frameAt_real h]
  have h_half : ((2⁻¹ : ℂ) • (1 + T)) *ᵥ x =
      (vecToMatrix (midpoint ℂ a c) w ⊕ᵥ vecToMatrix (midpoint ℂ a c) w) ⊕ᵥ
        vecToMatrix (posProj (realSigns E s') *ᵥ z) w := by
    ext ((i | i) | i) <;> simp [T, x, vecToMatrix, midpoint_eq_smul_add, posProj_eq, signMatrix,
      smul_mulVec, add_mulVec, fromBlocks_mulVec, mulVec_diagonal, mul_add, add_comm]
  calc (posProj (realSigns E s) *ᵥ framePoint h a z c) (w, l)
      = ((posProj s * atRealPlace (D.frameAt 1 b) w) *ᵥ x) l := by
        rw [← mulVec_mulVec, posProj, posProj, mulVec_diagonal, mulVec_diagonal, framePoint_apply h]
    _ = framePoint h (midpoint ℂ a c) (posProj (realSigns E s') *ᵥ z) (midpoint ℂ a c) (w, l) := by
        rw [h_mul, ← mulVec_mulVec, h_half, framePoint_apply h]

/-- The matrix of signs exchanges `L` and `K`, so on a point `L a + I z + K a`
(`framePoint h a z a`) it acts through the middle coordinate `z` only. -/
lemma signMatrix_mulVec_framePoint (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (z : InfinitePlace E × n' → ℂ) :
    signMatrix (realSigns E s) *ᵥ framePoint h a z a =
      framePoint h a (signMatrix (realSigns E s') *ᵥ z) a := by
  simp only [signMatrix_eq_posProj_sub, sub_mulVec, one_mulVec, posProj_mulVec_framePoint h,
    midpoint_self]
  simp only [framePoint, mulVec_sub]
  abel

/-- The difference of two points `L a + I z + K c` (`framePoint h a z c`) is the point of the
differences of their coordinates. -/
lemma framePoint_sub (h : D.IsAdapted 1 b) (a a' c c' : InfinitePlace E × r → ℂ)
    (z z' : InfinitePlace E × n' → ℂ) :
    framePoint h a z c - framePoint h a' z' c' = framePoint h (a - a') (z - z') (c - c') := by
  simp only [framePoint, mulVec_sub]
  abel

/-- The columns of `L`, `K` and `I` of an adapted splitting are orthonormal, so the inner product of
the points `L a + I u + K a` and `L c + I z + K c` (both `framePoint`) is `2 ⟨a, c⟩ + ⟨u, z⟩`. -/
lemma star_framePoint_dotProduct (h : D.IsAdapted 1 b) (a c : InfinitePlace E × r → ℂ)
    (u z : InfinitePlace E × n' → ℂ) :
    star (framePoint h a u a) ⬝ᵥ framePoint h c z c = 2 * star a ⬝ᵥ c + star u ⬝ᵥ z := by
  rw [framePoint_eq_mulVec h, framePoint_eq_mulVec h, star_mulVec_dotProduct, mulVec_mulVec,
    conjTranspose_realMatrix_mul_self _ h, one_mulVec]
  -- It remains to split the sum over the three blocks of coordinates.
  simp [vecToMatrix, sum_prod_type, sum_add_distrib, two_mul, dotProduct]

/-- A vector `y` in the positive coordinates (fixed by `posProj`) is a point `L c + I z + K c`
(`framePoint`) whose middle coordinate `z` is positive. -/
lemma exists_framePoint_eq_of_posProj_eq (h : D.IsAdapted 1 b) {y : InfinitePlace E × n → ℂ}
    (hy : posProj (realSigns E s) *ᵥ y = y) :
    ∃ (c : InfinitePlace E × r → ℂ) (z : InfinitePlace E × n' → ℂ),
      framePoint h c (posProj (realSigns E s') *ᵥ z) c = y := by
  obtain ⟨A, Z, C, h_span⟩ := h.mixedModel.exists_decomp
  -- In the coordinates of `y` in the frame, projecting takes the midpoint of those on `L` and `K`.
  have h_decomp : framePoint h (A *ᵥ y) (Z *ᵥ y) (C *ᵥ y) = y := h_span y
  exact ⟨midpoint ℂ (A *ᵥ y) (C *ᵥ y), Z *ᵥ y, by rw [← posProj_mulVec_framePoint h, h_decomp, hy]⟩

/-- Let `y` be a vector in the positive coordinates, and translate the vacuum (the Gaussian) by it
with the Heisenberg operator `realHeisenbergOp y`. The value at `u` of the slice at `a` of this
translate, in the mixed model of the adapted splitting, is the value of the translate at the point
`framePoint h (-a) u (-a)`, that is `-L a + I u - K a`. -/
lemma slice_realHeisenbergOp_vacElem_apply (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (u : InfinitePlace E × n' → ℂ) {y : InfinitePlace E × n → ℂ}
    (hy : posProj (realSigns E s) *ᵥ y = y) :
    h.mixedModel.slice a (realHeisenbergOp y vacElem) u =
      (realHeisenbergOp y vacElem : fockSpace (realSigns E s)) (framePoint h (-a) u (-a)) := by
  obtain ⟨c, z₀, rfl⟩ := exists_framePoint_eq_of_posProj_eq h hy
  set z : InfinitePlace E × n' → ℂ := posProj (realSigns E s') *ᵥ z₀
  have h_slice : h.mixedModel.slice a (realHeisenbergOp (framePoint h c z c) vacElem) u =
      (realHeisenberg 1).β (a + (a + c)) c * cexp (-(star (a + c) ⬝ᵥ (a + c))) *
        ((realHeisenberg (realSigns E s')).β z u * realVac (u - z)) := by
    rw [framePoint, slice_realHeisenbergOp, two_nsmul, add_assoc a a c]
    simp [slice_vac, IsVacuum.smul_apply, heisenbergOp_apply, vacElem_apply, mul_assoc]
  -- Both sides are exponentials. It remains to compare the exponents.
  rw [h_slice, heisenbergOp_apply, vacElem_apply, framePoint_sub]
  simp only [realHeisenberg, realVac, signMatrix_mulVec_framePoint h, star_framePoint_dotProduct h,
    signMatrix_one, one_mulVec, ← exp_add]
  congr 1
  simp only [star_add, star_sub, star_neg, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub, neg_dotProduct, dotProduct_neg]
  ring

/-- Let `e` split the coordinates `ι`, with signs `ε`, into `ι₁` and `ι₂`. The external product
`realBoxProd` of the translate of the vacuum by `y` with the vacuum is the translate of the vacuum
by the vector `(y, 0)`. -/
lemma realBoxProd_realHeisenbergOp_vacVector {ι ι₁ ι₂ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] {ε : ι → ℤˣ} {ε₁ : ι₁ → ℤˣ}
    {ε₂ : ι₂ → ℤˣ} {e : ι₁ ⊕ ι₂ ≃ ι} (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) (y : ι₁ → ℂ) :
    realBoxProd he (realHeisenbergOp y vacVector) vacVector =
      realHeisenbergOp ((realCoordSum he).equiv (y, 0)) vacVector := by
  show (realCoordSum he).tmul (heisenbergOp y vacElem) vacElem =
    heisenbergOp ((realCoordSum he).equiv (y, 0)) vacElem
  simp [← OrthogonalSum.tmul_vacElem (realCoordSum he), OrthogonalSum.heisenbergOp_tmul]

/-- Let `P` be a polynomial in the positive coordinates and `polyVector` its Fock vector
`P(ζ) exp(-|·|² / 2)`. In the mixed model of an adapted splitting, the value at `u` of the slice at
`a` of this vector is its value at the point `framePoint h (-a) u (-a)`, that is
`-L a + I u - K a`. -/
lemma slice_polyVector_apply (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (u : InfinitePlace E × n' → ℂ)
    (P : MvPolynomial {i : InfinitePlace E × n // realSigns E s i = 1} ℂ) :
    h.mixedModel.slice a (polyVector (realSigns E s) (rename Subtype.val P)) u =
      polyVector (realSigns E s) (rename Subtype.val P) (framePoint h (-a) u (-a)) := by
  -- Both sides are bounded functionals on the Fock space of the positive coordinates, tensored
  -- with the vacuum. So it is enough to treat the translates of the vacuum by positive vectors.
  have h_signs : realSigns E s ∘ Equiv.sumCompl (fun i ↦ realSigns E s i = 1) =
      (realSigns E s ∘ Subtype.val) ⊕ᵥ (realSigns E s ∘ Subtype.val) :=
    Sum.comp_elim (realSigns E s) Subtype.val Subtype.val
  let Φ : fockSpace (fun i : {i // realSigns E s i = 1} ↦ realSigns E s i) →L[ℂ] ℂ :=
    (valueAt u ∘L h.mixedModel.slice a - valueAt (framePoint h (-a) u (-a))) ∘L
      (realBoxProd h_signs).flip Fock.vacVector
  have h_functional : Φ = 0 := by
    refine hom_ext fun y ↦ ?_
    have h_positive : posProj (realSigns E s) *ᵥ (realCoordSum h_signs).equiv (y, 0) =
        (realCoordSum h_signs).equiv (y, 0) := by
      ext i
      by_cases hi : realSigns E s i = 1 <;> simp [realCoordSum, posProj, mulVec_diagonal, hi]
    simp [Φ, valueAt_apply, realBoxProd_realHeisenbergOp_vacVector,
      slice_realHeisenbergOp_vacElem_apply h a u h_positive]
  have h_box : realBoxProd h_signs
      (polyVector (fun i : {i // realSigns E s i = 1} ↦ realSigns E s i) P) vacVector =
      polyVector (realSigns E s) (rename Subtype.val P) := by
    simp [← polyVector_one, realBoxProd_polyVector, Function.comp_def]
  simpa [Φ, h_box, sub_eq_zero, valueAt_apply] using DFunLike.congr_fun h_functional
    (polyVector (fun i : {i // realSigns E s i = 1} ↦ realSigns E s i) P)

end Frame

/-- The test vector on `Hom(W, W)`, for a space `W` with signs `s` (the signs on `Hom(W, W)` are
`homSigns s s`, and the diagonal coordinates are positive for them): the Fock vector of the product,
over the infinite places `w`, of the `m w`-th powers of the diagonal variables at `w`. -/
def tateVector (s : n → ℤˣ) (m : InfinitePlace E → ℕ) : PairFock E s s :=
  polyVector (realSigns E (homSigns s s)) (∏ w : InfinitePlace E, ∏ i : n, X (w, i, i) ^ m w)

omit [WeilData E] in
/-- All weighted norms of the test vector are finite (`IsSchwartzVector`). -/
lemma isSchwartzVector_tateVector (s : n → ℤˣ) (m : InfinitePlace E → ℕ) :
    IsSchwartzVector (tateVector s m) :=
  fun N ↦ fockMoment_polyVector_ne_top N _

omit [WeilData E] in
/-- Let the signs `s` take each of the values `1` and `-1` once. Let the components of `g`, a point
of the archimedean unitary group `GInf E s`, preserve the lines of each sign (`blockDiagAlg s` is
the algebra of matrices commuting with the signs). Then `(1, g)`, acting in the real Weil
representation `realPairWeil` of the pair with weight `0` on the source and
`targetWeight n m = 1 - m` on the target, fixes the test vector, which is the Fock vector of
`∏ w, ∏ i, X (w, i, i) ^ m w`. -/
lemma realPairWeil_tateVector (hs : Function.Bijective s) (m : InfinitePlace E → ℕ) {g : GInf E s}
    (hg : ∀ w : InfinitePlace E, (g w : Matrix n n ℂ) ∈ blockDiagAlg s) :
    realPairWeil (targetWeight n fun w : InfinitePlace E ↦ m w) 0 (1, g) (tateVector s m) =
      tateVector s m := by
  -- Each `g w` is diagonal. It multiplies the polynomial by `det (g w) ^ m w`, and the character of
  -- the vacuum is the inverse of this number.
  classical
  have h_diag (w : InfinitePlace E) : (g w : Matrix n n ℂ).IsDiag :=
    fun i j hij ↦ mem_blockDiagAlg.1 (hg w) i j (hs.injective.ne hij)
  have h_det (w : InfinitePlace E) :
      ∏ i : n, (g w : Matrix n n ℂ) i i = (g w : Matrix n n ℂ).det := by
    simpa using congrArg det (h_diag w).diagonal_diag
  have h_column (w : InfinitePlace E) (i : n) :
      ∑ j, (g w : Matrix n n ℂ) j i • (X (w, j, i) : MvPolynomial (InfinitePlace E × n × n) ℂ) =
        (g w : Matrix n n ℂ) i i • X (w, i, i) :=
    Fintype.sum_eq_single i fun j hj ↦ by rw [h_diag w hj, zero_smul]
  have h_exponent (w : InfinitePlace E) (σ : ℤˣ) :
      targetWeight n (fun w ↦ m w) w - Nat.card {i : n // s i = -σ} = -m w := by
    rw [Nat.card_eq_one_iff_exists.2 (by simpa [ExistsUnique] using hs.existsUnique (-σ)),
      targetWeight, card_of_bijective hs, card_units_int]
    simp
  have h_character (w : InfinitePlace E) :
      ∏ σ ∈ ({1, -1} : Finset ℤˣ), principalMinor (g w) (fun i ↦ s i = σ) ^ (-m w : ℤ) =
        ((g w : Matrix n n ℂ).det ^ m w)⁻¹ := by
    rw [det_eq_prod_principalMinor (hg w), UnitsInt.univ, prod_zpow, _root_.zpow_neg, zpow_natCast]
  rw [tateVector, realPairWeil_polyVector _ _ (fun w ↦ by simp) hg, ← map_smul]
  simp only [Pi.one_apply, OneMemClass.coe_one, Units.val_one, principalMinor_one, _root_.one_zpow,
    mul_one, h_exponent, h_character]
  -- The substitution scales the diagonal variable `X (w, i, i)` by the entry `g w i i`, so it
  -- multiplies the polynomial by `∏ w, det (g w) ^ m w`.
  have h_scaled : ∏ w : InfinitePlace E, ∏ i : n,
      ((g w : Matrix n n ℂ) i i • (X (w, i, i) : MvPolynomial (InfinitePlace E × n × n) ℂ)) ^ m w =
        (∏ w, (g w : Matrix n n ℂ).det ^ m w) • ∏ w, ∏ i : n, X (w, i, i) ^ m w := by
    simp [smul_pow, prod_smul, prod_pow, h_det]
  simp [Matrix.one_apply, h_column, h_scaled, prod_ne_zero_iff, (g _ : GL n ℂ).det_ne_zero]

variable [IsEmpty n] (A : W'.Splitting W Unit) [IsBaseAdapted A]

/-- Let `A` be a base-adapted splitting (`IsBaseAdapted A`, which makes each
`lineTermSplitting A A β` adapted at `1`) of `W'` along a line over a space `W` of rank zero, and
take the frame of `lineTermSplitting A A β`, the splitting of `Hom(W', W')` over `Hom(W, W)` for the
model `β` (one of the two sides of Poisson's formula on the line). Let `x` be `a` on the line (the
right summand of the index set `LineIndex`) and `0` elsewhere. The diagonal entries at the infinite
place `w` of the point `framePoint h (-x) u (-x)`, for the adapted frame `h` of this splitting, are
`-a w`. -/
lemma framePoint_lineTermSplitting_diag (β : Bool) (a : InfinitePlace E → ℂ)
    (u : InfinitePlace E × n × n → ℂ) (w : InfinitePlace E) (i : n') :
    let x : InfinitePlace E × LineIndex n n → ℂ :=
      fun p : InfinitePlace E × LineIndex n n ↦ a p.1 * p.2.isRight.toNat
    framePoint (isAdapted_lineTermSplitting A A β) (-x) u (-x) (w, i, i) = -a w := by
  -- In either model the two columns for the line are the projections of `W'` on `k` and on `l`.
  -- Their sum is the identity, because `W = 0`.
  intro x
  have h_real : (A.kAdelic i ()).1 w * (A.kCoord () i).1 w +
      (A.lAdelic i ()).1 w * (A.lCoord () i).1 w = 1 := by
    simpa [Matrix.mul_apply, univ_eq_empty] using
      congrArg (fun M ↦ evalInf w (M i i)) A.sum_frame_mul_coord_eq_one
  -- A diagonal entry of the point sees only the two columns of the line, and in either model these
  -- are the products of frame and coordinate on `k` and on `l`.
  have h_value : framePoint (isAdapted_lineTermSplitting A A β) (-x) u (-x) (w, i, i) =
      -((A.kAdelic i ()).1 w * (A.kCoord () i).1 w * a w) +
        -((A.lAdelic i ()).1 w * (A.lCoord () i).1 w * a w) := by
    rw [framePoint_eq_mulVec, frameAt_lineTermSplitting]
    cases β <;> simp [x, realMatrix, mulVec, dotProduct, blockDiagonal, sum_prod_type, vecToMatrix,
      univ_eq_empty, add_comm]
  linear_combination h_value - a w * h_real

/-- Let `W` have rank zero (`n` is empty), let `W'` have rank two (`hn`), and let `A` be a
base-adapted splitting of `W'` over `W` along one line (`IsBaseAdapted A`, so that
`lineTermSplitting A A β` is adapted at `1`). For either of the two models `β` of Poisson's formula
on the line, the real line term `lineTermReal A A β a` is the slice, in the real mixed model of
`Hom(W', W')` over `Hom(W, W)`, at the point with coordinates `a` on the line and `0` elsewhere. It
sends the test vector `tateVector s' m` to `exp (-∑ |a w|²) ∏ conj (a w) ^ (2 m w)` times the
vacuum, where `tateVector s' m` is the Fock vector of the product over the infinite places `w` of
the `m w`-th powers of the diagonal variables at `w`. -/
lemma lineTermReal_tateVector (hn : Fintype.card n' = 2) (m : InfinitePlace E → ℕ) (β : Bool)
    (a : InfinitePlace E → ℂ) :
    lineTermReal A A β a (tateVector s' m) =
      (Real.exp (-∑ w : InfinitePlace E, ‖a w‖ ^ 2) *
        ∏ w : InfinitePlace E, star (a w) ^ (2 * m w) : ℂ) • vacVector := by
  -- The map is the slice at `x` in an adapted frame. So on polynomials in the positive coordinates,
  -- among them the diagonal ones, it evaluates at the point `y`.
  ext u
  let x : InfinitePlace E × LineIndex n n → ℂ :=
    fun p : InfinitePlace E × LineIndex n n ↦ a p.1 * p.2.isRight.toNat
  let y : InfinitePlace E × n' × n' → ℂ :=
    framePoint (isAdapted_lineTermSplitting A A β) (-x) u (-x)
  have h_eval (P : MvPolynomial
      {i : InfinitePlace E × n' × n' // realSigns E (homSigns s' s') i = 1} ℂ) :
      lineTermReal A A β a (polyVector _ (rename Subtype.val P)) u =
        (polyVector _ (rename Subtype.val P) : PairFock E s' s') y := by
    rw [lineTermReal]
    exact slice_polyVector_apply (isAdapted_lineTermSplitting A A β) x u P
  -- The polynomial `1` gives the vacuum, so this compares the Gaussians at `y` and at `u`.
  have h_vac : realVac y = Real.exp (-∑ w : InfinitePlace E, ‖a w‖ ^ 2) * realVac u := by
    -- The slice of the vacuum at `x` is `exp (-|x|²)` times the vacuum, and `|x|² = ∑ |a w|²`.
    simpa [lineTermReal, star_dotProduct_self_eq_sum, slice_vac, x, sum_prod_type, mul_pow,
      vacElem_apply,
      IsVacuum.smul_apply] using (h_eval 1).symm
  have h_pos (w : InfinitePlace E) (i : n') : realSigns E (homSigns s' s') (w, i, i) = 1 := by
    simp [pairSign]
  have h_coord (w : InfinitePlace E) (i : n') :
      holomorphicCoord (realSigns E (homSigns s' s')) y (w, i, i) = -star (a w) := by
    simp [holomorphicCoord_eq, h_pos, y, x, framePoint_lineTermSplitting_diag]
  calc lineTermReal A A β a (tateVector s' m) u
      = tateVector s' m y := by
        simpa only [tateVector, map_prod, map_pow, rename_X]
          using h_eval (∏ w, ∏ i, X ⟨(w, i, i), h_pos w i⟩ ^ m w)
    _ = ((Real.exp (-∑ w, ‖a w‖ ^ 2) * ∏ w, star (a w) ^ (2 * m w) : ℂ) •
          (vacVector : PairFock E s s)) u := by
      simp only [tateVector, polyVector_apply, map_prod, map_pow, eval_X, h_coord, prod_const,
        card_univ, hn, pow_right_comm _ _ 2, neg_sq, pow_mul, h_vac, IsVacuum.smul_apply,
        vacElem_apply]
      ring

/-- Let `A` be a base-adapted splitting (`IsBaseAdapted A`, so each `lineTermSplitting A A β` is
adapted at `1`) of `W'` along a line over a space of rank zero, and let the signs `s'` of `W'` take
each of the values `1` and `-1` once. The cone integrand `coneIntegrand` at `p = (κ, a)` is the
phase `∏ (a w / |a w|) ^ (2 m w)` times `|a| ^ z` times the line term at `a` of the translate by
`κ`; here `κ` is in the maximal compact group and `|a|` is the module of the idele with components
`a w` at infinity and `1` at the finite places. For the test vector `tateVector s' m`, the Fock
vector of `∏ X (w, i, i) ^ m w`, in either of the two models `β` of Poisson's formula on the line
and for every real exponent `z`, it is the vacuum times the number
`exp (-∑ |a w|²) |a| ^ z ∏ |a w| ^ (2 m w)`. -/
theorem coneIntegrand_tateVector (hs : Function.Bijective s') (m : InfinitePlace E → ℕ) (β : Bool)
    (z : ℝ) (p : maxCompact E s' × (InfinitePlace E → ℂ)ˣ) :
    coneIntegrand A A (fun w : InfinitePlace E ↦ m w) β z (tateVector s' m) p =
      (Real.exp (-∑ w : InfinitePlace E, ‖p.2.val w‖ ^ 2) * ideleAbs (realIdele p.2) ^ z *
        ∏ w : InfinitePlace E, normSq (p.2.val w) ^ m w) • vacVector := by
  -- The compact part `κ` fixes the test vector, and the phase in `coneIntegrand` turns
  -- `conj (a w) ^ (2 * m w)` into `normSq (a w) ^ m w`.
  obtain ⟨κ, a⟩ := p
  have h_phase (w : InfinitePlace E) :
      (a.val w / ‖a.val w‖) ^ (2 * m w : ℤ) * star (a.val w) ^ (2 * m w) =
        (normSq (a.val w) ^ m w : ℝ) := by
    have h_sq : (a.val w / ‖a.val w‖) ^ 2 * star (a.val w) ^ 2 = normSq (a.val w) := by
      rw [← mul_pow, div_mul_eq_mul_div, star_def, mul_conj', normSq_eq_norm_sq, ofReal_pow]
      field_simp [piUnits_val_apply_ne_zero]
    rw [ofReal_pow, ← h_sq, mul_pow, ← pow_mul, ← pow_mul]
    norm_cast
  rw [coneIntegrand, realPairWeil_tateVector hs m fun w ↦ mem_maxCompactU.1 (κ.prop.1 w trivial),
    lineTermReal_tateVector A ((card_of_bijective hs).trans card_units_int), smul_smul,
    ← Complex.coe_smul]
  congr 1
  -- It remains to absorb the phase at each place.
  simp only [ofReal_mul, ofReal_prod, ← h_phase, prod_mul_distrib]
  ring

end New.Exchange

end
