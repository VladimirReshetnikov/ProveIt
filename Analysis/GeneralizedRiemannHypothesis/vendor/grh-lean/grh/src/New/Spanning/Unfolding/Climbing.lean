import Lib.Adelic.QuotientMeasure.UnfoldingInStages
import New.Spanning.Unfolding.AmplitudeSums

/-!
# Residue lifts, lattice charts and common flag vectors: which filling terms contribute

This file sorts the terms of the second moment of the filling theorem and shows which of them
contribute. Common vectors of two flags are moved up the flags by elementary linear algebra.

## Main definitions and results

* `New.Filling.mem_congruenceGL_iff_isIntMatrix_scaleAt`: for an integral idele `p` that is a unit
  at one of each pair of conjugate places, a unitary `k` is integral with row `o` congruent to that
  of `1` modulo `p` iff `k - 1` stays integral after dividing row `o` by `p` and column `o` by `p̄`.
* `New.Filling.inclHFin_mem_latticeStabilizer_iff`: `S.inclHFin k` is integral iff `k` is integral
  and its row `k₀` is congruent to that of `1` modulo `S.piN`.
* `New.Filling.MeetsAt`, `New.Filling.fixer`, `New.Filling.IsOpenElement`,
  `New.Filling.InScalarCoset`: the meeting places, and the subsets of the finite group.
* `New.Filling.amplitudeSum_eq_zero_of_not_charsAgree`: a stable set of terms none of which agrees
  contributes `0`.
* `New.Filling.mul_star_eq_and_pairOccursAt_of_le`,
  `New.Filling.exists_pairOccursInColumnsAt_top_of_meetsAt`: when the characters agree, the leading
  coefficients of a common vector of two flags have equal norms and recur at all higher indices over
  `E`; modulo a place above `M` where the flags meet, some pair not both zero occurs at the top
  index.
* `New.Filling.CharsAgree.exists_hasCellRank`: a term with agreeing characters and discriminant `0`
  has a cell rank.

Notions from other files:
* `S : New.Filling E 𝔰`: the filling data over the CM field `E`; `S.chosenPlaces i` is a set of
  places of `E` of norm the prime `S.levelPrime i` (`i = 0, 1`). The places above `M` are these and
  their conjugates, indexed by pairs `(w, false)` and `(w, true)`.
* `S.latticeStabilizer`, `S.reduction`, `S.ResidueGL`: the integral elements of the finite adelic
  unitary group, and their reduction to the product of the general linear groups over the residue
  fields `ResField w` at the chosen places.
* `New.frameImage γ`: the columns of `γ` at the indices of the frame `f = (e₁, …, e_ϱ, z)`; so
  `frameImage 1` is the frame itself.
* `S.CharsAgree γ`, for rational `γ`: the character `S.unipotentChar` takes equal values on rational
  `u`, `u'` in `besselU` with `u γ = γ u'`. `S.Agrees s` is the analogue for `s` in `S.ResidueGL`.
* `besselH`, `besselU`, `besselS`: the unitary group of `X₀`, the unipotent group of the frame, and
  the Bessel subgroup that they generate.
* `Ô E`, `𝔸f E`: the integral finite adeles and the finite adeles of `E`.

## Relation to the literature

Take a rational element under which the unipotent character of the Poincaré series agrees with its
conjugate. For such an element, a vector shared by the standard frame and its image forces a
norm-one pair to occur. Take an integral adelic element k whose reduction modulo M agrees, and two
integral vectors orthogonal, in the standard form, to all vectors of f and kf but the last of each
(f is the frame). If the determinant δ of their products with these two last vectors is a finite
idele, the norm of the product of the primes over M where the span of f meets that of kf is at most
the index of δÔ in Ô (`New.Filling.meetNorm_le_genIndex_det`). This sorts the terms of the unfolded
second moment. Related work: Friedberg, Poincaré series for GL(n), 1987; Y. Liu, Relative trace
formulae toward Bessel and Fourier–Jacobi periods, 2014; Furusawa–Shalika, Central critical values
of degree four L-functions for GSp(4), Mem. AMS 782, 2003.
-/

noncomputable section

/-! ## Residues, meeting places, fixed vectors and open elements -/

namespace New.Filling

open Function Matrix Finset
variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- An entry of the reduction of an integral element modulo a chosen place `w` depends only on the
same entry of its matrix. -/
lemma reduction_apply_congr {k : S.latticeStabilizer} (l : S.latticeStabilizer) (i : Fin 2)
    (w : S.chosenPlaces i) {a b : 𝔰.BesselIndex}
    (h_entry : (k : S.GFin).val a b = (l : S.GFin).val a b) :
    S.reduction k i w a b = S.reduction l i w a b :=
  congrArg (New.reduceAt (w : FinPlace E)) (Subtype.ext h_entry)

/-- The chosen places `p` are the places of `E` in `S.chosenPlaces i`, of norm the prime
`S.levelPrime i` (`i = 0, 1`); `New.reduceAt p` is reduction of integral finite adeles modulo `p`.
Given residues `t p` and `t' p` at each chosen place `p`, some integral finite adele `y` reduces to
`t p` at every `p`, while its conjugate `star y` reduces to `t' p` there. -/
lemma exists_reduceAt_eq_and_reduceAt_star_eq
    (t t' : ∀ p : Σ i : Fin 2, S.chosenPlaces i, ResField (p.snd : FinPlace E)) :
    ∃ y : Ô E, ∀ p : Σ i : Fin 2, S.chosenPlaces i,
      New.reduceAt (p.snd : FinPlace E) y = t p ∧
      New.reduceAt (p.snd : FinPlace E) (star y) = t' p := by
  classical
  -- Take `a` with residues `t` and `b` with residues `t'`, both with conjugates that vanish at all
  -- chosen places. Then `y = a + star b`.
  suffices h_star_zero :
      ∀ u : ∀ p : Σ i : Fin 2, S.chosenPlaces i, ResField (p.snd : FinPlace E),
      ∃ a : Ô E, ∀ p : Σ i : Fin 2, S.chosenPlaces i,
        New.reduceAt (p.snd : FinPlace E) a = u p ∧
        New.reduceAt (p.snd : FinPlace E) (star a) = 0 by
    obtain ⟨a, ha⟩ := h_star_zero t
    obtain ⟨b, hb⟩ := h_star_zero t'
    exact ⟨a + star b, fun p ↦ by simp [ha p, hb p]⟩
  intro u
  -- Lift each `u p` to an integer of `E`, cut it off by the idempotent of `p`, and add up.
  let lift (p : Σ i : Fin 2, S.chosenPlaces i) : NumberField.RingOfIntegers E :=
    surjInv (algebraMap_ResField_surjective _) (u p)
  let e (p : Σ i : Fin 2, S.chosenPlaces i) : Ô E := ⟨idem {(p.snd : FinPlace E)}, idem_mem_Ô _⟩
  -- The chosen places are distinct, and no conjugate of one is chosen: one term survives.
  have h_idem (p q : Σ i : Fin 2, S.chosenPlaces i) :
      New.reduceAt (p.snd : FinPlace E) (e q) = if p = q then 1 else 0 := by
    simp [e, S.chosenPlaces_injective.eq_iff]
  have h_star_idem (p q : Σ i : Fin 2, S.chosenPlaces i) :
      New.reduceAt (p.snd : FinPlace E) (star (e q)) = 0 := by
    have h_star : star (e q) = ⟨idem (star ⁻¹' {(q.snd : FinPlace E)}), idem_mem_Ô _⟩ :=
      Subtype.ext (star_idem _)
    have h_ne : star (p.snd : FinPlace E) ≠ q.snd :=
      (ne_of_mem_of_not_mem q.snd.property (S.star_notMem_chosenPlaces p.snd.property)).symm
    simp [h_star, h_ne]
  refine ⟨∑ q : Σ i : Fin 2, S.chosenPlaces i, lift q • e q, fun p ↦ ⟨?_, ?_⟩⟩
  · simp [lift, Algebra.smul_def, h_idem, surjInv_eq]
  · simp [Algebra.smul_def, h_star_idem]

/-- Residues may be prescribed at all the places above `M`, the product of the two level primes, at
once. Such a place is a pair `x` of a chosen place `w` and a Boolean; `S.reduceAboveM x y` is the
residue at `w` of `y` if the Boolean is false and of its conjugate `star y` if it is true. For any
family `t` of residues there is an integral finite adele `y` with these reductions. -/
lemma exists_reduceAboveM_eq
    (t : ∀ x : (Σ i : Fin 2, S.chosenPlaces i) × Bool, ResField (x.1.snd : FinPlace E)) :
    ∃ y : Ô E, ∀ x : (Σ i : Fin 2, S.chosenPlaces i) × Bool, S.reduceAboveM x y = t x := by
  obtain ⟨y, hy⟩ :=
    exists_reduceAt_eq_and_reduceAt_star_eq (fun p ↦ t (p, false)) fun p ↦ t (p, true)
  refine ⟨y, ?_⟩
  rintro ⟨p, _ | _⟩
  · rw [reduceAboveM_false, (hy p).1]
  · rw [reduceAboveM_true, RingHom.comp_apply, starRingEnd_apply, (hy p).2]

/-- The action of `s` on the lattice modulo the place `p` of `E` above `M`: by its component at the
chosen place `w`, or by the inverse adjoint if `p` is the conjugate of `w`. -/
def actionAt (s : S.ResidueGL) (p : (Σ i : Fin 2, S.chosenPlaces i) × Bool) :
    Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField (p.1.snd : FinPlace E)) :=
  (S.idOrInvAdjoint p.2 (s p.1.fst p.1.snd)).val

/-- A nonzero vector of the span of the frame modulo the chosen place `w` (first component `false`)
or modulo its conjugate (`true`), given by its coordinates in the frame. -/
abbrev FrameVector {i : Fin 2} (w : S.chosenPlaces i) : Type :=
  Bool × {v : Fin (𝔰.ϱ + 1) → ResField (w : FinPlace E) // v ≠ 0}

/-- For `d = (ε, v)`, the subgroup of the `s` that fix the vector of the span of the frame with
coordinates `v`; the columns of `inclMatrix _ 𝔰.besselFrame` are the frame vectors. If `ε` is false,
`s` acts modulo `w` by its component at `w`; if `ε` is true, it acts modulo the conjugate of `w` by
the inverse adjoint of that component (`S.idOrInvAdjoint ε` makes this choice). See
`mem_vectorFixer`, `mem_vectorFixer_false` and `mem_vectorFixer_true`. -/
def vectorFixer {i : Fin 2} (w : S.chosenPlaces i) (d : S.FrameVector w) : Subgroup S.ResidueGL :=
  (MulAction.stabilizer (GL 𝔰.BesselIndex (ResField (w : FinPlace E)))
      (inclMatrix (ResField (w : FinPlace E)) 𝔰.besselFrame *ᵥ d.2.val)).comap
    (MonoidHom.mk' (fun s : S.ResidueGL ↦ S.idOrInvAdjoint d.1 (s i w)) (by simp))

/-- For `d = (ε, v)`, an element `s` lies in `vectorFixer w d` iff its action modulo the place
`(w, ε)` fixes the combination of the frame vectors with coordinates `v`. -/
lemma mem_vectorFixer {i : Fin 2} {w : S.chosenPlaces i} {d : S.FrameVector w} {s : S.ResidueGL} :
    s ∈ S.vectorFixer w d ↔
      S.actionAt s (⟨i, w⟩, d.1) *ᵥ frameImage 1 *ᵥ d.2.val = frameImage 1 *ᵥ d.2.val :=
  .rfl

/-- To fix a vector modulo the chosen place `w` is to fix it by the component at `w`. -/
lemma mem_vectorFixer_false {i : Fin 2} {w : S.chosenPlaces i}
    {v : {v : Fin (𝔰.ϱ + 1) → ResField (w : FinPlace E) // v ≠ 0}} {s : S.ResidueGL} :
    s ∈ S.vectorFixer w (false, v) ↔
      (s i w).val *ᵥ frameImage 1 *ᵥ v.val = frameImage 1 *ᵥ v.val :=
  .rfl

/-- To fix a vector modulo the conjugate of `w` is to fix, by the inverse transpose of the component
at `w`, the linear form that the vector defines through the Gram matrix of the lattice basis. -/
lemma mem_vectorFixer_true {i : Fin 2} {w : S.chosenPlaces i}
    {v : {v : Fin (𝔰.ϱ + 1) → ResField (w : FinPlace E) // v ≠ 0}} {s : S.ResidueGL} :
    s ∈ S.vectorFixer w (true, v) ↔
      invTransposeGL (s i w) •
          (S.latticeMiddle (ResField (w : FinPlace E))).splitGram *ᵥ frameImage 1 *ᵥ v.val =
        (S.latticeMiddle (ResField (w : FinPlace E))).splitGram *ᵥ frameImage 1 *ᵥ v.val := by
  let : StarRing (ResField (w : FinPlace E)) := starRingOfComm
  let J : GL 𝔰.BesselIndex (ResField (w : FinPlace E)) :=
    (Floors.IsHermitianUnit.isUnit (J := (S.latticeMiddle
      (ResField (w : FinPlace E))).splitGram)).unit
  set x : 𝔰.BesselIndex → ResField (w : FinPlace E) := frameImage 1 *ᵥ v.val
  -- The inverse adjoint is the conjugate of the inverse transpose by `J⁻¹`.
  change (J⁻¹ * invTransposeGL (s i w) * J⁻¹⁻¹) • x = x ↔ invTransposeGL (s i w) • J • x = J • x
  rw [inv_inv, mul_smul, mul_smul, inv_smul_eq_iff]

/-- The matrix `g` applied to the combination of the frame vectors with coordinates `x` is the
combination of their images with the same coordinates. -/
lemma mulVec_frameImage_one_mulVec {R : Type*} [CommRing R]
    (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R) (x : Fin (𝔰.ϱ + 1) → R) :
    g *ᵥ frameImage 1 *ᵥ x = frameImage g *ᵥ x := by
  rw [mulVec_mulVec]
  exact congrArg (fun N ↦ N *ᵥ x) (mul_inclMatrix g 𝔰.besselFrame)

/-- Let `besselH` be the fixer of all basis vectors outside `𝔰.κ`, a copy of the unitary group of
X₀. Its reduction to the residue fields, `S.reducedImage besselH`, fixes every nonzero vector `d` of
the span of the frame f = (e₁,…,e_ϱ,z), taken modulo a chosen place `w` or modulo its conjugate.
That is, `S.reducedImage besselH` lies in `S.vectorFixer w d`. -/
lemma reducedImage_besselH_le_vectorFixer {i : Fin 2} (w : S.chosenPlaces i)
    (d : S.FrameVector w) : S.reducedImage besselH ≤ S.vectorFixer w d := by
  rintro _ ⟨k, hk, rfl⟩
  -- The columns of `k` at the frame are those of `1`, and this passes to the residue field.
  have h_frame (a : 𝔰.BesselIndex) (b : Fin (𝔰.ϱ + 1)) :
      (k : S.GFin).val a (𝔰.besselFrame b) = if a = 𝔰.besselFrame b then 1 else 0 := by
    simpa [one_apply] using congrFun₂ (frameImage_mul_of_mem_agreeWithOneOn hk 1) a b
  have h_action : frameImage (S.actionAt (S.reduction k) (⟨i, w⟩, d.1)) = frameImage 1 := by
    rw [actionAt, ← intGL_map_reduceAboveM]
    ext a b
    by_cases h_eq : a = 𝔰.besselFrame b <;> simp [intGL.map_apply, h_frame, h_eq, one_apply,
      ← Submonoid.one_def, ← ZeroMemClass.zero_def]
  rw [mem_vectorFixer, mulVec_frameImage_one_mulVec, h_action]

/-- The element `s` meets at the place `p` of `E` above `M`: modulo `p`, the span of the frame and
its image under `s` share a nonzero vector. -/
def MeetsAt (s : S.ResidueGL) (p : (Σ i : Fin 2, S.chosenPlaces i) × Bool) : Prop :=
  ∃ x y : Fin (𝔰.ϱ + 1) → ResField (p.1.snd : FinPlace E),
    x ≠ 0 ∧ frameImage 1 *ᵥ x = frameImage (S.actionAt s p) *ᵥ y

open Classical in
/-- The absolute norm of the product of the places at which `s` meets; a place above
`S.levelPrime i` has norm `S.levelPrime i`. -/
def meetNorm (s : S.ResidueGL) : ℕ :=
  ∏ p : (Σ i : Fin 2, S.chosenPlaces i) × Bool with S.MeetsAt s p, S.levelPrime p.1.fst

/-- An element that fixes a nonzero vector of the span of the frame modulo a place meets there. -/
lemma meetsAt_of_mem_vectorFixer {i : Fin 2} {w : S.chosenPlaces i} {d : S.FrameVector w}
    {s : S.ResidueGL} (hs : s ∈ S.vectorFixer w d) : S.MeetsAt s (⟨i, w⟩, d.1) := by
  rw [mem_vectorFixer, mulVec_frameImage_one_mulVec] at hs
  exact ⟨d.2.val, d.2.val, d.2.property, hs.symm⟩

open scoped Classical in
/-- If `s` meets at every place of a set `A` of places above `M`, the product of their norms is at
most `meetNorm s`, the product of the norms of all the places at which `s` meets. -/
lemma prod_le_meetNorm {s : S.ResidueGL} {A : Finset ((Σ i : Fin 2, S.chosenPlaces i) × Bool)}
    (hA : ∀ p ∈ A, S.MeetsAt s p) : ∏ p ∈ A, S.levelPrime p.1.fst ≤ S.meetNorm s :=
  prod_le_prod_of_subset_of_one_le (fun p hp ↦ mem_filter.2 ⟨mem_univ p, hA p hp⟩)
    fun p _ _ ↦ (S.levelPrime_prime_and_ne p.1.fst).1.one_le

/-- The norm of the product of the places above `M` at which `s` meets is at least `1`. -/
lemma one_le_meetNorm (s : S.ResidueGL) : 1 ≤ S.meetNorm s := by
  simpa using prod_le_meetNorm (s := s) (A := ∅) (by simp)

/-- The subgroup of the elements that fix the given vector modulo `w` or its conjugate, for every
`w` in a set of chosen places above the first level prime. The vectors at other places are
ignored. -/
def fixer (places : Finset (S.chosenPlaces 0))
    (vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w) : Subgroup S.ResidueGL :=
  ⨅ w ∈ places, S.vectorFixer w (vectors w)

/-- An element lies in `fixer places vectors` iff it fixes `vectors w` for every `w` in
`places`. -/
lemma mem_fixer {places : Finset (S.chosenPlaces 0)}
    {vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w} {s : S.ResidueGL} :
    s ∈ S.fixer places vectors ↔ ∀ w ∈ places, s ∈ S.vectorFixer w (vectors w) := by
  simp [fixer, Subgroup.mem_iInf]

/-- The group that fixes given vectors of the span of the frame modulo some places contains the
reduction of `besselH`, the unitary group of `X₀`. -/
theorem reducedImage_besselH_le_fixer (places : Finset (S.chosenPlaces 0))
    (vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w) :
    S.reducedImage besselH ≤ S.fixer places vectors :=
  fun _ hs ↦ mem_fixer.2 fun w _ ↦ reducedImage_besselH_le_vectorFixer w (vectors w) hs

open scoped Classical in
/-- For `w` not in `places`, `s` lies in `S.fixer` for `insert w places` and `update vectors w d`
iff `s` lies in `S.fixer places vectors` and in `S.vectorFixer w d`, the subgroup fixing the vector
`d` at `w`. -/
lemma mem_fixer_insert {places : Finset (S.chosenPlaces 0)} {w : S.chosenPlaces 0} (hw : w ∉ places)
    {vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w} {d : S.FrameVector w} {s : S.ResidueGL} :
    s ∈ S.fixer (insert w places) (update vectors w d) ↔
      s ∈ S.fixer places vectors ∧ s ∈ S.vectorFixer w d := by
  rw [mem_fixer, mem_fixer, forall_mem_insert, update_self, and_comm]
  exact and_congr_left' (forall₂_congr fun v hv ↦ by rw [update_of_ne (ne_of_mem_of_not_mem hv hw)])

/-- The element `s` is open: at some chosen place `w` above the first level prime, the leading
principal minors of order less than `𝔰.n = ϱ + 1` of the matrix `(h(f_j, s f_l))` are all nonzero.
Here `f` is the frame, which has `𝔰.n` vectors, `h` is the form in the lattice basis modulo `w`
(its middle block is `S.latticeMiddle`), and `frameGram` is this matrix of products. -/
def IsOpenElement (s : S.ResidueGL) : Prop :=
  ∃ w : S.chosenPlaces 0, ∀ l : Fin 𝔰.n,
    leadingMinor ((S.latticeMiddle (ResField (w : FinPlace E))).frameGram (s 0 w).val) l.castSucc ≠
      0

/-- The element `s` is `ζ` times an element of the reduction of the Bessel subgroup, the integral
adele `ζ` acting through its residues at the chosen places. -/
def InScalarCoset (ζ : Ô E) (s : S.ResidueGL) : Prop :=
  ∃ t ∈ S.reducedImage besselS, ∀ (i : Fin 2) (w : S.chosenPlaces i),
    (s i w).val = New.reduceAt (w : FinPlace E) ζ • (t i w).val

end New.Filling

/-!
## The group U(X₀) in the lattice basis: integrality, reduction, class sums

The unitary group `New.Gf E 𝔰.κ` of the standard form on `X₀`, with basis indexed by `𝔰.κ`, over
the finite adeles embeds, by `New.Filling.inclHFin`, in the larger unitary group of the filling data
`S` (`New.Filling`). The larger group is written in the basis of a lattice that involves the idele
`S.piN` of norm `S.N` at the index `𝔰.k₀`.

`New.IsIntMatrix` says that a matrix has entries in a subring; `scaleAt p k₀` is the diagonal
matrix with `p` at `k₀` and `1` elsewhere; `congruenceGL M e` is the group of integral invertible
matrices whose rows `e i` are congruent to those of `1` modulo `M`.
-/

namespace New.Filling

open NumberField Matrix Valued
variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)

/-- The matrix `l` with row `o` multiplied by `a` is integral iff that row times `a` and the other
rows of `l` are integral. -/
lemma isIntMatrix_scaleAt_mul_iff {κ m R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R]
    {O : Subring R} {a : R} {o : κ} {l : Matrix κ m R} :
    IsIntMatrix O (scaleAt a o * l) ↔ (∀ j : m, a * l o j ∈ O) ∧ ∀ i ≠ o, ∀ j : m, l i j ∈ O := by
  simp only [IsIntMatrix, diagonal_mul]
  grind

/-- Let `S.piN` be the integral idele of the filling data `S`, and let `l` be a matrix over the
finite adeles with rows indexed by `𝔰.κ`; a matrix is integral (`IsIntMatrix (Ô E)`) if its entries
are integral finite adeles. The columns of `middleInclusionMatrix 𝔰 S.piN` are the orthonormal basis
vectors of `X₀` in the lattice basis of `X₀ ⊕ ⟨z⟩`. Its product with `l` is integral iff `l` is
integral and every entry of row `k₀` of `l` is `S.piN` times an integral adele. -/
lemma isIntMatrix_middleInclusionMatrix_mul_iff {m : Type*} {l : Matrix 𝔰.κ m (𝔸f E)} :
    IsIntMatrix (Ô E) (middleInclusionMatrix 𝔰 S.piN * l) ↔
      IsIntMatrix (Ô E) l ∧ ∀ j : m, l 𝔰.k₀ j ∈ Ô E ∙ S.piN.val := by
  -- The product has the rows of `l` outside `k₀`, row `k₀` times `star piN`, and row `k₀` times
  -- `-piN⁻¹`. As `piN` and `star piN` are integral, the last row decides for row `k₀`.
  have h_rows : IsIntMatrix (Ô E) (middleInclusionMatrix 𝔰 S.piN * l) ↔
      IsIntMatrix (Ô E) (scaleAt (star S.piN.val) 𝔰.k₀ * l) ∧
        ∀ j : m, S.piN⁻¹.val * l 𝔰.k₀ j ∈ Ô E := by
    simp [middleInclusionMatrix, IsIntMatrix, Matrix.mul_apply]
  rw [h_rows, isIntMatrix_scaleAt_mul_iff]
  constructor
  · rintro ⟨⟨-, h_other⟩, h_div⟩
    have h_row (j : m) : l 𝔰.k₀ j ∈ Ô E := by
      simpa using mul_mem S.piN_mem (h_div j)
    have h_int : IsIntMatrix (Ô E) l := by
      intro i j
      obtain rfl | hi := eq_or_ne i 𝔰.k₀
      · exact h_row j
      · exact h_other i hi j
    exact ⟨h_int, fun j ↦ mem_span_unit_iff.2 (h_div j)⟩
  · rintro ⟨h_int, h_span⟩
    have h_star (j : m) : star S.piN.val * l 𝔰.k₀ j ∈ Ô E :=
      mul_mem (star_mem_Ô S.piN_mem) (h_int 𝔰.k₀ j)
    have h_div (j : m) : S.piN⁻¹.val * l 𝔰.k₀ j ∈ Ô E := mem_span_unit_iff.1 (h_span j)
    exact ⟨⟨h_star, fun i _ j ↦ h_int i j⟩, h_div⟩

/-- If `l` stays integral after dividing its row `k₀` by `S.piN`, then the product of
`middleInclusionMatrix 𝔰 S.piN` with `l` is integral. -/
lemma isIntMatrix_middleInclusionMatrix_mul_of_scaleAt {m : Type*} {l : Matrix 𝔰.κ m (𝔸f E)}
    (hl : IsIntMatrix (Ô E) (scaleAt S.piN⁻¹.val 𝔰.k₀ * l)) :
    IsIntMatrix (Ô E) (middleInclusionMatrix 𝔰 S.piN * l) := by
  obtain ⟨h_div, h_other⟩ := isIntMatrix_scaleAt_mul_iff.1 hl
  refine S.isIntMatrix_middleInclusionMatrix_mul_iff.2
    ⟨fun i j ↦ ?_, fun j ↦ mem_span_unit_iff.2 (h_div j)⟩
  obtain rfl | hi := eq_or_ne i 𝔰.k₀
  · simpa using mul_mem S.piN_mem (h_div j)
  · exact h_other i hi j

/-- The blocks follow `𝔰.BesselIndex = Fin ϱ ⊕ (𝔰.κ ⊕ Unit) ⊕ Fin ϱ`. The image of `k` in the large
unitary group, in the lattice basis, differs from `1` only in the block with rows `𝔰.κ ⊕ Unit` and
columns `𝔰.κ`. There the difference is `middleInclusionMatrix * ((k - 1) * D)` with `D` the diagonal
matrix `scaleAt (star piN⁻¹) k₀`. -/
lemma inclHFin_sub_one_eq {k : U (1 : Matrix 𝔰.κ 𝔰.κ (𝔸f E))} :
    (S.inclHFin k).val.val - 1 = fromBlocks 0 0 0 (fromBlocks (fromCols
      (middleInclusionMatrix 𝔰 S.piN * ((k.val.val - 1) * scaleAt (star S.piN⁻¹.val) 𝔰.k₀)) 0)
      0 0 0) := by
  -- `S.inclHFin k` is the conjugate, by the lattice basis `B`, of `k` acting on the block `𝔰.κ`.
  let B : GL 𝔰.BesselIndex (𝔸f E) := besselLatticeBasis 𝔰 S.piN
  have h_block : (toBesselH 𝔰 (S.N : 𝔸f E) k).val.val - 1 =
      fromBlocks 0 0 0 (fromBlocks (fromBlocks (k.val.val - 1) 0 0 0) 0 0 0) := by
    simp [toBesselH, ← Matrix.ext_iff, Matrix.one_apply]
  have h_conj : (S.inclHFin k).val.val - 1 =
      B⁻¹.val * ((toBesselH 𝔰 (S.N : 𝔸f E) k).val.val - 1) * B.val := by
    simp [inclHFin, toLatticeBasis, B, mul_sub, sub_mul]
  rw [h_conj, h_block]
  simp [B, besselLatticeBasis, fromBlocks_multiply, fromCols_mul_fromBlocks, Matrix.mul_assoc]

/-- A property that holds for `0` holds for all entries of `S.inclHFin k - 1` iff it holds for all
entries of `middleInclusionMatrix * ((k - 1) * D)`, with `D` the diagonal matrix
`scaleAt (star piN⁻¹) k₀`. -/
lemma forall_inclHFin_sub_one_iff {k : U (1 : Matrix 𝔰.κ 𝔰.κ (𝔸f E))} (P : 𝔸f E → Prop) (hP : P 0) :
    (∀ a b : 𝔰.BesselIndex, P (((S.inclHFin k).val.val - 1) a b)) ↔
      ∀ (a : 𝔰.κ ⊕ Unit) (b : 𝔰.κ),
        P ((middleInclusionMatrix 𝔰 S.piN * ((k.val.val - 1) * scaleAt (star S.piN⁻¹.val) 𝔰.k₀) :
          Matrix (𝔰.κ ⊕ Unit) 𝔰.κ (𝔸f E)) a b) := by
  rw [inclHFin_sub_one_eq]
  simp [hP]

/-- Let the idele `p` be a unit at `w` or at the conjugate of `w`, for each place `w` (`v` is the
valuation). If the finite adelic unitary matrix `k` is integral with row `o` congruent to that of
`1` modulo `p`, then `k - 1` stays integral after dividing row `o` by `p` and column `o` by
`p̄`. -/
lemma isIntMatrix_scaleAt_mul_sub_one_mul_scaleAt {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : (𝔸f E)ˣ) (o : κ)
    (hp : ∀ w : FinPlace E, v (p.val w) = 1 ∨ v (p.val (star w)) = 1) {k : Gf E κ}
    (hk : k.val ∈ congruenceGL (Ô E ∙ p.val) fun () ↦ o) :
    IsIntMatrix (Ô E) (scaleAt p⁻¹.val o * ((k.val.val - 1) * scaleAt (star p⁻¹.val) o)) := by
  -- Row `o` of `M = k - 1` is divisible by `p`. The same holds for `k⁻¹ = kᴴ`, so column `o` of
  -- `M` is divisible by `star p`. All entries of `M` are integral.
  set M : Matrix κ κ (𝔸f E) := k.val.val - 1 with hM
  obtain ⟨-, hk_inv_row⟩ := inv_mem hk
  obtain ⟨hk_int, hk_row⟩ := hk
  have h_int : IsIntMatrix (Ô E) M := hk_int.isIntMatrix.sub .one
  have h_row (j : κ) : p⁻¹.val * M o j ∈ Ô E := mem_span_unit_iff.1 (hk_row () j)
  have h_col (i : κ) : M i o * star p⁻¹.val ∈ Ô E := by
    have h_inv : p⁻¹.val * Mᴴ o i ∈ Ô E := by
      rw [hM, conjTranspose_sub, conjTranspose_one, ← U.inv_val_eq_conjTranspose]
      exact mem_span_unit_iff.1 (hk_inv_row () i)
    simpa [star_mul] using star_mem_Ô h_inv
  -- The entry `(o, o)` is divided twice, but at each place one of the two divisors is a unit.
  have h_corner : p⁻¹.val * (M o o * star p⁻¹.val) ∈ Ô E := mem_Ô.2 fun w ↦ by
    obtain h_unit | h_unit := hp w
    · simpa [idele_inv_apply_and_ne_zero, h_unit] using mem_Ô.1 (h_col o) w
    · simpa [idele_inv_apply_and_ne_zero, h_unit] using mem_Ô.1 (h_row o) w
  refine isIntMatrix_scaleAt_mul_iff.2 ⟨fun j ↦ ?_, fun i _ j ↦ ?_⟩
  · by_cases hj : j = o <;> simp [hj, h_corner, h_row]
  · by_cases hj : j = o <;> simp [hj, h_col, h_int i j]

/-- The diagonal matrix with `a ∈ O` at `o` and `1` elsewhere has entries in the subring `O`. -/
lemma isIntMatrix_scaleAt {A κ : Type*} [CommRing A] [DecidableEq κ] {O : Subring A} {a : A}
    (ha : a ∈ O) (o : κ) : IsIntMatrix O (scaleAt a o) := by
  simp [ha, IsIntMatrix, diagonal, ite_mem]

/-- Let `p` be an integral idele such that at each place `p` or its conjugate is a unit. Let `L` be
the lattice of integral vectors whose coordinate `o` is divisible by `p`; its dual `L^∨` consists of
the vectors that are integral except for a denominator `p̄` in that coordinate. A finite adelic
unitary matrix `k` is integral with row `o` congruent to that of `1` modulo `p` if and only if
`k - 1` maps `L^∨` into `L`. -/
lemma mem_congruenceGL_iff_isIntMatrix_scaleAt {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : (𝔸f E)ˣ) (o : κ) (hp_int : p.val ∈ Ô E)
    (hp_unit : ∀ w : FinPlace E, v (p.val w) = 1 ∨ v (p.val (star w)) = 1) {k : Gf E κ} :
    k.val ∈ congruenceGL (Ô E ∙ p.val) (fun _ : Unit ↦ o) ↔
      IsIntMatrix (Ô E) (scaleAt p⁻¹.val o * ((k.val.val - 1) * scaleAt (star p⁻¹.val) o)) := by
  refine ⟨isIntMatrix_scaleAt_mul_sub_one_mul_scaleAt p o hp_unit, fun hM ↦ ?_⟩
  -- Undo the divisions by multiplying with integral diagonal matrices.
  have h_row : IsIntMatrix (Ô E) (scaleAt p⁻¹.val o * (k.val.val - 1)) := by
    simpa +contextual [Matrix.mul_assoc, ← star_mul] using
      hM.mul (isIntMatrix_scaleAt (star_mem_Ô hp_int) o)
  have h_sub : IsIntMatrix (Ô E) (k.val.val - 1) := by
    simpa +contextual [← Matrix.mul_assoc] using (isIntMatrix_scaleAt hp_int o).mul h_row
  refine ⟨mem_stdLevel.2 ?_, fun _ j ↦ mem_span_unit_iff.2 ?_⟩
  · simpa [IsIntMatrix] using h_sub.add .one
  · simpa using h_row o j

/-- An element `x` of the large unitary group lies in the stabilizer of the lattice iff `x - 1` is
integral: an isometry of a unimodular form with `x - 1` integral has an integral inverse. -/
lemma mem_latticeStabilizer_iff_isIntMatrix_sub_one {x : S.GFin} :
    x ∈ S.latticeStabilizer ↔ IsIntMatrix (Ô E) (x.val.val - 1) := by
  refine ⟨fun hx ↦ hx.isIntMatrix.sub .one, fun hx ↦ ?_⟩
  rw [latticeStabilizer, ← unitaryLevel_one]
  exact S.isUnimodular_latticeMiddle.splitGram.mem_unitaryLevel (one_mem _) (by simpa using hx)

/-- Let `k` be a unitary matrix for the identity form on `𝔰.κ` over the finite adeles `𝔸f E`. Its
image `S.inclHFin k` in the finite adelic unitary group of V, written in the lattice basis, lies in
`S.latticeStabilizer` exactly when `k` lies in `congruenceGL`. That means `k` is integral and its
row at `𝔰.k₀` is congruent to that of `1` modulo the integral idele `S.piN`. -/
lemma inclHFin_mem_latticeStabilizer_iff {k : U (1 : Matrix 𝔰.κ 𝔰.κ (𝔸f E))} :
    S.inclHFin k ∈ S.latticeStabilizer ↔
      k.val ∈ congruenceGL (Ô E ∙ S.piN.val) fun _ : Unit ↦ 𝔰.k₀ := by
  -- Both sides say that `(k - 1) * D⁻¹` stays integral after dividing its row `k₀` by `piN`, `D`
  -- being the diagonal matrix `scaleAt (star piN) k₀`.
  have h_mid : IsIntMatrix (Ô E) ((S.inclHFin k).val.val - 1) ↔ IsIntMatrix (Ô E)
      (middleInclusionMatrix 𝔰 S.piN * ((k.val.val - 1) * scaleAt (star S.piN⁻¹.val) 𝔰.k₀)) :=
    S.forall_inclHFin_sub_one_iff (fun x ↦ x ∈ Ô E) (zero_mem _)
  have h_unit (w : FinPlace E) : v (S.piN.val w) = 1 ∨ v (S.piN.val (star w)) = 1 :=
    (S.N_split w).imp_right And.right
  rw [mem_latticeStabilizer_iff_isIntMatrix_sub_one, h_mid,
    mem_congruenceGL_iff_isIntMatrix_scaleAt S.piN 𝔰.k₀ S.piN_mem h_unit]
  refine ⟨fun hM ↦ ?_, S.isIntMatrix_middleInclusionMatrix_mul_of_scaleAt⟩
  obtain ⟨h_int, h_row⟩ := S.isIntMatrix_middleInclusionMatrix_mul_iff.1 hM
  exact isIntMatrix_scaleAt_mul_iff.2
    ⟨fun j ↦ mem_span_unit_iff.1 (h_row j), fun i _ j ↦ h_int i j⟩

/-- Let `k` be a unitary matrix for the standard form on `X₀`, with basis indexed by `𝔰.κ`, over the
finite adeles. The embedding `S.inclHFin` sends it to the finite adelic unitary group of the whole
space, written in the lattice basis of `S`; `S.latticeStabilizer` consists of the elements whose
matrix in this basis is invertible over `Ô E`. Let `S.inclHFin k` lie in it, so that `k` is
integral. For `i : Fin 2`, indexing the level primes p₀, p₁ of `S`, and a place `w` in
`S.chosenPlaces i`, of norm p_i, the reduction `S.reduction` of `S.inclHFin k` modulo `w` is `1`
exactly when that of `k` is; `stdLevel.reduceAt w` is the entrywise reduction modulo `w` of integral
unitary matrices. -/
lemma reduction_inclHFin_eq_one_iff {k : U (1 : Matrix 𝔰.κ 𝔰.κ (𝔸f E))}
    (h_mem : S.inclHFin k ∈ S.latticeStabilizer) (i : Fin 2) (w : S.chosenPlaces i) :
    S.reduction ⟨S.inclHFin k, h_mem⟩ i w = 1 ↔
      stdLevel.reduceAt w ⟨k, (S.inclHFin_mem_latticeStabilizer_iff.mp h_mem).1⟩ = 1 := by
  -- Each side says that all entries of the matrix minus `1` have valuation `< 1` at `w`.
  have h_left : S.reduction ⟨S.inclHFin k, h_mem⟩ i w = 1 ↔
      ∀ a b : 𝔰.BesselIndex, v (((S.inclHFin k).val.val - 1) a b w) < 1 :=
    intGL.map_eq_one.trans (forall₂_congr fun _ _ ↦ reduceAt_eq_zero)
  have h_right : stdLevel.reduceAt w ⟨k, (S.inclHFin_mem_latticeStabilizer_iff.mp h_mem).1⟩ = 1 ↔
      ∀ a b : 𝔰.κ, v ((k.val.val - 1) a b w) < 1 :=
    intGL.map_eq_one.trans (forall₂_congr fun _ _ ↦ reduceAt_eq_zero)
  rw [h_left, h_right, S.forall_inclHFin_sub_one_iff (fun x ↦ v (x w) < 1) (by simp)]
  -- As `w` has norm `levelPrime i ≠ N`, `piN` and its conjugate are units at `w` and do not
  -- change valuations; the extra row of `middleInclusionMatrix` repeats the condition on row `k₀`.
  have h_unit {u : FinPlace E} (hu : u.q = S.levelPrime i) : v (S.piN.val u) = 1 :=
    (S.N_split u).resolve_right fun h_N ↦ (S.levelPrime_prime_and_ne i).2 (hu.symm.trans h_N.1)
  have h_row : (∀ a b : 𝔰.κ, v ((k.val.val - 1) a b w) < 1) →
      ∀ b : 𝔰.κ, v ((k.val.val - 1) 𝔰.k₀ b w) < 1 := fun h_all ↦ h_all 𝔰.k₀
  simpa [S.chosenPlaces_q i, h_unit, idele_inv_apply_and_ne_zero, apply_ite, ite_apply,
    middleInclusionMatrix, diagonal, Matrix.mul_apply] using h_row

/-- The classes `S.Classes` are the double cosets, in the finite adelic points of `U(X₀)`, of the
rational points `stdRatPoints` and the level subgroup `S.sourceLevel` of the filling data. At this
level the stabilisers are trivial, so the class sum of `f` (the sum over the double cosets weighted
by the inverse orders of the stabilisers) is the plain sum over the classes. -/
lemma classSum_sourceLevel_eq_sum (f : Gf E 𝔰.κ → ℝ) :
    classSum stdRatPoints S.sourceLevel f = (∑ c : S.Classes, f c.out : ℝ) := by
  rw [← finsum_eq_sum_of_fintype]
  exact finsum_congr fun c ↦ by simp [classAut_eq_bot]

/-- The residue field at a chosen place `w` of index `i` has `S.levelPrime i` elements. -/
lemma card_resField_eq_levelPrime (i : Fin 2) (w : S.chosenPlaces i) :
    Nat.card (ResField w.val) = S.levelPrime i := by
  rw [card_ResField, S.chosenPlaces_q i w w.property]

end New.Filling

/-! ## Terms that do not agree contribute `0` -/

namespace New.Filling
open MulAction Matrix Fin Set MeasureTheory
open scoped Classical
open NumberField (InfinitePlace)

/-- Let `a x • x` be a chosen representative of the orbit of `x` under the group `H`. A sum over
`u : H` that is restricted to those `u` for which `u • x` is the representative is a sum over the
stabilizer of the representative, shifted by `a x`. -/
lemma tsum_indicator_smul_eq_tsum_stabilizer {H X : Type*} [Group H] [MulAction H X] {a : X → H}
    (ha : ∀ x : X, a x • x = (Quotient.mk (orbitRel H X) x).out) (f : X → H → ENNReal) (x : X) :
    ∑' u : H, {z : X | z = a z • z}.indicator 1 (u • x) * f (u • x) u =
      ∑' u : stabilizer H (a x • x), f (a x • x) (u * a x) := by
  have h_mem (u : H) : u • a x • x = a (u • a x • x) • u • a x • x ↔ u • a x • x = a x • x := by
    rw [ha (u • a x • x), ← mul_smul, Quotient.sound (s := orbitRel H X) (mem_orbit x _), ← ha]
  calc _ = ∑' u : H, {z : X | z = a z • z}.indicator 1 ((u * a x) • x) *
        f ((u * a x) • x) (u * a x) := ((Equiv.mulRight (a x)).tsum_eq _).symm
    _ = ∑' u : H, (stabilizer H (a x • x) : Set H).indicator
        (fun u : H ↦ f (a x • x) (u * a x)) u :=
      tsum_congr fun u ↦ by simp +contextual [indicator_apply, mul_smul, h_mem]
    _ = _ := (tsum_subtype _ _).symm

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- Let the characters of the rational element `γ` not agree (`¬S.CharsAgree γ`): the character
`S.unipotentChar` takes different values on some rational `u`, `u'` in the Bessel unipotent group
`besselU` with `u γ = γ u'`. For `c` in `S.Classes`, the double cosets
`U(X₀)(E⁺) \ U(X₀)(𝔸_f) / sourceLevel`, `S.classUnipotent c` is a congruence subgroup of the
rational points of `besselU`. Let `Γ` be the stabilizer in it of the coset
`γ · S.classUnipotent c'`, mapped by `S.ratToInf` to the product over the infinite places of the
complex unitary group `𝔰.G₁`. Let `Γ` be discrete and `β` a cutoff for it. Then the kernel
`S.besselKernel side γ y = W(y) ⊗ W(γ⁻¹ y)^*` has integral `0` against `β`; here `W` is the Bessel
function or its cut, according to `side`. -/
lemma integral_besselKernel_eq_zero_of_not_charsAgree {γ : S.G E} (side : FullOrCut)
    (hγ : ¬S.CharsAgree γ) {c c' : S.Classes} {Γ : Subgroup (InfinitePlace E → 𝔰.G₁)}
    (hΓ : Γ = (stabilizer (S.classUnipotent c) (γ : S.G E ⧸ S.classUnipotent c')).map
      (S.ratToInf.domRestrict (S.classUnipotent c))) [DiscreteTopology Γ]
    {β : (InfinitePlace E → 𝔰.G₁) → ENNReal} (hβ : IsCutoff (H := Γ) Measure.count β) :
    ∫ y : InfinitePlace E → 𝔰.G₁, (β y).toReal • S.besselKernel side γ y = 0 := by
  -- The kernel is invariant under `Γ`, so this is its integral over the quotient by `Γ`; and some
  -- `u` twists the kernel by a scalar `≠ 1`.
  obtain ⟨u, hu, u', hu', h_comm, h_ne⟩ : ∃ u ∈ besselU, ∃ u' ∈ besselU, u * γ = γ * u' ∧
      S.unipotentChar (S.ratToFin u) ≠ S.unipotentChar (S.ratToFin u') := by
    simpa [CharsAgree] using hγ
  have h_inv (g : Γ) (y : InfinitePlace E → 𝔰.G₁) :
      S.besselKernel side γ (g • y) = S.besselKernel side γ y := by
    subst hΓ
    obtain ⟨_, k, hk, rfl⟩ := g
    have h_conj : γ⁻¹ * (k * γ) ∈ S.classUnipotent c' := QuotientGroup.eq.1 hk.symm
    have h_shift : S.besselFn side ((S.ratToInf γ)⁻¹ * (S.ratToInf k * y)) =
        S.besselFn side ((S.ratToInf γ)⁻¹ * y) := by
      simpa [mul_assoc] using besselFn_mul_of_mem_classUnipotent ⟨_, h_conj⟩ ((S.ratToInf γ)⁻¹ * y)
    simp [besselKernel, besselFn_mul_of_mem_classUnipotent k, h_shift]
  have h_twist (y : InfinitePlace E → 𝔰.G₁) : S.besselKernel side γ (S.ratToInf u * y) =
      ((S.unipotentChar (S.ratToFin u))⁻¹ * S.unipotentChar (S.ratToFin u')) •
        S.besselKernel side γ y := by
    rw [← besselKernel_besselU_mul hu hu', mul_inv_eq_of_eq_mul h_comm]
  rw [← hβ.integral_orbitMeasure h_inv]
  exact integral_quotMeasure_eq_zero_of_twist volume (fun g hg ↦ h_inv ⟨g, hg⟩)
    continuous_besselKernel (by simp [unipotentChar]) (mt eq_of_inv_mul_eq_one h_ne) h_twist

/-- Let `E` contain a primitive root of unity of order `5040`, let the filling data satisfy the
standing hypotheses `S.IsAdmissible`, and let `T` be a set of rational elements that is stable under
multiplication by the unipotent group `besselU` on both sides. Suppose that no `γ` in `T` has
agreeing characters: for each `γ` in `T` the character `S.unipotentChar` takes different values on
some rational `u`, `u'` in `besselU` with `u γ = γ u'`. Then `S.amplitudeSum side T c s c' = 0`.
This is the sum of the amplitudes of the `γ` in `T` such that `h_c⁻¹ γ h_c'` is integral with
reduction `s`, where `h_c`, `h_c'` represent the classes `c`, `c'`. -/
lemma amplitudeSum_eq_zero_of_not_charsAgree [HasPrimitiveRoot5040 E]
    [S.IsAdmissible] {side : FullOrCut} {T : Set (S.G E)}
    (hT : S.IsStable T) (h_not_agree : ∀ γ ∈ T, ¬S.CharsAgree γ) (c : S.Classes) (s : S.ResidueGL)
    (c' : S.Classes) : S.amplitudeSum side T c s c' = 0 := by
  -- The sum may be computed with any weight of sum `1` on the orbits of
  -- `S.classUnipotent c × S.classUnipotent c'`. Take one adapted to the stabilizers of the cosets
  -- `γ · S.classUnipotent c'`; then the term of each `γ` is a multiple of an integral that
  -- vanishes. `φ x` is a cutoff for the stabilizer of the coset `x` acting at the infinite places.
  let Γ (x : S.G E ⧸ S.classUnipotent c') : Subgroup (InfinitePlace E → 𝔰.G₁) :=
    (stabilizer (S.classUnipotent c) x).map (S.ratToInf.domRestrict (S.classUnipotent c))
  have h_cutoff (x : S.G E ⧸ S.classUnipotent c') : ∃ β : (InfinitePlace E → 𝔰.G₁) → ENNReal,
      Measurable β ∧ (∀ y, ∑' u : stabilizer (S.classUnipotent c) x, β (S.ratToInf u * y) = 1) ∧
        DiscreteTopology (Γ x) ∧ IsCutoff (H := Γ x) Measure.count β :=
    S.exists_cutoff_classUnipotent (stabilizer (S.classUnipotent c) x)
  choose φ hφ_meas hφ_sum h_discrete hφ_cutoff using h_cutoff
  -- `a x • x` is a chosen representative of the orbit of the coset `x` under `S.classUnipotent c`.
  have h_rep (x : S.G E ⧸ S.classUnipotent c') : ∃ u : S.classUnipotent c,
      u • x = (Quotient.mk (orbitRel (S.classUnipotent c) (S.G E ⧸ S.classUnipotent c')) x).out :=
    Quotient.mk_out (s := orbitRel (S.classUnipotent c) (S.G E ⧸ S.classUnipotent c')) x
  choose a ha using h_rep
  let reps : Set (S.G E ⧸ S.classUnipotent c') := {x | x = a x • x}
  let wt (γ : S.G E) : (InfinitePlace E → 𝔰.G₁) → ENNReal :=
    (S.classCutoff c' (S.ratToInf γ)⁻¹ * reps.indicator 1 γ) • φ γ
  have h_wt (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) :
      ∑' u : S.classUnipotent c × S.classUnipotent c',
        wt (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1 := by
    let x : S.G E ⧸ S.classUnipotent c' := γ
    have coe_mul (u : S.classUnipotent c) : (↑(u * γ) : S.G E ⧸ S.classUnipotent c') = u • x := rfl
    calc _ = ∑' u : S.classUnipotent c, reps.indicator 1 (u • x) * φ (u • x)
           (S.ratToInf u * y) := by
          simp [wt, tsum_classCutoff_eq_one, coe_mul, ENNReal.tsum_prod', ENNReal.tsum_mul_right]
      _ = ∑' u : stabilizer (S.classUnipotent c) (a x • x),
            φ (a x • x) (S.ratToInf (u * a x : S.classUnipotent c) * y) :=
          tsum_indicator_smul_eq_tsum_stabilizer ha (fun z u ↦ φ z (S.ratToInf u * y)) x
      _ = 1 := by
          simpa only [Subgroup.coe_mul, map_mul, mul_assoc]
            using hφ_sum (a x • x) (S.ratToInf (a x) * y)
  have h_wt_meas (γ : S.G E) : Measurable (wt γ) := (hφ_meas γ).const_smul _
  obtain ⟨h_hasSum, -⟩ :=
    hasSum_amplitudeSum_of_cutoff (side := side) hT c s c' wt (fun γ _ ↦ h_wt γ) h_wt_meas
  refine h_hasSum.unique (hasSum_zero.congr_fun ?_)
  rintro ⟨γ, hγ, -⟩
  have h_zero : ∫ y : InfinitePlace E → 𝔰.G₁, (φ γ y).toReal • S.besselKernel side γ y = 0 :=
    integral_besselKernel_eq_zero_of_not_charsAgree side (h_not_agree γ hγ) rfl (hφ_cutoff γ)
  simp [wt, mul_smul, integral_smul, h_zero]

end New.Filling

/-!
## Common vectors of two flags

Two matrices `P`, `P'` with columns indexed by `Fin (n + 1)` give two flags, spanned by the first
columns. A common vector is a relation `P *ᵥ x = P' *ᵥ y`. Indices start at `0`.
-/

namespace New
open Matrix Fin

variable {F ι : Type*} [Field F] {n : ℕ} {P P' : Matrix ι (Fin (n + 1)) F}
  {x y : Fin (n + 1) → F} {μ μ' : F} {j l : Fin (n + 1)}

/-- Some vector lies in the span of the columns of index at most `j` of both `P` and `P'`, and
its coefficients at `j` are `μ` and `μ'`. -/
def PairOccursInColumnsAt (P P' : Matrix ι (Fin (n + 1)) F) (μ μ' : F) (j : Fin (n + 1)) : Prop :=
  ∃ x y : Fin (n + 1) → F, P *ᵥ x = P' *ᵥ y ∧ x j = μ ∧ y j = μ' ∧ ∀ b > j, x b = 0 ∧ y b = 0

/-- The index `j` is the top index of the vector with coordinates `x` in one frame and `y` in the
other: the least index above which both vanish. -/
def IsTopIndex (x y : Fin (n + 1) → F) (j : Fin (n + 1)) : Prop :=
  IsLeast {a : Fin (n + 1) | ∀ b > a, x b = 0 ∧ y b = 0} j

/-- Every pair of coordinate vectors `x`, `y` has a top index. -/
lemma exists_isTopIndex (x y : Fin (n + 1) → F) : ∃ j : Fin (n + 1), IsTopIndex x y j :=
  ⟨_, isLeast_csInf ⟨last n, fun b hb ↦ absurd hb b.le_last.not_gt⟩⟩

/-- If `x ≠ 0` and `j` is the least index above which `x` and `y` vanish, then `x j` and `y j` are
not both `0`. -/
lemma IsTopIndex.ne_zero_or_ne_zero (h_top : IsTopIndex x y j) (hx : x ≠ 0) :
    x j ≠ 0 ∨ y j ≠ 0 := by
  by_contra! h_zero
  have h_from (b : Fin (n + 1)) (hb : j ≤ b) : x b = 0 ∧ y b = 0 := by
    obtain rfl | h_lt := hb.eq_or_lt
    exacts [h_zero, h_top.1 b h_lt]
  cases j using Fin.cases with
  | zero => exact hx (funext fun b ↦ (h_from b b.zero_le).1)
  | succ i =>
    exact i.castSucc_lt_succ.not_ge (h_top.2 fun b hb ↦ h_from b (castSucc_lt_iff_succ_le.1 hb))

/-- An index `j` above which the coordinates `x`, `y` vanish, and at which they are not both `0`, is
the top index. -/
lemma isTopIndex_of_ne_zero (h_above : ∀ b > j, x b = 0 ∧ y b = 0) (h_ne : x j ≠ 0 ∨ y j ≠ 0) :
    IsTopIndex x y j :=
  ⟨h_above, fun _ ha ↦ not_lt.1 fun h_lt ↦ not_and_or.2 h_ne (ha j h_lt)⟩

/-- Suppose that whenever `μ`, `μ'` are the coefficients at an index of a common vector of the flags
of `P` and `P'`, they are so at the next index. Then coefficients at `j` are coefficients at every
`l ≥ j`. -/
lemma PairOccursInColumnsAt.of_le
    (h_step : ∀ i : Fin n,
      PairOccursInColumnsAt P P' μ μ' i.castSucc → PairOccursInColumnsAt P P' μ μ' i.succ)
    (h_start : PairOccursInColumnsAt P P' μ μ' j) (hjl : j ≤ l) :
    PairOccursInColumnsAt P P' μ μ' l := by
  induction l using Fin.induction with
  | zero => rwa [Fin.le_zero_iff.1 hjl] at h_start
  | succ i ih =>
    obtain rfl | h_lt := hjl.eq_or_lt
    exacts [h_start, h_step i (ih (le_castSucc_iff.2 h_lt))]

/-- If every linear form `m` that kills the columns of index below `j` of `P` and `P'` takes the
same value on `μ` times column `j` of `P` and `μ'` times column `j` of `P'`, then some vector lies
in the span of the columns of index at most `j` of both `P` and `P'`, with coefficients `μ`, `μ'` at
`j`. -/
lemma pairOccursInColumnsAt_of_forall_mul_vecMul_eq [Fintype ι]
    (h_forms : ∀ m : ι → F, (∀ b < j, (m ᵥ* P) b = 0) → (∀ b < j, (m ᵥ* P') b = 0) →
      μ * (m ᵥ* P) j = μ' * (m ᵥ* P') j) : PairOccursInColumnsAt P P' μ μ' j := by
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_mulVec_eq_of_annihilator P P' (Set.Iio j) (Set.Iio j)
    (Pi.single j μ) (Pi.single j μ') fun m hm hm' ↦ by simpa [mul_comm] using h_forms m hm hm'
  exact ⟨x, y, hxy, by simp [hx], by simp [hy],
    fun b hb ↦ by simp [hx b hb.not_gt, hy b hb.not_gt, hb.ne']⟩

/-- Let `w` vanish up to the index `i` and `x` above it. The vector `cons 0 (init x)` is `x` shifted
up by one index, so only one term remains in the sum of the products `w (b + 1) * x b`. -/
lemma dotProduct_cons_zero_init {R : Type*} [CommRing R] {w x : Fin (n + 1) → R} {i : Fin n}
    (hw : ∀ b < i.succ, w b = 0) (hx : ∀ b > i.castSucc, x b = 0) :
    w ⬝ᵥ cons 0 (init x) = x i.castSucc * w i.succ := by
  rw [dotProduct, sum_univ_succ, cons_zero, mul_zero, zero_add,
    Fintype.sum_eq_single i fun b hb ↦ ?_, cons_succ, init, mul_comm]
  obtain h_lt | h_gt := hb.lt_or_gt
  · simp [hw b.succ (succ_lt_succ_iff.2 h_lt)]
  · simp [init, hx b.castSucc (castSucc_lt_castSucc_iff.2 h_gt)]

end New

/-!
## Moving common vectors up the flags over `E`

Here `f = frameImage 1` is the frame `(e₁, …, e_ϱ, z)` and `γ f = frameImage γ` its image under the
rational element `γ`. The predicate `PairOccursAt γ` is `PairOccursInColumnsAt` for these two
matrices.
-/

namespace New.Filling
open Matrix Fin Set
open scoped Classical

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} {γ : S.G E}

/-- One step up the flags of the frame `f = (e₁, …, e_ϱ, z)`, the basis vectors at the indices
`𝔰.besselFrame`, and of its image `γ f`. Let the characters of the rational element `γ` agree:
`S.unipotentChar` takes equal values on rational `u`, `u'` in the unipotent group `besselU` with
`u γ = γ u'`. Suppose that `f x = γ f y` for coordinates `x`, `y` that vanish above `j` and equal
`μ`, `μ'` at `j`. Then `f x' = γ f y'` for some `x'`, `y'` that vanish above `j + 1` and equal `μ`,
`μ'` at `j + 1`. -/
lemma pairOccursAt_succ (h_agree : S.CharsAgree γ) {μ μ' : E} (j : Fin 𝔰.ϱ)
    (h_occurs : PairOccursAt γ μ μ' j.castSucc) : PairOccursAt γ μ μ' j.succ := by
  obtain ⟨x, y, hxy, rfl, rfl, h_above⟩ := h_occurs
  have hx : ∀ b ≥ j.succ, x b = 0 := fun b hb ↦ (h_above b (castSucc_lt_iff_succ_le.2 hb)).1
  have hy : ∀ b ≥ j.succ, y b = 0 := fun b hb ↦ (h_above b (castSucc_lt_iff_succ_le.2 hb)).2
  -- It suffices that every form `m` that kills `f b` and `γ f b` for `b ≤ j` takes the same value
  -- on `μ f (j + 1)` and `μ' γ f (j + 1)`. These values are sums over the shifted coordinates.
  refine pairOccursInColumnsAt_of_forall_mul_vecMul_eq fun m hm hm' ↦ ?_
  rw [← dotProduct_cons_zero_init hm hx, ← dotProduct_cons_zero_init hm' hy]
  -- Two elements of `E` are equal once `ψf` agrees on all their multiples by `t : E`.
  refine (algebraMap E (𝔸f E)).injective (eq_of_forall_ψf_mul_eq
    (denseRange_algebraMap_finAdele.eq fun t ↦ ?_))
  -- `v` represents the form `m ᵥ* γ`, so `γ *ᵥ v` represents `m`.
  obtain ⟨v, hv⟩ := exists_star_vecMul_eq S.ratGram (m ᵥ* γ)
  have hγv : star (γ *ᵥ v) ᵥ* S.ratGram = m ᵥ* 1 := by
    rw [star_mulVec, vecMul_vecMul, ← U.form_mul_inv_eq, ← vecMul_vecMul, hv]
    simp
  -- The Eichler maps `u` along `r • x` and `w` along `r • y` lie in `besselU`; the factor `r`
  -- cancels the constants in the character. As `x`, `y` give the same vector, `u * γ = γ * w`.
  let r : E := S.M * S.deltaE * -t
  obtain ⟨u, hu, hu_sum, hu_eichler⟩ := exists_mem_besselU_eq_eichlerMap j.succ x r hγv hx hm
  obtain ⟨w, hw, hw_sum, hw_eichler⟩ := exists_mem_besselU_eq_eichlerMap j.succ y r hv hy hm'
  have h_comm : u * γ = γ * w := by
    ext : 2
    simp [hu_eichler, hw_eichler, hxy, ext_iff_mulVec, U.form_mulVec_mulVec, ← mulVec_mulVec,
      frameImage_mulVec γ.val.val, eichlerMap_mulVec, mulVec_sub, mulVec_add, mulVec_smul]
  -- So the agreement of the characters at `u` and `w` is the claim.
  have coeHom_apply (c : Circle) : Circle.coeHom c = c := rfl
  have h_char (z : S.G E) (d : E) (hz : simpleRootSum z = r * d) :
      S.unipotentChar (S.ratToFin z) = ψf E (algebraMap E (𝔸f E) t * algebraMap E (𝔸f E) d) := by
    simp [hz, r, unipotentChar, ideleM, selfDualChar, ratToFin, simpleRootSum_adelicToFin,
      ← map_mul, mul_assoc, Nat.Prime.ne_zero, coeHom_apply]
  exact Circle.ext ((h_char u _ hu_sum).symm.trans
    ((h_agree u hu w hw h_comm).trans (h_char w _ hw_sum)))

/-- Let the characters of `γ` agree. If `μ`, `μ'` are the coefficients at `j` of a common vector of
the flags of the frame `f` and of `γ f`, they are the coefficients of a common vector at every index
`l ≥ j`. -/
lemma CharsAgree.pairOccursAt_mono (h_agree : S.CharsAgree γ) {μ μ' : E}
    {j l : Fin (𝔰.ϱ + 1)} (h_occurs : PairOccursAt γ μ μ' j) (hjl : j ≤ l) :
    PairOccursAt γ μ μ' l :=
  PairOccursInColumnsAt.of_le (pairOccursAt_succ h_agree) h_occurs hjl

/-- Let the characters of `γ` agree. If `μ`, `μ'` are the coefficients at `j` of a common vector of
the flags of the frame `f` and of `γ f`, then `μ μ̄ = μ' μ̄'`. -/
lemma CharsAgree.mul_star_eq_of_pairOccursAt (h_agree : S.CharsAgree γ) {μ μ' : E}
    {j : Fin (𝔰.ϱ + 1)} (h_occurs : PairOccursAt γ μ μ' j) :
    μ * star μ = μ' * star μ' := by
  -- The vector at the last index has norm `-N μ μ̄` in one frame and `-N μ' μ̄'` in the other.
  obtain ⟨x, y, hxy, rfl, rfl, -⟩ : PairOccursAt γ μ μ' 𝔰.top :=
    h_agree.pairOccursAt_mono h_occurs j.le_last
  rw [mul_comm, star_mul_last_eq_of_frameImage_eq hxy, mul_comm]

/-- Let the characters of `γ` agree. If `μ`, `μ'` are the coefficients at `j` of a common vector of
the flags of the frame `f` and of `γ f`, then `μ μ̄ = μ' μ̄'`, and `μ`, `μ'` are the coefficients of
a common vector at every index `l ≥ j`. -/
lemma mul_star_eq_and_pairOccursAt_of_le (h_agree : S.CharsAgree γ) (j : Fin (𝔰.ϱ + 1)) (μ μ' : E)
    (h_occurs : PairOccursAt γ μ μ' j) :
    μ * star μ = μ' * star μ' ∧ ∀ l ≥ j, PairOccursAt γ μ μ' l :=
  ⟨h_agree.mul_star_eq_of_pairOccursAt h_occurs,
    fun _ hl ↦ h_agree.pairOccursAt_mono h_occurs hl⟩

/-- Let the characters of `γ` agree, and let a common vector, with coordinates `x` in the frame `f`
and `y` in `γ f`, have the top index `j` (the least index above which `x` and `y` vanish). Then
`x j` and `y j` have the same norm. -/
lemma CharsAgree.mul_star_eq_of_isTopIndex (h_agree : S.CharsAgree γ) {x y : Fin (𝔰.ϱ + 1) → E}
    {j : Fin (𝔰.ϱ + 1)} (hxy : frameImage 1 *ᵥ x = frameImage γ *ᵥ y)
    (h_top : IsTopIndex x y j) : x j * star (x j) = y j * star (y j) :=
  h_agree.mul_star_eq_of_pairOccursAt ⟨x, y, hxy, rfl, rfl, h_top.1⟩

/-- Let `γ` satisfy `S.CharsAgree γ`. Let `x ≠ 0` and `y` be the coordinates of one vector in the
frames `frameImage 1` and `frameImage γ`, with top index `j`. Then `x j * star (x j) ≠ 0`. -/
lemma CharsAgree.mul_star_ne_zero_of_isTopIndex (h_agree : S.CharsAgree γ) {x y : Fin (𝔰.ϱ + 1) → E}
    {j : Fin (𝔰.ϱ + 1)} (hxy : frameImage 1 *ᵥ x = frameImage γ *ᵥ y) (hx : x ≠ 0)
    (h_top : IsTopIndex x y j) : x j * star (x j) ≠ 0 := by
  obtain hxj | hyj : x j ≠ 0 ∨ y j ≠ 0 := h_top.ne_zero_or_ne_zero hx
  · exact mul_ne_zero hxj (star_ne_zero.2 hxj)
  · rw [h_agree.mul_star_eq_of_isTopIndex hxy h_top]
    exact mul_ne_zero hyj (star_ne_zero.2 hyj)

/-- Suppose `S.CharsAgree γ`: the unipotent character takes equal values at `u` and `γ⁻¹ u γ` for
every rational `u` in `𝖴 ∩ γ 𝖴 γ⁻¹`. Let a nonzero vector have coordinates `x` in the frame
`f = (e₁,…,e_ϱ,z)` (`frameImage 1`) and `y` in `γ f` (`frameImage γ`), with top index `j`. Then for
every `l ≥ j` some such common vector has top index `l` and the coefficients `x j`, `y j` at `l`. -/
lemma CharsAgree.exists_isTopIndex_apply_eq (h_agree : S.CharsAgree γ) {x y : Fin (𝔰.ϱ + 1) → E}
    {j l : Fin (𝔰.ϱ + 1)} (hxy : frameImage 1 *ᵥ x = frameImage γ *ᵥ y) (hx : x ≠ 0)
    (h_top : IsTopIndex x y j) (hjl : j ≤ l) :
    ∃ x' y' : Fin (𝔰.ϱ + 1) → E,
      frameImage 1 *ᵥ x' = frameImage γ *ᵥ y' ∧
      IsTopIndex x' y' l ∧
      x' l = x j ∧
      y' l = y j := by
  obtain ⟨x', y', hxy', hx', hy', h_above⟩ : PairOccursAt γ (x j) (y j) l :=
    h_agree.pairOccursAt_mono ⟨x, y, hxy, rfl, rfl, h_top.1⟩ hjl
  have h_not_both : x' l ≠ 0 ∨ y' l ≠ 0 := by
    rw [hx', hy']
    exact h_top.ne_zero_or_ne_zero hx
  exact ⟨x', y', hxy', isTopIndex_of_ne_zero h_above h_not_both, hx', hy'⟩

/-- Let `γ` satisfy `S.CharsAgree γ`. Let `x ≠ 0` and `y` be the coordinates of one vector in the
frames `frameImage 1` and `frameImage γ`, with top index `j`. Then
`x j * star (x j) = y j * star (y j) ≠ 0`. For every `l ≥ j`, some such pair `x'`, `y'` has top
index `l` with `x' l = x j` and `y' l = y j`. -/
lemma mul_star_eq_and_ne_zero_and_exists_isTopIndex (h_agree : S.CharsAgree γ)
    {x y : Fin (𝔰.ϱ + 1) → E} {j : Fin (𝔰.ϱ + 1)}
    (hxy : frameImage 1 *ᵥ x = frameImage γ *ᵥ y) (hx : x ≠ 0) (h_top : IsTopIndex x y j) :
    x j * star (x j) = y j * star (y j) ∧
    x j * star (x j) ≠ 0 ∧
    ∀ l ≥ j, ∃ x' y' : Fin (𝔰.ϱ + 1) → E,
      frameImage 1 *ᵥ x' = frameImage γ *ᵥ y' ∧
      IsTopIndex x' y' l ∧
      x' l = x j ∧
      y' l = y j :=
  ⟨h_agree.mul_star_eq_of_isTopIndex hxy h_top,
    h_agree.mul_star_ne_zero_of_isTopIndex hxy hx h_top,
    fun _ hl ↦ h_agree.exists_isTopIndex_apply_eq hxy hx h_top hl⟩

end New.Filling

/-!
## Common vectors of two frames modulo a place above `M`

For an element of the stabilizer of the lattice whose reduction agrees (`New.Filling.Agrees`), the
coefficients at one index of a common vector of the two flags modulo a place `w` above `M` are also
the coefficients at the next index of some common vector, and so up to the last index. Here `M` is
the product of the two level primes, and a place above `M` is a pair of a chosen place and a Boolean
that is true for its conjugate.
-/

namespace New.Filling

open Matrix Fin Nat Function intGL Units IsAdelic

section
variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}

/-- For `w`, a chosen place of norm `S.levelPrime i` together with a Boolean that says whether to
conjugate first, `S.actionAt (S.reduction k) w` is the integral matrix of `k` reduced entrywise by
`S.reduceAboveM w`. -/
lemma actionAt_reduction (k : S.latticeStabilizer) (w : (Σ i : Fin 2, S.chosenPlaces i) × Bool) :
    S.actionAt (S.reduction k) w =
      (intGL.map (S.reduceAboveM w) ⟨k.val.val, k.property⟩).val := by
  rw [actionAt, ← intGL_map_reduceAboveM]

/-- The action modulo a place `w` above `M` is multiplicative. -/
lemma actionAt_mul (s t : S.ResidueGL) (w : (Σ i : Fin 2, S.chosenPlaces i) × Bool) :
    S.actionAt (s * t) w = S.actionAt s w * S.actionAt t w := by
  simp [actionAt]

/-- Two elements `s`, `t` of `S.ResidueGL` are equal if `S.actionAt s (q, b) = S.actionAt t (q, b)`
for every chosen place `q`. Here `b` is fixed: either `b = false` (modulo the chosen places) or
`b = true` (modulo their conjugates). -/
lemma eq_of_forall_actionAt_eq (b : Bool) {s t : S.ResidueGL}
    (h_action : ∀ q : Σ i : Fin 2, S.chosenPlaces i,
      S.actionAt s (q, b) = S.actionAt t (q, b)) : s = t :=
  funext₂ fun i v ↦ (S.idOrInvAdjoint b).injective (Units.ext (h_action ⟨i, v⟩))

/-- Conjugation exchanges the reductions at a chosen place and at its conjugate. -/
lemma reduceAboveM_star (q : Σ i : Fin 2, S.chosenPlaces i) (b : Bool) (z : Ô E) :
    S.reduceAboveM (q, b) (star z) = S.reduceAboveM (q, !b) z := by
  cases b <;> simp [reduceAboveM, starRingEnd_apply]

/-- Let `w` be a place above `M`, the product of the two level primes: a chosen place, or its
conjugate if the Boolean is true. Residues at `w` lift to integral adeles, `0` to `0`, that vanish
at all other places above `M`. -/
lemma exists_lift_reduceAboveM_eq (w : (Σ i : Fin 2, S.chosenPlaces i) × Bool) :
    ∃ lift : ResField (w.1.snd : FinPlace E) → Ô E,
      lift 0 = 0 ∧
      (∀ t : ResField (w.1.snd : FinPlace E), S.reduceAboveM w (lift t) = t) ∧
      ∀ w' ≠ w, ∀ t : ResField (w.1.snd : FinPlace E), S.reduceAboveM w' (lift t) = 0 := by
  classical
  choose l hl using exists_reduceAboveM_eq (S := S)
  exact ⟨fun t ↦ l (Pi.single w t) - l 0, by simp, by simp [hl], fun w' hw' ↦ by simp [hl, hw']⟩

end

variable {E W : Type} {𝔰 : Shape} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {S : Filling E 𝔰}

/-- Let the coordinates `x` in the frame vanish from `a` on, and let the linear form `m` kill the
frame vectors below `a`; both are integral, and so is `r`. Then some `u` in the stabilizer of the
lattice, an Eichler map, lies in the Bessel unipotent group, and the sum of its superdiagonal
entries on the frame is `r` times the value of `m` on `x` shifted up by one index. Modulo a place
`w` above `M` that divides `star x`, it is `1 + r (f x) m`, where `f x = frameImage 1 *ᵥ x` is the
vector with coordinates `x`. -/
lemma exists_eichler_mem_latticeStabilizer (a : Fin (𝔰.ϱ + 1)) (r : Ô E) (x : Fin (𝔰.ϱ + 1) → Ô E)
    (m : 𝔰.BesselIndex → Ô E) (hx : ∀ b ≥ a, x b = 0) (hm : ∀ b < a, m (𝔰.besselFrame b) = 0) :
    ∃ u : S.latticeStabilizer, u.val ∈ besselU ∧
      simpleRootSum u.val = r * (m ∘ 𝔰.besselFrame ⬝ᵥ cons 0 (init x) : Ô E) ∧
      ∀ w : (Σ i : Fin 2, S.chosenPlaces i) × Bool,
        (∀ i : Fin (𝔰.ϱ + 1), S.reduceAboveM w (star (x i)) = 0) →
        (intGL.map (S.reduceAboveM w) ⟨u, u.property⟩).val =
          1 + S.reduceAboveM w r •
            vecMulVec (frameImage 1 *ᵥ S.reduceAboveM w ∘ x) (S.reduceAboveM w ∘ m) := by
  -- Take the Eichler map over `Ô` for the vector `v` with `h(v, ·) = m` and an integral `τ` of
  -- trace `1`, and push it into the finite adeles.
  obtain ⟨v, hv⟩ := exists_star_vecMul_eq (S.latticeMiddle (Ô E)).splitGram m
  obtain ⟨-, -, τ, hτ_mem, -, -, hτ⟩ := exists_skew_unit (A := 𝔸f E)
  have : Floors.TraceOne (Ô E) := ⟨⟨τ, hτ_mem⟩, Subtype.ext hτ⟩
  obtain ⟨u, hu, hu_sum, hu_eq⟩ := exists_mem_besselU_eq_eichlerMap a x r hv hx hm
  let u' : S.GFin := U.map (Ô E).subtype (by simp) (map_splitGram_latticeMiddle _) u
  have hu'_sum : simpleRootSum u' = (simpleRootSum u : Ô E) := (map_sum (Ô E).subtype _ _).symm
  refine ⟨⟨u', _, rfl⟩, hu.map_mem_agreeWithOneOn _, by rw [hu'_sum, hu_sum, Subring.coe_mul],
    fun w hw ↦ ?_⟩
  change u.val.val.map (S.reduceAboveM w) = _
  -- The last term of `eichlerMap` carries the factor `star x`, so it vanishes modulo `w`.
  simp [hu_eq, eichlerMap, hv, hw, vecMulVec_apply, apply_ite, ← ext_iff, dotProduct, mulVec,
    vecMul, Matrix.one_apply]

/-- Work modulo a place `w` above `M`. Let `k` stabilize the lattice, let its reduction agree, and
write `γ` for `S.actionAt (S.reduction k) w`, the matrix of `k` modulo `w`. Suppose that
`f x = γ f y` for the frame `f`, where the coordinates `x` and `y` vanish from `a` on, and let the
linear form `m` kill `f_c` and `γ f_c` for `c < a`. Then `m` takes the same value on the two vectors
obtained by shifting the coordinates up by one index. -/
lemma vecMul_frameImage_dotProduct_cons_init_eq_of_agrees {k : S.latticeStabilizer}
    (hk : S.Agrees (S.reduction k))
    (w : (Σ i : Fin 2, S.chosenPlaces i) × Bool) {a : Fin (𝔰.ϱ + 1)}
    {m : 𝔰.BesselIndex → ResField (w.1.snd : FinPlace E)}
    {x y : Fin (𝔰.ϱ + 1) → ResField (w.1.snd : FinPlace E)}
    (hxy : frameImage 1 *ᵥ x = frameImage (S.actionAt (S.reduction k) w) *ᵥ y)
    (hx : ∀ c ≥ a, x c = 0) (hy : ∀ c ≥ a, y c = 0)
    (hm_frame : ∀ c < a, (m ᵥ* frameImage 1) c = 0)
    (hm_image : ∀ c < a, (m ᵥ* frameImage (S.actionAt (S.reduction k) w)) c = 0) :
    m ᵥ* frameImage 1 ⬝ᵥ cons 0 (init x) =
      m ᵥ* frameImage (S.actionAt (S.reduction k) w) ⬝ᵥ cons 0 (init y) := by
  -- Lift the data to `Ô` and compare the unipotent character on two Eichler maps `u`, `u'` with
  -- `u k ≡ k u'` modulo `M`.
  obtain ⟨p, b⟩ := w
  obtain ⟨lift, lift_zero, h_lift, h_lift_ne⟩ : ∃ lift : ResField p.2.val → Ô E, lift 0 = 0 ∧
      (∀ t : ResField p.2.val, S.reduceAboveM (p, b) (lift t) = t) ∧
      ∀ w' ≠ (p, b), ∀ t : ResField p.2.val, S.reduceAboveM w' (lift t) = 0 :=
    exists_lift_reduceAboveM_eq (p, b)
  set γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField p.2.val) :=
    S.actionAt (S.reduction k) (p, b) with hγ
  have h_star (q : Σ i : Fin 2, S.chosenPlaces i) (t : ResField p.2.val) :
      S.reduceAboveM (q, b) (star (lift t)) = 0 := by
    rw [reduceAboveM_star, h_lift_ne (q, !b) (by simp) t]
  -- `liftPairing 1 x` and `liftPairing γ y` lift the two sides to `Ô`; it suffices that `M` divides
  -- their difference.
  let liftPairing (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField p.2.val))
      (z : Fin (𝔰.ϱ + 1) → ResField p.2.val) : Ô E :=
    lift ∘ (m ᵥ* frameImage g) ⬝ᵥ cons 0 (init (lift ∘ z))
  suffices h_dvd : S.ideleM⁻¹ • (liftPairing 1 x - liftPairing γ y).val ∈ Ô E by
    simpa [liftPairing, dotProduct, sum_univ_succ, init, h_lift, sub_eq_zero] using
      (S.inv_ideleM_smul_mem_iff _).1 h_dvd (p, b)
  -- `Ô` is self-dual for `S.selfDualChar`, so we test against every `r ∈ Ô`.
  refine (S.forall_selfDualChar_mul_eq_one_iff _).1 fun r ↦ ?_
  -- The Eichler map along `r` times the lift of `z` for the lift of the form `m g`.
  have h_eichler (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField p.2.val))
      (z : Fin (𝔰.ϱ + 1) → ResField p.2.val) (hz : ∀ c ≥ a, z c = 0)
      (hm_g : ∀ c < a, (m ᵥ* frameImage g) c = 0) :
      ∃ u : S.latticeStabilizer, u.val ∈ besselU ∧ simpleRootSum u.val = r * liftPairing g z ∧
        S.actionAt (S.reduction u) (p, b) =
          1 + S.reduceAboveM (p, b) r • vecMulVec (frameImage 1 *ᵥ z) (m ᵥ* g) ∧
        ∀ q ≠ p, S.actionAt (S.reduction u) (q, b) = 1 := by
    obtain ⟨u, hu, hu_sum, hu_red⟩ := exists_eichler_mem_latticeStabilizer a r (lift ∘ z)
      (lift ∘ (m ᵥ* g))
      (fun c hc ↦ (congrArg lift (hz c hc)).trans lift_zero)
      fun c hc ↦ (congrArg lift (hm_g c hc)).trans lift_zero
    refine ⟨u, hu, hu_sum, ?_, fun q hq ↦ ?_⟩
    · simp [actionAt_reduction, hu_red _ fun c ↦ h_star p (z c), comp_def, h_lift]
    · simp [actionAt_reduction, hu_red _ fun c ↦ h_star q (z c), comp_def,
        h_lift_ne (q, b) (by simpa using hq), ← Pi.zero_def]
  obtain ⟨u, hu, hu_sum, hu_at, hu_ne⟩ := h_eichler 1 x hx hm_frame
  obtain ⟨u', hu', hu'_sum, hu'_at, hu'_ne⟩ := h_eichler γ y hy hm_image
  have h_red : S.reduction u * S.reduction k = S.reduction k * S.reduction u' := by
    refine eq_of_forall_actionAt_eq b fun q ↦ ?_
    obtain rfl | hq := eq_or_ne q p
    · -- Both sides are `γ + r (f x) (m γ)`.
      have h_vec : γ *ᵥ frameImage 1 *ᵥ y = frameImage 1 *ᵥ x := by
        rw [hxy, mulVec_frameImage_one_mulVec]
      simp [actionAt_mul, hu_at, hu'_at, ← hγ, add_mul, mul_add, vecMulVec_mul, mul_vecMulVec,
        h_vec]
    · simp [actionAt_mul, hu_ne q hq, hu'_ne q hq]
  have h_char : S.selfDualChar (S.ideleM⁻¹.val * (r * liftPairing 1 x)) =
      S.selfDualChar (S.ideleM⁻¹.val * (r * liftPairing γ y)) := by
    simpa only [unipotentChar, hu_sum, hu'_sum] using hk u u' hu hu' h_red
  simpa [smul_def, mul_sub, mul_left_comm r.val, AddChar.map_sub_eq_div,
    (S.selfDualChar.val_isUnit _).div_eq_one_iff_eq] using h_char

/-- One step up modulo a place above `M = p₀ p₁`, the product of the two level primes. Here `w` is a
chosen place, of norm `p₀` or `p₁`, with a Boolean that picks this place or its conjugate. Let `k`
stabilize the lattice, and let its reduction `S.reduction k` agree: integral unipotent `u`, `u'`
with `u k ≡ k u'` modulo `M` have the same unipotent character. Let
`s = S.actionAt (S.reduction k) w` be the matrix of `k` modulo the picked place. Let `A_{≤j}` be the
span of the frame vectors `(e₁,…,e_ϱ,z)` of index at most `j`. If `μ`, `μ'` are the coefficients at
`j` of a vector of `A_{≤j} ∩ s A_{≤j}`, they are also the coefficients at `j + 1` of some vector of
`A_{≤j+1} ∩ s A_{≤j+1}`. -/
lemma pairOccursInColumnsAt_succ_of_agree {k : S.latticeStabilizer} (hk : S.Agrees (S.reduction k))
    (w : (Σ i : Fin 2, S.chosenPlaces i) × Bool) {μ μ' : ResField (w.1.snd : FinPlace E)}
    (j : Fin 𝔰.ϱ)
    (h_occurs : PairOccursInColumnsAt (frameImage 1) (frameImage (S.actionAt (S.reduction k) w))
      μ μ' j.castSucc) :
    PairOccursInColumnsAt (frameImage 1) (frameImage (S.actionAt (S.reduction k) w)) μ μ'
      j.succ := by
  obtain ⟨x, y, hxy, rfl, rfl, h_above⟩ := h_occurs
  have hx : ∀ b ≥ j.succ, x b = 0 := fun b hb ↦ (h_above b (castSucc_lt_iff_succ_le.2 hb)).1
  have hy : ∀ b ≥ j.succ, y b = 0 := fun b hb ↦ (h_above b (castSucc_lt_iff_succ_le.2 hb)).2
  refine pairOccursInColumnsAt_of_forall_mul_vecMul_eq fun m hm hm' ↦ ?_
  rw [← dotProduct_cons_zero_init hm hx, ← dotProduct_cons_zero_init hm' hy]
  exact vecMul_frameImage_dotProduct_cons_init_eq_of_agrees hk w hxy hx hy hm hm'

/-- Let `s` be the reduction `S.reduction k` of an element `k` of the lattice stabilizer, and let
`s` agree: the unipotent character takes equal values on integral unipotent `u`, `u'` with
`u s = s u'` after reduction. Here `w` is a chosen place above `M = p₀ p₁`, the product of the two
level primes, with a Boolean that picks this place or its conjugate. Suppose the span of the frame
`f = (e₁,…,e_ϱ,z)` and that of `s f` share a nonzero vector modulo this place. Then `f x = s f y`
modulo it for some `x`, `y` whose entries `μ`, `μ'` at the last index `𝔰.top` are not both `0`. -/
lemma exists_pairOccursInColumnsAt_top_of_meetsAt {k : S.latticeStabilizer}
    (hk : S.Agrees (S.reduction k))
    {w : (Σ i : Fin 2, S.chosenPlaces i) × Bool} (h_meet : S.MeetsAt (S.reduction k) w) :
    ∃ μ μ' : ResField (w.1.snd : FinPlace E),
      (μ ≠ 0 ∨ μ' ≠ 0) ∧
      PairOccursInColumnsAt (frameImage 1) (frameImage (S.actionAt (S.reduction k) w)) μ μ'
        𝔰.top := by
  -- Start at the top index of the shared vector and go up to the last index.
  obtain ⟨x, y, hx, hxy⟩ := h_meet
  obtain ⟨j, h_top⟩ := exists_isTopIndex x y
  exact ⟨x j, y j, h_top.ne_zero_or_ne_zero hx,
    PairOccursInColumnsAt.of_le (pairOccursInColumnsAt_succ_of_agree hk w)
    ⟨x, y, hxy, rfl, rfl, h_top.1⟩ j.le_last⟩

/-- Let `s : S.ResidueGL` be a tuple of invertible matrices over the residue fields at the places
`S.chosenPlaces i` (of norm p₀ or p₁). Let `δ : Ô E` have conjugate a unit of `𝔸f E`, and let
`S.reduceAboveM w δ = 0` (reduction modulo `w`, after conjugation if the Boolean of `w` is true) at
each chosen `w` where `s` meets: modulo `w`, the span of the frame (e₁,…,e_ϱ,z) and its image under
`s` share a nonzero vector. Then `S.meetNorm s`, the norm of the product of these places, is at most
the generalised index of the conjugate of `δ`: the inverse of the factor by which it scales Haar
measure, here the order of `Ô / δ Ô`. -/
lemma meetNorm_le_genIndex_star {s : S.ResidueGL} {δ : Ô E} (h_unit : IsUnit (star (δ : 𝔸f E)))
    (h_vanish : ∀ w : (Σ i : Fin 2, S.chosenPlaces i) × Bool,
      S.MeetsAt s w → S.reduceAboveM w δ = 0) :
    (S.meetNorm s : ℝ) ≤ genIndex (star (δ : 𝔸f E)) := by
  classical
  -- The index is `|Ô / δ|`, and `Ô / δ` maps onto the product of the residue fields at the set `A`
  -- of places where `s` meets.
  have h_index : genIndex (star (δ : 𝔸f E)) = Nat.card (Ô E ⧸ Ideal.span {δ}) := by
    simpa using genIndex_eq_card isOpen_Ô isCompact_Ô δ.property (by simpa using h_unit)
  have h_finite : Finite (Ô E ⧸ Ideal.span {δ}) := finite_of_card_ne_zero
    (Nat.cast_ne_zero.1 (h_index.symm.trans_ne (genIndex_pos h_unit.unit).ne'))
  let A : Finset ((Σ i : Fin 2, S.chosenPlaces i) × Bool) := {w | S.MeetsAt s w}
  let π : Ô E →+* ∀ w : A, ResField w.val.1.snd.val := RingHom.pi fun w ↦ S.reduceAboveM w.val
  have h_onto : Surjective π := fun t ↦ by
    obtain ⟨y, hy⟩ := S.exists_reduceAboveM_eq fun w ↦ if h : w ∈ A then t ⟨w, h⟩ else 0
    exact ⟨y, funext fun w ↦ by simp [π, hy]⟩
  have h_ker : Ideal.span {δ} ≤ RingHom.ker π := by simpa [π, A, funext_iff] using h_vanish
  rw [h_index, Nat.cast_le]
  calc S.meetNorm s = ∏ w ∈ A, S.levelPrime w.1.fst := rfl
    _ = Nat.card (∀ w : A, ResField w.val.1.snd.val) := by
      simp [card_pi, card_resField_eq_levelPrime, ← A.prod_attach]
    _ ≤ Nat.card (Ô E ⧸ Ideal.span {δ}) :=
      card_le_card_of_surjective _ (Ideal.Quotient.lift_surjective_of_surjective _ h_ker h_onto)

variable (𝔰) in
/-- The two indices of the pair of frames `(f | k f)` that belong to the last vector of `f` and to
the last vector of `k f`, listed along the bijection `ρ` of `W` with a set of two elements. -/
def lastIndices (ρ : W ≃ Unit ⊕ Unit) : W → Fin (𝔰.ϱ + 1) ⊕ Fin (𝔰.ϱ + 1) :=
  Sum.map (fun _ : Unit ↦ 𝔰.top) (fun _ : Unit ↦ 𝔰.top) ∘ ρ

/-- Let `w` be a chosen place of `E`, with a Boolean that says whether to conjugate first. Let the
reduction of `k` agree: integral unipotent `u`, `u'` with `u k ≡ k u'` have the same unipotent
character. Let `f = (e₁, …, e_ϱ, z)` be the frame, and let the spans of `f` and `k f` share a
nonzero vector modulo `w`. Let `K` be the matrix of `k` over `Ô`, and let `Q = T (f | K f)` for an
integral matrix `T` whose two rows are indexed by `W`. Suppose all columns of `Q` vanish except the
two at the last index of `f` and of `K f`, which `lastIndices 𝔰 ρ` lists. Then the determinant of
these two columns vanishes modulo `w`. -/
lemma reduceAboveM_det_eq_zero_of_meetsAt {k : S.latticeStabilizer} (hk : S.Agrees (S.reduction k))
    {w : (Σ i : Fin 2, S.chosenPlaces i) × Bool} (h_meet : S.MeetsAt (S.reduction k) w)
    [Fintype W] [DecidableEq W] (ρ : W ≃ Unit ⊕ Unit) {T : Matrix W 𝔰.BesselIndex (Ô E)}
    {K : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E)}
    (hK : K.map (Ô E).subtype = (k : S.GFin).val.val)
    {Q : Matrix W (Fin (𝔰.ϱ + 1) ⊕ Fin (𝔰.ϱ + 1)) (Ô E)}
    (hQ : Q = T * (frameImage 1).fromCols (frameImage K))
    (h_left : ∀ (a : Fin 𝔰.ϱ) (j : W), Q j (Sum.inl a.castSucc) = 0)
    (h_right : ∀ (a : Fin 𝔰.ϱ) (j : W), Q j (Sum.inr a.castSucc) = 0) :
    S.reduceAboveM w (Q.submatrix id (lastIndices 𝔰 ρ)).det = 0 := by
  by_contra h_ne
  obtain ⟨μ, μ', h_not_both, x, y, hxy, rfl, rfl, -⟩ :
      ∃ μ μ' : ResField (w.1.snd : FinPlace E), (μ ≠ 0 ∨ μ' ≠ 0) ∧
        PairOccursInColumnsAt (frameImage 1) (frameImage (S.actionAt (S.reduction k) w)) μ μ'
          𝔰.top :=
    exists_pairOccursInColumnsAt_top_of_meetsAt hk h_meet
  have h_red : S.actionAt (S.reduction k) w = K.map (S.reduceAboveM w) := by
    rw [actionAt_reduction]
    ext a b
    exact congrArg (S.reduceAboveM w) (Subtype.ext (congrFun₂ hK a b).symm)
  rw [h_red] at hxy
  -- Modulo `w`, `Q` kills `(x, -y)`, and only the two last columns of `Q` take part in the product.
  have h_ker : Q.map (S.reduceAboveM w) *ᵥ (x ⊕ᵥ -y) = 0 := by
    simp [hQ, ← mulVec_mulVec, ← submatrix_map, mulVec_neg, hxy, fromCols_map,
      -Bool.cond_eq_ite]
  have h_ker_last : (S.reduceAboveM w).mapMatrix (Q.submatrix id (lastIndices 𝔰 ρ)) *ᵥ
      ((x ⊕ᵥ -y) ∘ lastIndices 𝔰 ρ) = 0 := by
    simpa [funext_iff, mulVec_eq_sum, sum_univ_castSucc, reindex_equiv ρ.symm, lastIndices, h_left,
      h_right] using h_ker
  have h_last : x 𝔰.top = 0 ∧ y 𝔰.top = 0 := by
    simpa [lastIndices, funext_iff, reindex_equiv ρ.symm] using
      eq_zero_of_mulVec_eq_zero (by rwa [← RingHom.map_det]) h_ker_last
  exact not_and_or.2 h_not_both h_last

/-- Let `k` stabilize the lattice, and let its reduction agree: integral unipotent `u`, `u'` with
`u k ≡ k u'` modulo `M`, the product of the two level primes, have the same unipotent character. Let
`t` be an integral matrix whose two columns are indexed by `W`. Let `P = (f | k f)ᴴ t`, where
`framePair k` is the matrix `(f | k f)` of the frame `f = (e₁, …, e_ϱ, z)` and its image. Suppose
all rows of `P` vanish except the two at the last index of `f` and of `k f`, which `lastIndices 𝔰 ρ`
lists, and that their determinant is a unit of the finite adeles. Then `meetNorm`, the norm of the
product of the places above `M` modulo which the spans of `f` and `k f` share a nonzero vector, is
at most the generalised index `genIndex` of the determinant: the inverse of the factor by which it
scales Haar measure. -/
lemma meetNorm_le_genIndex_det {k : S.latticeStabilizer} (hk : S.Agrees (S.reduction k))
    [Fintype W] [DecidableEq W] {t : Matrix 𝔰.BesselIndex W (𝔸f E)} (ht : IsIntMatrix (Ô E) t)
    (h_zero : ((framePair k.val)ᴴ * t).submatrix (Sum.map castSucc castSucc) id = 0)
    (ρ : W ≃ Unit ⊕ Unit)
    (h_unit : IsUnit (((framePair k.val)ᴴ * t).submatrix (lastIndices 𝔰 ρ) id).det) :
    (S.meetNorm (S.reduction k) : ℝ) ≤
      genIndex (((framePair k.val)ᴴ * t).submatrix (lastIndices 𝔰 ρ) id).det := by
  -- The determinant is the conjugate of an integral `δ` that vanishes at each place where the
  -- frames meet. `T`, `K` and `Q` are `tᴴ`, `k` and `Pᴴ = tᴴ (f | k f)` as matrices over `Ô`.
  let T : Matrix W 𝔰.BesselIndex (Ô E) := of fun i j ↦ ⟨tᴴ i j, ht.conjTranspose i j⟩
  let K : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E) :=
    (map (RingHom.id (Ô E)) ⟨k.val.val, k.property⟩).val
  let Q : Matrix W (Fin (𝔰.ϱ + 1) ⊕ Fin (𝔰.ϱ + 1)) (Ô E) :=
    T * (frameImage 1).fromCols (frameImage K)
  have hT : T.map (Ô E).subtype = tᴴ := rfl
  have hK : K.map (Ô E).subtype = k.val.val.val := rfl
  have hP : (framePair k.val)ᴴ * t = (Q.map (Ô E).subtype)ᴴ := by
    rw [← conjTranspose_conjTranspose t, ← conjTranspose_mul, Matrix.map_mul, hT, fromCols_map,
      ← submatrix_map, ← submatrix_map, hK, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hP] at h_zero h_unit ⊢
  obtain ⟨h_left, h_right⟩ : (∀ (a : Fin 𝔰.ϱ) (j : W), Q j (Sum.inl a.castSucc) = 0) ∧
      ∀ (a : Fin 𝔰.ϱ) (j : W), Q j (Sum.inr a.castSucc) = 0 := by
    simpa [← ext_iff] using h_zero
  let δ : Ô E := (Q.submatrix id (lastIndices 𝔰 ρ)).det
  have h_det : ((Q.map (Ô E).subtype)ᴴ.submatrix (lastIndices 𝔰 ρ) id).det = star (δ : 𝔸f E) := by
    rw [← conjTranspose_submatrix, det_conjTranspose, submatrix_map, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, Subring.subtype_apply]
  rw [h_det] at h_unit ⊢
  exact meetNorm_le_genIndex_star h_unit fun w h_meet ↦
    reduceAboveM_det_eq_zero_of_meetsAt hk h_meet ρ hK rfl h_left h_right

/-- Let `k` stabilize the lattice, and let its reduction agree. Let `t` be an integral matrix with
two columns, and let `P = (f | k f)ᴴ t` for the frame `f`. Suppose all rows of `P` vanish except the
two at the last index of `f` and of `k f`, which `lastIndices 𝔰 ρ` lists, and that their determinant
is a unit of the finite adeles. Let `x` be at most `meetNorm`, the norm of the product of the places
above `M` modulo which the spans of `f` and `k f` share a nonzero vector. Then `x` is at most the
generalised index of the determinant. -/
lemma le_genIndex_det_of_le_meetNorm {k : S.latticeStabilizer} {x : ℕ}
    (hk : S.Agrees (S.reduction k))
    [Fintype W] [DecidableEq W] {t : Matrix 𝔰.BesselIndex W (𝔸f E)} (ht : IsIntMatrix (Ô E) t)
    (h_zero : ((framePair k.val)ᴴ * t).submatrix (Sum.map castSucc castSucc) id = 0)
    (ρ : W ≃ Unit ⊕ Unit)
    (h_unit : IsUnit (((framePair k.val)ᴴ * t).submatrix (lastIndices 𝔰 ρ) id).det)
    (h_le : x ≤ S.meetNorm (S.reduction k)) :
    (x : ℝ) ≤ genIndex (((framePair k.val)ᴴ * t).submatrix (lastIndices 𝔰 ρ) id).det :=
  (Nat.cast_le.2 h_le).trans (meetNorm_le_genIndex_det hk ht h_zero ρ h_unit)

end New.Filling

/-! ## The cell rank of a term whose characters agree -/

namespace New.Filling
open Matrix Fin Set
open scoped Classical

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} {γ : S.G E}

/-- Let the characters of `γ` agree, and let `j` be the least index from which on one pair `(ζ, 1)`
with `ζ ζ̄ = 1` occurs as the coefficients of a common vector at all indices. Then a nonzero common
vector, with coordinates `x` in the frame `f` and `y` in `γ f`, has nonzero coordinates in both
frames at some index `l ≥ j`. -/
lemma CharsAgree.exists_coords_ne_zero_of_common_vector (h_agree : S.CharsAgree γ) {j : ℕ}
    (h_least : IsLeast {i : ℕ | NormOnePairOccursFrom i γ} j) {x y : Fin (𝔰.ϱ + 1) → E}
    (hxy : frameImage 1 *ᵥ x = frameImage γ *ᵥ y) (hx : x ≠ 0) :
    ∃ l : Fin (𝔰.ϱ + 1), j ≤ l.val ∧ x l ≠ 0 ∧ y l ≠ 0 := by
  -- Let `l` be the top index of the vector. Scale the pair at `l` to `(ζ, 1)`; it occurs at all
  -- higher indices.
  obtain ⟨l, h_top⟩ := exists_isTopIndex x y
  have h_norm : x l * star (x l) = y l * star (y l) := h_agree.mul_star_eq_of_isTopIndex hxy h_top
  have h_ne : x l * star (x l) ≠ 0 := h_agree.mul_star_ne_zero_of_isTopIndex hxy hx h_top
  have hyl : y l ≠ 0 := left_ne_zero_of_mul (h_norm.symm.trans_ne h_ne)
  let ζ : E := (y l)⁻¹ * x l
  have h_pair : PairOccursAt γ ζ 1 l :=
    ⟨(y l)⁻¹ • x, (y l)⁻¹ • y, by rw [mulVec_smul, mulVec_smul, hxy], rfl,
      inv_mul_cancel₀ hyl, fun b hb ↦ by simp [h_top.1 b hb]⟩
  have hζ : ζ * star ζ = 1 := by simpa using h_agree.mul_star_eq_of_pairOccursAt h_pair
  have h_from : NormOnePairOccursFrom l.val γ :=
    ⟨ζ, hζ, fun _ ha ↦ h_agree.pairOccursAt_mono h_pair ha⟩
  exact ⟨l, h_least.2 h_from, left_ne_zero_of_mul h_ne, hyl⟩

/-- Let the characters of `γ` agree: `S.unipotentChar` takes equal values on rational unipotent `u`,
`u'` with `u γ = γ u'`. Let `f = (e₁, …, e_ϱ, z)` be the frame. Let `j` be the least index such that
one pair `(ζ, 1)` with `ζ ζ̄ = 1` occurs as the coefficients of a vector common to the flags of `f`
and of `γ f` at all indices from `j` on. The matrix `S.frameProducts γ` has the entries
`h(f_a, γ f_b)`, where `h` is the hermitian form of the space, with Gram matrix `S.ratGram`. If
`j ≤ 𝔰.ϱ`, the leading minor of order `j` of this matrix is nonzero. -/
lemma CharsAgree.leadingMinor_ne_zero (h_agree : S.CharsAgree γ) {j : Fin (𝔰.ϱ + 2)}
    (h_least : IsLeast {i : ℕ | NormOnePairOccursFrom i γ} j.val) (hj : j.val ≤ 𝔰.ϱ) :
    leadingMinor (S.frameProducts γ) j ≠ 0 := by
  -- Otherwise some `y ≠ 0` vanishes from `j` on and is killed by the first `j` rows.
  intro h_det
  obtain ⟨y, hy_ne, hy⟩ : ∃ y ≠ 0, paddedLeading j (S.frameProducts γ) *ᵥ y = 0 :=
    exists_mulVec_eq_zero_iff.2 (det_paddedLeading.trans h_det)
  have h_rows (a : Fin (𝔰.ϱ + 1)) (ha : a.val < j.val) : (S.frameProducts γ *ᵥ y) a = 0 := by
    simpa [paddedLeading, ha, mulVec, dotProduct] using congrFun hy a
  have h_above (a : Fin (𝔰.ϱ + 1)) (ha : j.val ≤ a.val) : y a = 0 := by
    simpa [paddedLeading, ha.not_gt, mulVec, dotProduct] using congrFun hy a
  -- The remaining rows kill `y` too. For any `w`, some vector shared by `f` and `γ⁻¹ f` has the
  -- coordinates `star w` from `j` on; its pairing with `y` is a multiple of `y 𝔰.top = 0`.
  have h_products : S.frameProducts γ *ᵥ y = 0 := by
    refine dotProduct_eq_zero _ fun w ↦ ?_
    obtain ⟨Y, X, hX, hYX⟩ := exists_frameImage_eq_of_normOnePairOccursFrom h_least.1.inv (star w)
    have h_pair : star X ⬝ᵥ S.frameProducts γ *ᵥ y = -(S.N * star (Y 𝔰.top) * y 𝔰.top) := by
      simpa [star_mulVec_dotProduct] using
        congrArg (star · ⬝ᵥ y) (frameProducts_mulVec_of_frameImage_eq hYX)
    rw [h_above 𝔰.top hj, mul_zero, neg_zero] at h_pair
    rw [← h_pair, dotProduct_comm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    obtain ha | ha := lt_or_ge a.val j.val
    · simp [h_rows a ha]
    · simp [hX a ha]
  -- So `γ f y` lies in the span of the frame `f`, although `y` vanishes from `j` on.
  obtain ⟨x, hxy⟩ := exists_frameImage_eq_of_frameProducts_mulVec_eq_zero h_products
  have hx : x ≠ 0 := by
    rintro rfl
    exact hy_ne (frameImage_mulVec_eq_zero_iff.1 (by simpa using hxy.symm))
  obtain ⟨l, hl, -, hyl⟩ := h_agree.exists_coords_ne_zero_of_common_vector h_least hxy hx
  exact hyl (h_above l hl)

/-- Let the characters of `γ` agree, and let `S.termDisc γ = 0`, which says that the spans of the
frame `f` and of `γ f` share a nonzero vector. Then `γ` has a cell rank `j`. That is, for one `ζ`
with `ζ ζ̄ = 1` the flags of `f` and of `γ f` share a vector with coefficients `ζ`, `1` at each
index from `j` on; the leading minor of order `j` of the matrix `S.frameProducts γ` of hermitian
products `h(f_a, γ f_b)` is nonzero; and `j ≤ ϱ`. -/
lemma CharsAgree.exists_hasCellRank (h_agree : S.CharsAgree γ) (h_disc : S.termDisc γ = 0) :
    ∃ j : Fin (𝔰.ϱ + 2), S.HasCellRank j γ := by
  -- Take the least index `j` from which a norm-one pair occurs; the condition from `ϱ + 1` on is
  -- empty, as no index reaches it.
  have h_empty : NormOnePairOccursFrom (𝔰.ϱ + 1) γ :=
    ⟨1, by simp, fun a ha ↦ absurd a.isLt ha.not_gt⟩
  obtain ⟨j, h_least⟩ : ∃ j : ℕ, IsLeast {i : ℕ | NormOnePairOccursFrom i γ} j :=
    ⟨_, Nat.isLeast_find ⟨_, h_empty⟩⟩
  -- The two frames share a nonzero vector, so `j ≤ ϱ`.
  obtain ⟨x, y, hy, hxy⟩ := termDisc_eq_zero_iff_exists.1 h_disc
  have hx : x ≠ 0 := fun h ↦ hy (frameImage_mulVec_eq_zero_iff.1 (by rw [← hxy, h, mulVec_zero]))
  obtain ⟨l, hl, -⟩ := h_agree.exists_coords_ne_zero_of_common_vector h_least hxy hx
  have hj : j ≤ 𝔰.ϱ := hl.trans l.is_le
  exact ⟨⟨j, by lia⟩, h_least.1, h_agree.leadingMinor_ne_zero h_least hj, by simp [hj, h_disc]⟩

end New.Filling

end
