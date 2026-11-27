import Lib.SiegelWeil.SingularForms.CentreCoefficients
import Lib.Weil.MixedModel.AdaptedSplitting

/-!
# Singular forms governed by unimodular coefficients

The file first computes how conjugation scales Haar measure on the hermitian `1 × 1` matrices, which
parametrise the centre of the unipotent radical of the stabiliser of an isotropic line. Its main
result, after Freitag, concerns an automorphic function `f` that is right invariant under the
integral points supported on `S ∪ S̄` and whose partial means along extra isotropic lines are
invariant under shears; `S` is a set of finite places away from the level of `f`. Suppose the
Fourier coefficient of `f` at an invertible `T` vanishes at the points that act on the frame by a
matrix `γ` on `S ∪ S̄` and by `1` elsewhere, where the normalised index `δ⁻¹ γᴴ T γ` is unimodular
on `S ∪ S̄` and `δ = ȷκκ̄`. Then this coefficient vanishes at all points that fix the frame off
`S ∪ S̄`. Lattices on `S ∪ S̄` are given by matrices `γ` whose columns span them.

## Main definitions and results

* `New.Exchange.closurePart`: the endomorphism that keeps the components on `S ∪ S̄` and replaces
  all others by 1.
* `New.Exchange.StraightPoint`, `New.Exchange.exists_straightPoint`: points whose lattice splits
  along the two isotropic lines, and the straightening of a point by singularity.
* `New.Exchange.centreCoeff_eq_zero_of_unimodular`: the vanishing theorem.

Notions from other files:
* `New.Space.Splitting`: a decomposition of a hermitian space into two dual isotropic frames k, l
  and an orthogonal complement with inclusion ι and form ε₀; `A.symm` exchanges k and l, and
  `A.comp B` has the frame (k_A, ι_A k_B).
* `New.Space.Splitting.radicalElement`: For adelic c (n₀×p, where n₀ indexes the complement) and b
  (p×p), the element of G with k ↦ k, ι ↦ ι + kc*ε₀, l ↦ l − ιc − k(½ȷ⁻¹(b + b*) + ½c*ε₀c).
* `New.Space.Splitting.lineShift`: n₊(a) = `A.lineShift B a` shifts the isotropic vector u of A to
  u − ι k_B aᴴ; n₋(b) = `A.symm.lineShift B b` shifts that of `A.symm`.
* `IsBaseAdapted`: the frames of a splitting are orthonormal at the infinite places and integral at
  the finite ones. `stdLevel E n` consists of the points that are integral at the finite places.
* `New.Space.Splitting.partialMean`, `New.Space.Splitting.shiftedMean`: f⁺(g) is the mean over b of
  the coefficient of f along D at T at n₋(b) g, and φ⁺_g(a) = f⁺(n₊(a) g); f⁻ and φ⁻ are those for
  `A.symm`.
* `New.Space.Splitting.frameStabilizer`: the points that fix a given multiple of the frame of D.
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄.

## Relation to the literature

Known result: Singular forms are governed by their coefficients at unimodular indices. Here the
setting is adelic, unitary and not holomorphic, and singularity comes from invariance under shears
at a nonempty set of places. The result here is the vanishing criterion
`centreCoeff_eq_zero_of_unimodular`, proved by choosing a point at which the denominator of the
inverse determinant of the index is least. Source: E. Freitag, Singular Modular Forms and Theta
Relations, Lecture Notes in Math. 1487, Springer 1991; see also J.-S. Li, Automorphic forms with
degenerate Fourier coefficients, Amer. J. Math. 119 (1997).

The tower property for the constant term of a theta lift along an isotropic line is in
`Lib.SiegelWeil.Tower.LargeSideConstantTerm`.
-/

noncomputable section

namespace New.Exchange

/-! ## Haar measure on the centre of the radical of an isotropic line -/

section LineRadical

open MeasureTheory Measure WeilData

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {m : Type} [Fintype m] [DecidableEq m] {t : m → ℤˣ}

instance : CompactSpace (maxCompact E t) := isCompact_iff_compactSpace.1 isCompact_maxCompact

/-- Let `μ` be a Haar measure on the hermitian `1 × 1` matrices over the adeles, and let `a` be
invertible. The push-forward of `μ` under `x ↦ a x a*` is `μ` scaled by the inverse of the idelic
absolute value of `det a`. -/
lemma map_conjugate_selfAdjoint {a : GL Unit (𝔸 E)}
    (μ : Measure (selfAdjoint (Matrix Unit Unit (𝔸 E)))) [IsAddHaarMeasure μ] :
    μ.map (β := selfAdjoint (Matrix Unit Unit (𝔸 E)))
        (fun b : selfAdjoint (Matrix Unit Unit (𝔸 E)) ↦
          ⟨a.val * b.val * star a.val, IsSelfAdjoint.conjugate b.property a.val⟩) =
      ENNReal.ofReal (ideleAbs a.det)⁻¹ • μ := by
  -- A 1×1 matrix `z` is a pair of hermitian ones, `z + z*` and `j z + (j z)*`, and `z ↦ a z a*`
  -- acts on both by the given map. It scales the measure on matrices by `|a a*|⁻¹ = |a|⁻²`, so
  -- `μ × μ` is scaled by `|a|⁻²`; on squares `s ×ˢ s` take the square root.
  have : IsAddHaarMeasure (μ.prod μ) := prod.instIsAddHaarMeasure μ μ
  let conj (b : selfAdjoint (Matrix Unit Unit (𝔸 E))) : selfAdjoint (Matrix Unit Unit (𝔸 E)) :=
    ⟨a.val * b.val * star a.val, b.property.conjugate a.val⟩
  let e : selfAdjoint (Matrix Unit Unit (𝔸 E)) × selfAdjoint (Matrix Unit Unit (𝔸 E)) ≃ₜ+
      Matrix Unit Unit (𝔸 E) :=
    { toFun := fun (p, q) ↦ toAdele (2⁻¹ : E) • (toAdele (j⁻¹ : E) • q + p)
      invFun z := (⟨z + star z, .add_star_self z⟩,
        ⟨toAdele (j : E) • z + star (toAdele (j : E) • z), .add_star_self _⟩)
      -- both inverses: expand, using `star j = -j`, and compare the scalar coefficients
      left_inv _ := by
        simp [Subtype.ext_iff, Prod.ext_iff]
        constructor <;> match_scalars <;> grind
      right_inv _ := by
        simp
        match_scalars <;> grind
      map_add' _ _ := by simp [add_add_add_comm] }
  have h_semiconj (x : selfAdjoint (Matrix Unit Unit (𝔸 E)) ×
      selfAdjoint (Matrix Unit Unit (𝔸 E))) :
      e (Prod.map conj conj x) = a.val * e x * (star a).val := by
    simp [e, conj, Matrix.mul_add, Matrix.add_mul]
  have h_prod : (μ.prod μ).map (Prod.map conj conj) =
      ENNReal.ofReal (ideleAbs ((star a).det ^ Fintype.card Unit * a.det))⁻¹ • μ.prod μ :=
    map_addHaar_eq_smul_of_semiconj _ e h_semiconj (by fun_prop)
      (volume_map_mul_mul_adele a (star a))
  refine Measure.ext fun s _ ↦ (ENNReal.pow_right_strictMono two_ne_zero).injective ?_
  calc μ.map conj s ^ 2 = (μ.prod μ).map (Prod.map conj conj) (s ×ˢ s) := by
        rw [sq, ← prod_prod, map_prod_map] <;> fun_prop
    _ = (ENNReal.ofReal (ideleAbs a.det)⁻¹ • μ) s ^ 2 := by
      simp [h_prod, sq, mul_mul_mul_comm _ (μ _)]

end LineRadical

/-!
## Singular forms and unimodular coefficients

The proof takes a point with the least value of a subgroup index that measures how far the
determinant of the normalised index is from a unit.
-/

section SingularForms

open AddSubgroup Matrix Circle RingHom NumberField WeilData G Gf Space Splitting Prod
  stdLattice

variable {E n n₁ n₂ p : Type} [Field E] [CMType E]
  [Fintype n] [DecidableEq n] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
  [Fintype p] [DecidableEq p] {s : n → ℤˣ} {s₁ : n₁ → ℤˣ}
variable {S : Set (FinPlace E)} {W : Space E n s} {W₁ : Space E n₁ s₁} {f : G E s → ℂ}
  {D : W.Splitting W₁ p}
variable {T : Matrix p p E} {s₂ : n₂ → ℤˣ} {W₀ : Space E ((p ⊕ p) ⊕ n₂) (hyperbolicSigns p ⊕ᵥ s₂)}
  {W₂ : Space E n₂ s₂} {A : W.Splitting W₀ Unit} {B : W₀.Splitting W₂ p} {U : Set (FinPlace E)}

/-- The ring of adeles that are integral at the places of S ∪ S̄. -/
def closureIntegers {E : Type} [Field E] [NumberField E] [IsCMField E] (S : Set (FinPlace E)) :
    Subring (𝔸 E) := by
  -- the set is closed under the ring operations, as one sees place by place
  use! {x | (idemAdele S.conjClosure * x).2 ∈ Ô E} <;> simp [Ô, idem_apply, ite_mem] <;> bound

/-- The endomorphism of the adelic unitary group that keeps the components on S ∪ S̄ and
replaces all others by 1. -/
def closurePart {E : Type} [Field E] [NumberField E] [IsCMField E] (S : Set (FinPlace E)) :
    G E s →* G E s :=
  MonoidHom.prodMap 1 (componentOn n S)

lemma mem_closureIntegers_iff {x : 𝔸 E} :
    x ∈ closureIntegers S ↔ (idemAdele S.conjClosure * x).2 ∈ Ô E :=
  Iff.rfl

@[simp high]
lemma idemAdele_conjClosure_mul_self :
    idemAdele S.conjClosure * idemAdele S.conjClosure = idemAdele S.conjClosure := by
  simp [idem_mul_self]

@[simp]
lemma star_idemAdele_conjClosure : star (idemAdele S.conjClosure) = idemAdele S.conjClosure := by
  aesop

/-- Taking the part on S ∪ S̄ of an adele, as a finite adele, is multiplicative. -/
lemma snd_idemAdele_conjClosure_mul_mul (x y : 𝔸 E) :
    (idemAdele S.conjClosure * (x * y)).2 =
      (idemAdele S.conjClosure * x).2 * (idemAdele S.conjClosure * y).2 := by
  rw [← snd_mul, mul_mul_mul_comm, idemAdele_conjClosure_mul_self]

instance {E : Type} [Field E] [NumberField E] [IsCMField E] {S : Set (FinPlace E)} :
    IsStarStable (closureIntegers S) :=
  ⟨fun h ↦ by simpa [closureIntegers] using star_mem_Ô h⟩

/-- The matrix of `closurePart S g` is that of `g` on S ∪ S̄ and the identity elsewhere. -/
@[simp]
lemma adeleMatrix_closurePart (g : G E s) :
    (closurePart (s := s) S g).adeleMatrix =
      idemAdele S.conjClosure • g.adeleMatrix + (1 - idemAdele S.conjClosure) • 1 := by
  -- compare entries at the infinite and at the finite places
  ext i k <;> by_cases h : i = k <;>
    simp [closurePart, componentOn, U.cutAt, cutGL, h]

variable [WeilData E]

/-- The idele ȷκκ̄, with κ = `New.WeilData.scaleIdele`; its finite part is ȷαᾱ. -/
def invDifferentIdele (E : Type) [Field E] [CMType E] [WeilData E] : (𝔸 E)ˣ :=
  Units.map (toAdele (E := E)) (Units.mk0 (j : E) j_ne_zero) * scaleIdele E * star (scaleIdele E)

lemma snd_invDifferentIdele :
    (invDifferentIdele E).val.2 = algebraMap E (𝔸f E) j * α.val * star α.val :=
  rfl

/-- Siegel's T[γ] = γᴴTγ for a matrix T over E, read in the adeles, and an adelic matrix γ, divided
by the idele δ = ȷκκ̄ (`New.Exchange.invDifferentIdele`). -/
def siegelBracket (T : Matrix p p E) (γ : Matrix p p (𝔸 E)) : Matrix p p (𝔸 E) :=
  (invDifferentIdele E)⁻¹.1 • (γᴴ * T.map toAdele * γ)

lemma star_invDifferentIdele_inv :
    star (invDifferentIdele E)⁻¹.val = -(invDifferentIdele E)⁻¹.val := by
  simp [invDifferentIdele, mul_left_comm]

/-- The part `closurePart S` on S ∪ S̄ of an element of the unipotent radical is the element whose
parameters are multiplied by the adele that is 1 on S ∪ S̄ and 0 elsewhere. -/
lemma closurePart_radicalElement (c : Matrix n₁ p (𝔸 E)) (z : Matrix p p (𝔸 E)) :
    closurePart S (D.radicalElement c z) =
      D.radicalElement (idemAdele S.conjClosure • c) (idemAdele S.conjClosure • z) := by
  apply ext_adeleMatrix
  simp only [radicalElement, adeleMatrix_closurePart, adeleMatrix_ofMatrix, conjTranspose_smul,
    star_idemAdele_conjClosure, idemAdele_conjClosure_mul_self, Matrix.mul_assoc, smul_add,
      smul_smul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.add_mul, smul_mul]
  module

/-- The part `closurePart S` on S ∪ S̄ of an element `D.radicalCentre M` (matrix
`1 + D.kAdelic * (M - Mᴴ) * D.lCoord`, so only `M - Mᴴ` matters) of the centre of the unipotent
radical is the element whose parameter is multiplied by the adele that is 1 on S ∪ S̄ and 0
elsewhere. -/
lemma closurePart_radicalCentre (M : Matrix p p (𝔸 E)) :
    closurePart S (D.radicalCentre M) = D.radicalCentre (idemAdele S.conjClosure • M) := by
  apply ext_adeleMatrix
  simp only [adeleMatrix_closurePart, adeleMatrix_radicalCentre, conjTranspose_smul,
    star_idemAdele_conjClosure,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, smul_add, Matrix.mul_smul, smul_mul]
  module

/-! ### Fourier coefficients -/

/-- On the adeles supported on S ∪ S̄, the standard character at δx is the character
`selfDualAddChar E : z ↦ ψ_f(ȷαᾱz)` of the finite adeles at x, for the idele δ = ȷκκ̄. -/
lemma stdAddChar_idemAdele_mul (x : 𝔸 E) :
    (stdAddChar E (idemAdele S.conjClosure * (invDifferentIdele E * x)) : ℂ) =
      selfDualAddChar E (idemAdele S.conjClosure * x).2 := by
  rw [selfDualAddChar_apply, ← snd_invDifferentIdele, ← snd_mul, mul_left_comm]
  simp [stdAddChar]

/-- Let `f` be an automorphic function, let `X` agree on `S ∪ S̄` with a point `g` that acts on the
isotropic frame of `D` by `c`, and let `D.radicalCentre M`, whose matrix is
`1 + D.kAdelic * (M - Mᴴ) * D.lCoord`, be an element of the centre of the unipotent radical. Right
translation of `X` by the part on `S ∪ S̄` of this element divides the Fourier coefficient at `T` by
the value of the character `selfDualAddChar E : z ↦ ψ_f(ȷαᾱz)` of the finite adeles at the part on
`S ∪ S̄` of `tr (M * siegelBracket T c)`. Here `siegelBracket T c = δ⁻¹ cᴴ T c`. -/
lemma centreCoeff_mul_radicalCentre (hf : IsAutFunction W f) {T : Matrix p p E} {X g : G E s}
    {c : Matrix p p (𝔸 E)} (hX : closurePart S X = closurePart S g) (hg : D.ActsOnFrame g c)
    (M : Matrix p p (𝔸 E)) :
    selfDualAddChar E (idemAdele S.conjClosure * (M * siegelBracket T c).trace).2 *
        D.centreCoeff T f (X * closurePart S (D.radicalCentre M)) =
      D.centreCoeff T f X := by
  -- `X` agrees with `g` on `S ∪ S̄`, so the `S ∪ S̄`-part of `D.radicalCentre M` moves across `X`.
  have h_part : closurePart S X * closurePart S (D.radicalCentre M) =
      closurePart S (D.radicalCentre (c * M * cᴴ)) * closurePart S X := by
    rw [hX, ← map_mul, D.mul_radicalCentre hg M, map_mul]
  -- Off `S ∪ S̄` both sides below are `X`; on `S ∪ S̄` they are the two sides of `h_part`.
  have h_comm : X * closurePart S (D.radicalCentre M) =
      closurePart S (D.radicalCentre (c * M * cᴴ)) * X := ext_adeleMatrix <| by
    simpa [smul_sub, Matrix.mul_add, mul_sub, Matrix.add_mul, sub_mul, smul_smul]
      using congrArg adeleMatrix h_part
  have h_char : selfDualAddChar E (idemAdele S.conjClosure * (M * siegelBracket T c).trace).2 =
      stdAddChar E (T.map toAdele * idemAdele S.conjClosure • (c * M * cᴴ)).trace := by
    rw [← stdAddChar_idemAdele_mul]
    simp [M.trace_mul_cycle', siegelBracket, Matrix.mul_assoc]
  rw [h_comm, h_char, closurePart_radicalCentre]
  exact D.centreCoeff_radicalCentre_mul hf _ X

/-! ### The index of a lattice in its dual -/

omit [WeilData E] in
/-- The denominator of a finite adele `a` (the index in `Ô` of the group of the `x` with `a x ∈ Ô`)
is smaller than that of `b`, if `a = u b` with `u ∈ Ô` and some `y ∈ Ô` has `a y ∈ Ô`, `b y ∉ Ô`. -/
lemma denomIndex_lt_of_mul_mem_of_mul_notMem {a b u y : 𝔸f E} (hu : u ∈ Ô E) (h_eq : a = u * b)
    (hy : y ∈ Ô E) (hay : a * y ∈ Ô E) (hby : b * y ∉ Ô E) :
    denomIndex (Ô E) a < denomIndex (Ô E) b := by
  let H (c : 𝔸f E) : AddSubgroup (Ô E).toAddSubgroup :=
    ((Ô E).toAddSubgroup.comap (AddMonoidHom.mulLeft c)).addSubgroupOf (Ô E).toAddSubgroup
  have mem_H (c : 𝔸f E) (x : (Ô E).toAddSubgroup) : x ∈ H c ↔ c * x.val ∈ Ô E := Iff.rfl
  -- An open subgroup of the compact group `Ô E` has finite index.
  have : (H b).FiniteIndex :=
    ⟨isCompact_Ô.relIndex_ne_zero_add (isOpen_Ô.preimage (continuous_const_mul b))⟩
  have h_le : H b ≤ H a := fun x hx ↦ by
    simpa [mem_H, h_eq, mul_assoc] using (Ô E).mul_mem hu ((mem_H b x).1 hx)
  change (H a).index < (H b).index
  exact index_strictAnti (lt_of_le_not_ge h_le fun h_ge ↦
    hby ((mem_H b ⟨y, hy⟩).1 (h_ge ((mem_H a _).2 hay))))

/-- The denominator (`denomIndex`, an index of subgroups of `Ô`) of the part on `S ∪ S̄` of the
determinant of the inverse of `siegelBracket T γ = δ⁻¹ γᴴ T γ`. If `siegelBracket T γ` is
invertible and integral on `S ∪ S̄`, this is the index there of the lattice spanned by `γ` in its
dual. -/
def dualIndex (S : Set (FinPlace E)) (T : Matrix p p E) (γ : Matrix p p (𝔸 E)) : ℕ :=
  denomIndex (Ô E) (idemAdele S.conjClosure * (siegelBracket T γ)⁻¹.det).2

/-- Let `siegelBracket T γ` (the matrix `γᴴ T γ` divided by the idele `invDifferentIdele E`) and `r`
be integral on `S ∪ S̄`, let `siegelBracket T (γ * r)` be invertible, and let the inverse of `det r`
not be integral on `S ∪ S̄`. Then passing from `γ` to `γ * r` raises `dualIndex`, the denominator of
the part on `S ∪ S̄` of `(siegelBracket T γ)⁻¹.det`. -/
lemma dualIndex_lt_dualIndex_mul_of_det_inv_notMem {T : Matrix p p E} {γ r : Matrix p p (𝔸 E)}
    (hγ : IsIntMatrix (closureIntegers S) (siegelBracket T γ))
    (hr : IsIntMatrix (closureIntegers S) r) (hunit : IsUnit (siegelBracket T (γ * r)).det)
    (hr_inv : Ring.inverse r.det ∉ closureIntegers S) :
    dualIndex S T γ < dualIndex S T (γ * r) := by
  -- With `C = siegelBracket T γ`, the element `det (rᴴ C)` clears the denominator of `det C⁻¹` but
  -- not that of `det (rᴴ C r)⁻¹`.
  have hC_mul : siegelBracket T (γ * r) = rᴴ * siegelBracket T γ * r := by
    simp [siegelBracket, Matrix.mul_assoc]
  rw [hC_mul] at hunit
  rw [dualIndex, dualIndex, hC_mul]
  generalize siegelBracket T γ = C at hγ hunit ⊢
  obtain ⟨⟨hrH_unit, hC_unit⟩, hr_unit⟩ : (IsUnit rᴴ.det ∧ IsUnit C.det) ∧ IsUnit r.det := by
    simpa only [det_mul, IsUnit.mul_iff] using hunit
  have h_inv : (rᴴ * C * r)⁻¹.det = Ring.inverse r.det * (C⁻¹.det * Ring.inverse rᴴ.det) := by
    simp [det_nonsing_inv, Ring.mul_inverse_rev]
  have h_det : C⁻¹.det = (rᴴ * r).det * (rᴴ * C * r)⁻¹.det := by
    grind [det_mul, Ring.mul_inverse_cancel]
  have h_clear : C⁻¹.det * (rᴴ * C).det = rᴴ.det := by
    grind [det_mul, det_nonsing_inv_mul_det]
  have h_not_clear : (rᴴ * C * r)⁻¹.det * (rᴴ * C).det = Ring.inverse r.det := by
    grind [Ring.mul_inverse_cancel]
  refine denomIndex_lt_of_mul_mem_of_mul_notMem
    (mem_closureIntegers_iff.1 (hr.conjTranspose.mul hr).det_mem) ?_
    (mem_closureIntegers_iff.1 (hr.conjTranspose.mul hγ).det_mem) ?_ ?_ <;>
    simp only [← snd_idemAdele_conjClosure_mul_mul, ← h_det, h_clear, h_not_clear,
      ← mem_closureIntegers_iff]
  exacts [hr.conjTranspose.det_mem, hr_inv]

/-! ### Points that agree on `S ∪ S̄` -/

/-- The point `X` agrees with `g` on `S ∪ S̄` and fixes the isotropic frame of `D` elsewhere. -/
structure AgreesOnClosure (S : Set (FinPlace E)) {W : Space E n s} {W₁ : Space E n₁ s₁}
    (D : W.Splitting W₁ p) (X g : G E s) : Prop where
  /-- `X` and `g` have the same components on `S ∪ S̄`. -/
  closurePart_eq : closurePart S X = closurePart S g
  /-- `X` fixes the frame of `D` off `S ∪ S̄`. -/
  mem_frameStabilizer : X ∈ D.frameStabilizer (1 - idemAdele S.conjClosure)

section

omit [WeilData E]

/-- The part of `g` on `S ∪ S̄` agrees with `g` on `S ∪ S̄` and fixes the frame of `D` elsewhere. -/
lemma AgreesOnClosure.closurePart_self (g : G E s) : AgreesOnClosure S D (closurePart S g) g :=
  ⟨ext_adeleMatrix (by simp [smul_smul, mul_sub]), Splitting.mem_frameStabilizer.2 <| by
    simp [Matrix.add_mul, smul_smul, sub_mul, mul_sub]⟩

/-- A point supported on `S ∪ S̄` fixes the frame of `D` off `S ∪ S̄`. -/
lemma mem_frameStabilizer_of_mem_supportedOn {g : Gf E n} (hg : g ∈ supportedOn n S) :
    ((1, g) : G E s) ∈ D.frameStabilizer (1 - idemAdele S.conjClosure) := by
  have hg_on : componentOn n S g = g :=
    eq_of_supportedOn componentOn_mem_supportedOn hg (by simp +contextual)
  simpa [closurePart, Prod.map, hg_on] using
    (AgreesOnClosure.closurePart_self (S := S) (D := D) (1, g)).mem_frameStabilizer

/-- If `X`, `Y` agree with `g`, `k` on `S ∪ S̄` and fix the frame of `D` elsewhere, then `X * Y`
does so with respect to `g * k`. -/
lemma AgreesOnClosure.mul {X Y g k : G E s} (hX : AgreesOnClosure S D X g)
    (hY : AgreesOnClosure S D Y k) : AgreesOnClosure S D (X * Y) (g * k) :=
  ⟨by rw [map_mul, map_mul, hX.closurePart_eq, hY.closurePart_eq],
    mul_mem hX.mem_frameStabilizer hY.mem_frameStabilizer⟩

end

/-- Let the frame of `D` be that of `B` inside the complement of the plane split off by `A`. If `X`
agrees with `g` on `S ∪ S̄` and fixes the frame of `D` elsewhere, then so does n₊(a) X with respect
to n₊(a) g, for the shift n₊(a) = `A.lineShift B a`. -/
lemma AgreesOnClosure.lineShift_mul (hD : D.kAdelic = A.iAdelic * B.kAdelic) {X g : G E s}
    (hX : AgreesOnClosure S D X g) (a : Matrix Unit p (𝔸 E)) :
    AgreesOnClosure S D (A.lineShift B a * X) (A.lineShift B a * g) :=
  .mul ⟨rfl, (actsOnFrame_lineShift_one hD a).mem_frameStabilizer _⟩ hX

omit [WeilData E] in
/-- If `X` agrees on `S ∪ S̄` with a point `g` that acts on the frame `k` of `D` by `γ` (that is,
`g k = k γ`), and fixes the frame elsewhere, then `X` acts on the frame by `γ` on `S ∪ S̄` and by
`1` elsewhere. -/
lemma AgreesOnClosure.actsOnFrame {X g : G E s} {γ : Matrix p p (𝔸 E)}
    (hX : AgreesOnClosure S D X g) (hg : D.ActsOnFrame g γ) :
    D.ActsOnFrame X (idemAdele S.conjClosure • γ + (1 - idemAdele S.conjClosure) • 1) := by
  have h_sum : (closurePart S X).adeleMatrix * idemAdele S.conjClosure • D.kAdelic +
      X.adeleMatrix * (1 - idemAdele S.conjClosure) • D.kAdelic =
      (closurePart S g).adeleMatrix * idemAdele S.conjClosure • D.kAdelic +
        (1 - idemAdele S.conjClosure) • D.kAdelic := by
    rw [hX.closurePart_eq, Splitting.mem_frameStabilizer.1 hX.mem_frameStabilizer]
  simpa [hg, Matrix.mul_add, Matrix.add_mul, smul_smul, mul_sub] using h_sum

/-! ### Integrality -/

/-- If `T` and `γ` are invertible, then so is `siegelBracket T γ = δ⁻¹ γᴴ T γ`. -/
lemma isUnit_det_siegelBracket {γ : Matrix p p (𝔸 E)} (hT : T.det ≠ 0) (hγ : IsUnit γ.det) :
    IsUnit (siegelBracket T γ).det := by
  simp [hγ, hT, ← mapMatrix_apply, ← map_det, IsUnit.pow, siegelBracket]

/-- For invertible `γ`, a column `x`, a row `b` and a scalar `t`, the pairing `tr (T (γ x tᴴ) b)` is
δ times the value of the form `siegelBracket T γ = δ⁻¹ γᴴ T γ` at the columns `γ⁻¹ bᴴ t` and `x`. -/
lemma invDifferentIdele_mul_siegelBracket_apply {γ : Matrix p p (𝔸 E)} (hγ : IsUnit γ.det)
    (x : Matrix p Unit (𝔸 E)) (b : Matrix Unit p (𝔸 E)) (t : Matrix Unit Unit (𝔸 E)) :
    invDifferentIdele E * ((γ⁻¹ * (bᴴ * t))ᴴ * (siegelBracket T γ * x)) () () =
      (T.map toAdele * (γ * x * tᴴ * b)).trace := by
  have h_prod : (γ⁻¹ * (bᴴ * t))ᴴ * (siegelBracket T γ * x) =
      (invDifferentIdele E)⁻¹.val • (tᴴ * b * (T.map toAdele * (γ * x))) := by
    simp [siegelBracket, Matrix.mul_assoc, ← Matrix.mul_assoc γ⁻¹ᴴ, ← conjTranspose_mul γ, hγ]
  calc _ = (tᴴ * b * (T.map toAdele * (γ * x))).trace := by rw [h_prod]; simp [trace]
    _ = _ := by rw [trace_mul_comm]; simp only [Matrix.mul_assoc]

/-- Let `f` be right invariant under the integral points supported on `S ∪ S̄`, and let `k` be
integral at the finite places. Right translation by the part of `k` on `S ∪ S̄` does not change the
Fourier coefficients of `f` along `D`. -/
lemma centreCoeff_mul_closurePart (hK : HasLevel f (stdLevel E n ⊓ supportedOn n S)) (X : G E s)
    {k : G E s} (hk : k.2 ∈ stdLevel E n) :
    D.centreCoeff T f (X * closurePart S k) = D.centreCoeff T f X := by
  simp [centreCoeff, ← mul_assoc, closurePart, Prod.map, hK, componentOn_mem_stdLevel, hk,
    componentOn_mem_supportedOn]

/-- Let `f` be automorphic and right invariant under the integral points supported on `S ∪ S̄`. Let
the splittings `A`, `B` be adapted to the integral structure, and let the frame of `D` be that of
`B` inside the complement of the plane split off by `A`. Let `X` have the same components on
`S ∪ S̄` as a point `u` that acts on the frame of `D` by `γ`. If the Fourier coefficient of `f`
along `D` at `T` is not zero at `X`, then Siegel's bracket `siegelBracket T γ = δ⁻¹ γᴴ T γ` has
entries integral at the places of `S ∪ S̄`, where δ = ȷκκ̄ is the idele `invDifferentIdele`; that
is, the lattice spanned by the columns of `γ` lies in its dual for the form δ⁻¹ T. -/
lemma isIntMatrix_siegelBracket {T : Matrix p p E} {s₂ : n₂ → ℤˣ}
    {W₀ : Space E ((p ⊕ p) ⊕ n₂) (hyperbolicSigns p ⊕ᵥ s₂)} {W₂ : Space E n₂ s₂}
    {A : W.Splitting W₀ Unit} {B : W₀.Splitting W₂ p}
    (hK : HasLevel f (stdLevel E n ⊓ supportedOn n S)) (hf : IsAutFunction W f)
    [IsBaseAdapted A] [IsBaseAdapted B] (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    {X u : G E s} {γ : Matrix p p (𝔸 E)}
    (hX : closurePart S X = closurePart S u) (hu : D.ActsOnFrame u γ)
    (h_ne : D.centreCoeff T f X ≠ 0) :
    IsIntMatrix (closureIntegers S) (siegelBracket T γ) := by
  -- Integral central elements fix the coefficient and multiply it by a character, which must
  -- therefore be trivial; `Ô E` is self-dual under `selfDualAddChar`.
  intro i j
  suffices h_trivial : ∀ a ∈ Ô E,
      selfDualAddChar E ((idemAdele S.conjClosure * siegelBracket T γ i j).2 * a) = 1 from
    (stdLattice.forall_selfDualAddChar_mul_eq_one_iff _).1 h_trivial
  intro a ha
  let O : Subring (𝔸 E) := (Ô E).comap (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E))
  let M : Matrix p p (𝔸 E) := .single j i (0, a)
  have hM : IsIntMatrix O (M - Mᴴ) := by
    refine .sub ?_ ?_ <;> simp [O, M, IsIntMatrix, single_apply, apply_ite, ha, star_mem_Ô]
  have h_mat : IsIntMatrix O (D.radicalCentre M).adeleMatrix := by
    -- the frame of `D` is the second block of the integral frame of `A.comp B`
    obtain ⟨hk, hl⟩ := isIntMatrix_kAdelic_and_lCoord (A.comp B)
    have hk_D : IsIntMatrix O D.kAdelic := fun i j ↦ by
      simpa only [comp_kAdelic, ← hD, fromCols_apply_inr] using hk i (.inr j)
    have hl_D : IsIntMatrix O D.lCoord := fun i j ↦ by
      simpa only [lCoord, comp_kAdelic, ← hD, mul_apply, conjTranspose_apply,
        fromCols_apply_inr] using hl (.inr i) j
    simpa only [adeleMatrix_radicalCentre] using IsIntMatrix.one.add ((hk_D.mul hM).mul hl_D)
  have h_centre : (D.radicalCentre M).2 ∈ stdLevel E n := mem_stdLevel.2 h_mat
  have h_char : selfDualAddChar E (idemAdele S.conjClosure * (M * siegelBracket T γ).trace).2 *
      D.centreCoeff T f (X * closurePart S (D.radicalCentre M)) = D.centreCoeff T f X :=
    centreCoeff_mul_radicalCentre hf hX hu M
  rw [centreCoeff_mul_closurePart hK X h_centre, mul_eq_right₀ h_ne] at h_char
  have h_trace : (M * siegelBracket T γ).trace = siegelBracket T γ i j * (0, a) := by
    simp [M, trace_single_mul, mul_comm]
  rw [h_trace] at h_char
  simpa [mul_assoc] using h_char

omit [WeilData E] in
/-- If a point `k` that is integral at the finite places acts by `a` on the frame of a splitting `D`
adapted to the integral structure, then `a` is integral on `S ∪ S̄`. -/
lemma isIntMatrix_closureIntegers_of_actsOnFrame [IsBaseAdapted D] {k : G E s}
    {a : Matrix p p (𝔸 E)} (hk : k.2 ∈ stdLevel E n) (ha : D.ActsOnFrame k a) :
    IsIntMatrix (closureIntegers S) a := by
  let O : Subring (𝔸 E) := (Ô E).comap (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E))
  have hk_int : IsIntMatrix O k.adeleMatrix := mem_stdLevel.1 hk
  -- Read in the integral frame of `D`, `k` is the matrix `a`.
  have ha_int : IsIntMatrix O a := by
    simpa [ha, ← Matrix.mul_assoc] using (isIntMatrix_kAdelic_and_lCoord D.symm).2.mul
      (hk_int.mul (isIntMatrix_kAdelic_and_lCoord D).1)
  intro i j
  simpa [closureIntegers] using mul_mem (idem_mem_Ô S.conjClosure) (ha_int i j)

/-! ### Iwasawa blocks -/

/-- Iwasawa decomposition for the flag of `A.comp B`: every `g` has a right translate `g * κ`, with
`κ` integral at the finite places, that acts on the frame by a block upper triangular matrix. -/
lemma exists_mem_stdLevel_actsOnFrame_fromBlocks (A : W.Splitting W₀ Unit) (B : W₀.Splitting W₂ p)
    (g : G E s) :
    ∃ (κ : G E s) (α : Matrix Unit Unit (𝔸 E)) (β : Matrix Unit p (𝔸 E)) (γ : Matrix p p (𝔸 E)),
      κ.2 ∈ stdLevel E n ∧ (A.comp B).ActsOnFrame (g * κ) (fromBlocks α β 0 γ) := by
  obtain ⟨κ, hκ, b, hb, h_frame, -⟩ := (A.comp B).iwasawa g (Sum.elim 0 1)
  -- The weight is 0 on the line of `A` and 1 on the frame of `B`, so the lower left block is zero.
  have h_zero : b.val.toBlocks₂₁ = 0 := ext fun _ _ ↦ hb zero_lt_one
  exact ⟨κ, b.val.toBlocks₁₁, b.val.toBlocks₁₂, b.val.toBlocks₂₂, hκ.2,
    by simpa only [← h_zero, fromBlocks_toBlocks] using h_frame⟩

/-- Let `g` act on the frame of `A.comp B` by a block upper triangular matrix with last block `γ`.
Up to the unipotent radical of `A`, `g` is an element `u` that acts on the frames of `A.comp B` and
`A.symm.comp B` by block diagonal matrices `t ⊕ γ` and `t' ⊕ γ` with `t'ᴴ t = 1`. -/
lemma exists_eq_radicalElement_mul_actsOnFrame {g : G E s} {α : Matrix Unit Unit (𝔸 E)}
    {β : Matrix Unit p (𝔸 E)} {γ : Matrix p p (𝔸 E)}
    (hg : (A.comp B).ActsOnFrame g (fromBlocks α β 0 γ)) :
    ∃ (c : Matrix ((p ⊕ p) ⊕ n₂) Unit (𝔸 E)) (z t t' : Matrix Unit Unit (𝔸 E)) (u : G E s),
      g = A.radicalElement c z * u ∧ (A.comp B).ActsOnFrame u (fromBlocks t 0 0 γ) ∧
      (A.symm.comp B).ActsOnFrame u (fromBlocks t' 0 0 γ) ∧ t'ᴴ * t = 1 := by
  obtain ⟨h_line, h_rest⟩ : A.ActsOnFrame g α ∧
      g.adeleMatrix * (A.iAdelic * B.kAdelic) = A.kAdelic * β + A.iAdelic * (B.kAdelic * γ) := by
    simpa [comp_kAdelic, fromCols_ext_iff, fromCols_mul_fromBlocks, Matrix.mul_assoc] using hg
  -- `A` splits `g` as a radical element times a Levi element, with `g₀` on the complement.
  obtain ⟨c, z, t, g₀, hg_eq, -, hg₀⟩ := A.exists_eq_radicalElement_mul_levi h_line
  have h_compl :
      (A.levi (t, g₀)).adeleMatrix * (A.iAdelic * B.kAdelic) = A.iAdelic * (B.kAdelic * γ) := by
    simp [Splitting.levi, hg₀, h_rest, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
  obtain ⟨h_k, h_l⟩ : A.ActsOnFrame (A.levi (t, g₀)) t.val ∧
      A.symm.ActsOnFrame (A.levi (t, g₀)) (t⁻¹).valᴴ := by
    constructor <;> simp [Splitting.levi, Matrix.mul_assoc, Matrix.add_mul]
  refine ⟨c, z, t.val, (t⁻¹).valᴴ, A.levi (t, g₀), hg_eq, ?_, ?_,
    by rw [conjTranspose_conjTranspose, t.inv_mul]⟩
  · simp [ActsOnFrame, comp_kAdelic, mul_fromCols, h_k, h_compl, fromCols_mul_fromBlocks,
      Matrix.mul_assoc]
  · simp only [ActsOnFrame, comp_kAdelic, mul_fromCols, h_l]
    simp [h_compl, fromCols_mul_fromBlocks, Matrix.mul_assoc]

/-- Let the splittings `A`, `B` be adapted to the integral structure, let `h` act on the frame of
`A.comp B` with upper right block `0` and lower blocks `x`, `γ`, and let `h * κ`, with `κ` integral
at the finite places, act by a block upper triangular matrix with last block `γ'`. If
`siegelBracket T γ'` is integral on `S ∪ S̄`, `γ` and `siegelBracket T γ` are invertible and
`γ⁻¹ * x` is not integral on `S ∪ S̄`, then `dualIndex` (the denominator on `S ∪ S̄` of the
determinant of the inverse of `siegelBracket T γ`) is smaller for `γ'` than for `γ`. -/
lemma dualIndex_lt_of_actsOnFrame [IsBaseAdapted A] [IsBaseAdapted B] {h κ : G E s}
    {τ α : Matrix Unit Unit (𝔸 E)} {x : Matrix p Unit (𝔸 E)} {β : Matrix Unit p (𝔸 E)}
    {γ γ' : Matrix p p (𝔸 E)} (hκ : κ.2 ∈ stdLevel E n)
    (hh : (A.comp B).ActsOnFrame h (fromBlocks τ 0 x γ))
    (hhκ : (A.comp B).ActsOnFrame (h * κ) (fromBlocks α β 0 γ')) (hγ : IsUnit γ.det)
    (h_unit : IsUnit (siegelBracket T γ).det)
    (h_int : IsIntMatrix (closureIntegers S) (siegelBracket T γ'))
    (h_not_int : ¬IsIntMatrix (closureIntegers S) (γ⁻¹ * x)) :
    dualIndex S T γ' < dualIndex S T γ := by
  -- Let `a` be the integral matrix of `κ⁻¹` on the frame. Then `x = γ' a₂₁` and `γ = γ' a₂₂`, so
  -- `γ⁻¹ x = a₂₂⁻¹ a₂₁`, and `det a₂₂` has no integral inverse.
  obtain ⟨a, ha⟩ : fromBlocks α β 0 γ' ∣ fromBlocks τ 0 x γ := hhκ.isUnit.dvd
  have hκa : (A.comp B).ActsOnFrame κ⁻¹ a := by
    calc κ⁻¹.adeleMatrix * (A.comp B).kAdelic
        = (h * κ)⁻¹.adeleMatrix * (h.adeleMatrix * (A.comp B).kAdelic) := by
          simp [← Matrix.mul_assoc, ← adeleMatrix_mul]
      _ = (A.comp B).kAdelic * a := by
        rw [hh, ha, ← Matrix.mul_assoc (A.comp B).kAdelic, ← hhκ]
        simp [← Matrix.mul_assoc, ← adeleMatrix_mul]
  have ha_int : IsIntMatrix (closureIntegers S) a :=
    isIntMatrix_closureIntegers_of_actsOnFrame (k := κ⁻¹) (inv_mem hκ) hκa
  have ha₂₂ : IsIntMatrix (closureIntegers S) a.toBlocks₂₂ := fun i j ↦ ha_int (.inr i) (.inr j)
  obtain ⟨rfl, rfl⟩ : x = γ' * a.toBlocks₂₁ ∧ γ = γ' * a.toBlocks₂₂ := by
    rw [← a.fromBlocks_toBlocks, fromBlocks_multiply, fromBlocks_inj] at ha
    simp_all
  have hγ' : IsUnit γ'.det := isUnit_of_mul_isUnit_left (by rwa [← det_mul])
  rw [Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hγ'] at h_not_int
  refine dualIndex_lt_dualIndex_mul_of_det_inv_notMem h_int ha₂₂ h_unit fun h_inv ↦ h_not_int ?_
  rw [inv_def]
  exact .mul (.smul h_inv ha₂₂.adjugate) fun i j ↦ ha_int (.inr i) (.inl j)

/-! ### Straight points -/

/-- A straight point for the plane split off by `A`: a point that fixes the frame of `D` off
`S ∪ S̄` and agrees on `S ∪ S̄` with a point `u` = `blockPoint` that scales the two isotropic
vectors of `A` by `t` = `lineScalar` and `t'` = `dualScalar` and acts on the image of the frame of
`B` by `γ`. If `A` and `B` are adapted to the integral structure, then on `S ∪ S̄` the lattice of
the point is the direct sum of its parts in the two isotropic lines and in their orthogonal
complement, and the columns of `γ` span its part in the span of the frame of `B`. -/
structure StraightPoint (S : Set (FinPlace E)) (A : W.Splitting W₀ Unit) (B : W₀.Splitting W₂ p)
    (D : W.Splitting W₁ p) where
  /-- The point. -/
  point : G E s
  /-- A point with the same components on `S ∪ S̄` that acts by block diagonal matrices. -/
  blockPoint : G E s
  /-- The scalar by which `u` acts on the isotropic vector of `A`. -/
  lineScalar : Matrix Unit Unit (𝔸 E)
  /-- The scalar by which `u` acts on the isotropic vector of `A.symm`. -/
  dualScalar : Matrix Unit Unit (𝔸 E)
  /-- The matrix by which `u` acts on the image of the frame of `B`. -/
  γ : Matrix p p (𝔸 E)
  /-- The point agrees with `u` on `S ∪ S̄` and fixes the frame of `D` elsewhere. -/
  agrees : AgreesOnClosure S D point blockPoint
  /-- `u` acts on the frame of `A.comp B` by `t ⊕ γ`. -/
  actsOnFrame_comp : (A.comp B).ActsOnFrame blockPoint (fromBlocks lineScalar 0 0 γ)
  /-- `u` acts on the frame of `A.symm.comp B` by `t' ⊕ γ`. -/
  actsOnFrame_symm_comp : (A.symm.comp B).ActsOnFrame blockPoint (fromBlocks dualScalar 0 0 γ)
  /-- The two scalars are dual to each other. -/
  conjTranspose_mul : dualScalarᴴ * lineScalar = 1

namespace StraightPoint

variable (P : StraightPoint S A B D)

/-- The same point, with the two isotropic lines exchanged. -/
def symm : StraightPoint S A.symm B D where
  point := P.point
  blockPoint := P.blockPoint
  lineScalar := P.dualScalar
  dualScalar := P.lineScalar
  γ := P.γ
  agrees := P.agrees
  actsOnFrame_comp := P.actsOnFrame_symm_comp
  actsOnFrame_symm_comp := P.actsOnFrame_comp
  conjTranspose_mul := by simpa using congrArg conjTranspose P.conjTranspose_mul

omit [WeilData E] in
/-- If the frame of `D` is the image of the frame of `B`, then `blockPoint` acts on it by `γ`. -/
lemma actsOnFrame (hD : D.kAdelic = A.iAdelic * B.kAdelic) : D.ActsOnFrame P.blockPoint P.γ := by
  have h_blocks : A.ActsOnFrame P.blockPoint P.lineScalar ∧ D.ActsOnFrame P.blockPoint P.γ := by
    simpa [comp_kAdelic, fromCols_ext_iff, fromCols_mul_fromBlocks, ← hD] using P.actsOnFrame_comp
  exact h_blocks.2

omit [WeilData E] in
lemma isUnit_det (hD : D.kAdelic = A.iAdelic * B.kAdelic) : IsUnit P.γ.det :=
  P.γ.isUnit_iff_isUnit_det.1 (P.actsOnFrame hD).isUnit

/-- Let the frame of `D` be that of `B` inside the complement of the plane split off by `A`. If the
function φ⁺ (`shiftedMean`) of a straight point is not zero, then the coefficient of `f` along `D`
at `T` is not zero at some point that agrees on `S ∪ S̄` with one acting on the frame of `D` by `γ`
and fixes this frame elsewhere. -/
lemma exists_centreCoeff_ne_zero (hD : D.kAdelic = A.iAdelic * B.kAdelic)
    (h_ne : A.shiftedMean B D T f P.point ≠ 0) :
    ∃ Y v : G E s, AgreesOnClosure S D Y v ∧ D.ActsOnFrame v P.γ ∧ D.centreCoeff T f Y ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a : Matrix Unit p (𝔸 E),
      A.partialMean B D T f (A.lineShift B a * P.point) ≠ 0 := Function.ne_iff.1 h_ne
  obtain ⟨b, hb⟩ := Splitting.exists_centreCoeff_ne_zero ha
  refine ⟨_, _, (P.agrees.lineShift_mul hD a).lineShift_mul (A := A.symm) hD b, ?_, hb⟩
  have h_plus : D.ActsOnFrame (A.lineShift B a) 1 := actsOnFrame_lineShift_one hD a
  have h_minus : D.ActsOnFrame (A.symm.lineShift B b) 1 :=
    actsOnFrame_lineShift_one (A := A.symm) hD b
  simpa only [Matrix.one_mul] using h_minus.mul (h_plus.mul (P.actsOnFrame hD))

/-- Let `f` be automorphic and right invariant under the integral points supported on `S ∪ S̄`, let
`A`, `B` be adapted to the integral structure, and let the frame of `D` be that of `B` inside the
complement of the plane split off by `A`. If the function φ⁺ (`shiftedMean`) of a straight point is
not zero, then `siegelBracket T γ = δ⁻¹ γᴴ T γ` is integral on `S ∪ S̄`. -/
lemma isIntMatrix_siegelBracket (hK : HasLevel f (stdLevel E n ⊓ supportedOn n S))
    (hf : IsAutFunction W f) [IsBaseAdapted A] [IsBaseAdapted B]
    (hD : D.kAdelic = A.iAdelic * B.kAdelic) (h_ne : A.shiftedMean B D T f P.point ≠ 0) :
    IsIntMatrix (closureIntegers S) (siegelBracket T P.γ) := by
  obtain ⟨Y, v, hY, hv, hY_ne⟩ := P.exists_centreCoeff_ne_zero hD h_ne
  exact Exchange.isIntMatrix_siegelBracket hK hf hD hY.closurePart_eq hv hY_ne

end StraightPoint

/-- Straightening. Let `f` be automorphic and right invariant under the integral points supported on
`S ∪ S̄`, let the frame of `D` be that of `B` inside the complement of the plane split off by `A`,
and let the partial mean f⁺ be invariant under the shears for a nonempty set `U` of finite places at
the points that fix the frame of `D` off `S ∪ S̄`. Let `X` be such a point, which agrees with `g` on
`S ∪ S̄`, and let `g * κ`, with `κ` integral at the finite places, act on the frame of `A.comp B` by
a block upper triangular matrix with last block `γ`. If f⁺ is not zero at `X`, then the function φ⁺
(`shiftedMean`) is not zero for some straight point with matrix `γ`. For adapted `A`, `B` the
columns of `γ` span the projection, along the line of `A`, of the part of the lattice of `g` in the
span of the frame of `A.comp B`. -/
lemma exists_straightPoint (hK : HasLevel f (stdLevel E n ⊓ supportedOn n S))
    (hf : IsAutFunction W f) (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hU : U.Nonempty)
    (h_shear : ∀ g ∈ D.frameStabilizer (1 - idemAdele S.conjClosure),
      A.ShearInvariant B D T f (idemAdele U) g)
    {X g κ : G E s} {α : Matrix Unit Unit (𝔸 E)} {β : Matrix Unit p (𝔸 E)} {γ : Matrix p p (𝔸 E)}
    (hX : AgreesOnClosure S D X g) (hκ : κ.2 ∈ stdLevel E n)
    (h_flag : (A.comp B).ActsOnFrame (g * κ) (fromBlocks α β 0 γ))
    (h_ne : A.partialMean B D T f X ≠ 0) :
    ∃ P : StraightPoint S A B D, P.γ = γ ∧ A.shiftedMean B D T f P.point ≠ 0 := by
  -- Write `g * κ = h * u` with `h = A.radicalElement c z` in the radical and `u` in the Levi
  -- subgroup, and move `X` by the parts of `h⁻¹` and `κ` on `S ∪ S̄`.
  obtain ⟨c, z, t, t', u, hu, hu_comp, hu_symm, ht⟩ :=
    exists_eq_radicalElement_mul_actsOnFrame h_flag
  have hXκ : AgreesOnClosure S D (X * closurePart S κ) (g * κ) := hX.mul (.closurePart_self κ)
  have hX' :
      AgreesOnClosure S D (closurePart S (A.radicalElement c z)⁻¹ * (X * closurePart S κ)) u := by
    rw [← inv_mul_eq_of_eq_mul hu]
    exact .mul (.closurePart_self _) hXκ
  refine ⟨⟨_, u, t, t', γ, hX', hu_comp, hu_symm, ht⟩, rfl, Function.ne_iff.2 ⟨0, ?_⟩⟩
  -- Singularity removes the part of `h⁻¹`, and the level of `f` that of `κ`.
  have h_radical :
      A.partialMean B D T f (closurePart S (A.radicalElement c z)⁻¹ * (X * closurePart S κ)) =
        A.partialMean B D T f (X * closurePart S κ) := by
    rw [radicalElement_inv, closurePart_radicalElement] at hX' ⊢
    exact partialMean_radicalElement_mul hD hf hU h_shear hXκ.mem_frameStabilizer
      hX'.mem_frameStabilizer
  have h_level : A.partialMean B D T f (X * closurePart S κ) = A.partialMean B D T f X := by
    simp only [partialMean, ← mul_assoc, centreCoeff_mul_closurePart hK _ hκ]
  rwa [shiftedMean_apply_zero, h_radical, h_level]

namespace StraightPoint

variable (P : StraightPoint S A B D)

/-- Supports. Let `f` be automorphic and right invariant under the integral points supported on
`S ∪ S̄`, let `A`, `B` be adapted to the integral structure, let the frame of `D` be that of `B`
inside the complement of the plane split off by `A`, let `det T ≠ 0`, and let the partial mean f⁺ be
invariant under the shears for a nonempty set `U` of finite places at the points that fix the frame
of `D` off `S ∪ S̄`. Let no straight point whose function φ⁺ (`shiftedMean`) is not zero have a
smaller `dualIndex` (the denominator on `S ∪ S̄` of `det (siegelBracket T γ)⁻¹`) than `P`. If the
function φ⁺ of `P` is not zero at `a`, then `γ⁻¹ aᴴ t`, with `t = P.lineScalar`, is integral on
`S ∪ S̄`: the vector `aᴴ t` lies in the lattice spanned by `γ`. -/
lemma isIntMatrix_of_shiftedMean_ne_zero (hK : HasLevel f (stdLevel E n ⊓ supportedOn n S))
    (hf : IsAutFunction W f) [IsBaseAdapted A] [IsBaseAdapted B]
    (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hT : T.det ≠ 0) (hU : U.Nonempty)
    (h_shear : ∀ g ∈ D.frameStabilizer (1 - idemAdele S.conjClosure),
      A.ShearInvariant B D T f (idemAdele U) g)
    (h_min : ∀ Q : StraightPoint S A B D, A.shiftedMean B D T f Q.point ≠ 0 →
      dualIndex S T P.γ ≤ dualIndex S T Q.γ)
    {a : Matrix Unit p (𝔸 E)} (ha : A.shiftedMean B D T f P.point a ≠ 0) :
    IsIntMatrix (closureIntegers S) (P.γ⁻¹ * (aᴴ * P.lineScalar)) := by
  -- Otherwise straightening the point n₊(a) P gives a larger lattice, with a smaller index.
  by_contra h_not
  have h_frame : (A.comp B).ActsOnFrame (A.lineShift B a * P.blockPoint)
      (fromBlocks P.lineScalar 0 (-(aᴴ * P.lineScalar)) P.γ) := by
    simp [← (adeleMatrix _).mul_assoc, P.actsOnFrame_comp, Matrix.mul_assoc, actsOnFrame_lineShift,
      fromBlocks_multiply]
  obtain ⟨κ, α, β, γ', hκ, h_flag⟩ :=
    exists_mem_stdLevel_actsOnFrame_fromBlocks A B (A.lineShift B a * P.blockPoint)
  obtain ⟨Q, rfl, hQ⟩ :=
    exists_straightPoint hK hf hD hU h_shear (P.agrees.lineShift_mul hD a) hκ h_flag ha
  have h_lt : dualIndex S T Q.γ < dualIndex S T P.γ :=
    dualIndex_lt_of_actsOnFrame hκ h_frame h_flag (P.isUnit_det hD)
      (isUnit_det_siegelBracket hT (P.isUnit_det hD)) (Q.isIntMatrix_siegelBracket hK hf hD hQ)
      fun h_neg ↦ h_not (by simpa using h_neg.neg)
  exact (h_min Q hQ).not_gt h_lt

/-- Periods. Let `A` split a hyperbolic plane off the hermitian space `W`, let `B` split the
complement `W₀` along an isotropic frame, and let the isotropic frame of `D` be the image in `W` of
that of `B` (`hD`). Let `f` be continuous and left invariant under the rational points of the
unitary group of `W` (`hf`), and let `det T ≠ 0`.

Let `S` be a set of finite places, `S̄` its conjugate, and `P` a straight point. On `S ∪ S̄` the
point `g = P.point` acts on the frame of `D` by `γ = P.γ` and scales the isotropic vector of
`A.symm` by `t' = P.dualScalar`; elsewhere it fixes the frame of `D`. The function
φ⁺ = `A.shiftedMean B D T f g` sends an adelic row `a` to f⁺(n₊(a) g), where n₊(a) is the shift
`A.lineShift B a` and f⁺(g) is the mean over rows `b` of the Fourier coefficient of `f` along `D`
at `T` at the point `A.symm.lineShift B b * g`. The function φ⁻ is the same for `A.symm`.

Suppose that `γ⁻¹ bᴴ t'` has entries integral on `S ∪ S̄` whenever φ⁻(b) ≠ 0 (`h_supp`), and that
`x` is a column with `siegelBracket T γ * x = δ⁻¹ γᴴ T γ x` integral on `S ∪ S̄` (`hx`), where δ is
the idele `invDifferentIdele E`. Then the row that is `(γ x t'ᴴ)ᴴ` on `S ∪ S̄` and zero elsewhere
is a period of φ⁺; `idemAdele S.conjClosure` is the adele that is 1 on `S ∪ S̄` and 0 elsewhere. -/
lemma shiftedMean_add_of_isIntMatrix {S : Set (FinPlace E)} {W : Space E n s} {W₁ : Space E n₁ s₁}
    {f : G E s → ℂ} {D : W.Splitting W₁ p} {T : Matrix p p E} {s₂ : n₂ → ℤˣ}
    {W₀ : Space E ((p ⊕ p) ⊕ n₂) (hyperbolicSigns p ⊕ᵥ s₂)} {W₂ : Space E n₂ s₂}
    {A : W.Splitting W₀ Unit} {B : W₀.Splitting W₂ p} (P : StraightPoint S A B D)
    (hf : IsAutFunction W f) (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hT : T.det ≠ 0)
    (h_supp : ∀ b : Matrix Unit p (𝔸 E), A.symm.shiftedMean B D T f P.point b ≠ 0 →
      IsIntMatrix (closureIntegers S) (P.γ⁻¹ * (bᴴ * P.dualScalar)))
    {x : Matrix p Unit (𝔸 E)} (hx : IsIntMatrix (closureIntegers S) (siegelBracket T P.γ * x))
    (y : Matrix Unit p (𝔸 E)) :
    A.shiftedMean B D T f P.point (y + idemAdele S.conjClosure • (P.γ * x * P.dualScalarᴴ)ᴴ) =
      A.shiftedMean B D T f P.point y := by
  -- Left translation by n₊(a) multiplies φ⁻ by a character that is trivial on its support. So it
  -- does not change φ⁻, nor therefore φ⁺, which it translates by `a`.
  set a : Matrix Unit p (𝔸 E) := idemAdele S.conjClosure • (P.γ * x * P.dualScalarᴴ)ᴴ with ha
  have h_char (b : Matrix Unit p (𝔸 E)) (hb : A.symm.shiftedMean B D T f P.point b ≠ 0) :
      (stdAddChar E (T.map toAdele * -(aᴴ * b)).trace : ℂ) = 1 := by
    let c : 𝔸 E := ((P.γ⁻¹ * (bᴴ * P.dualScalar))ᴴ * (siegelBracket T P.γ * x)) () ()
    have hc : -c ∈ closureIntegers S := neg_mem ((h_supp b hb).conjTranspose.mul hx () ())
    have h_trace : (T.map toAdele * -(aᴴ * b)).trace =
        idemAdele S.conjClosure * (invDifferentIdele E * -c) := by
      rw [mul_neg _ c, invDifferentIdele_mul_siegelBracket_apply (P.isUnit_det hD)]
      simp [ha]
    rw [h_trace, stdAddChar_idemAdele_mul,
      selfDualAddChar_eq_one_of_mem (mem_closureIntegers_iff.1 hc)]
  have h_minus : A.symm.shiftedMean B D T f (A.lineShift B a * P.point) =
      (1 : ℂ) • A.symm.shiftedMean B D T f P.point := by
    funext b
    rw [one_smul, shiftedMean_symm_lineShift_mul hD hf]
    rcases eq_or_ne (A.symm.shiftedMean B D T f P.point b) 0 with hb | hb
    · rw [hb, mul_zero]
    · rw [h_char b hb, one_mul]
  have h_plus : A.shiftedMean B D T f (A.lineShift B a * P.point) =
      (1 : ℂ) • A.shiftedMean B D T f P.point :=
    shiftedMean_symm_eq_smul (A := A.symm) hD hf hT h_minus
  calc A.shiftedMean B D T f P.point (y + a)
      = A.shiftedMean B D T f (A.lineShift B a * P.point) y :=
        (shiftedMean_lineShift_mul a y P.point).symm
    _ = A.shiftedMean B D T f P.point y := by rw [h_plus, one_smul]

/-- Let `f` be automorphic, let the frame of `D` be that of `B` inside the complement of the plane
split off by `A`, and let `det T ≠ 0`. Let the function φ⁺ (`shiftedMean`) of the straight point `P`
be nonzero. Suppose that `γ⁻¹ aᴴ t`, with `t = P.lineScalar`, is integral on `S ∪ S̄` at each `a` in
the support of φ⁺, and `γ⁻¹ bᴴ t'`, with `t' = P.dualScalar`, at each `b` in the support of φ⁻. Then
the inverse of `siegelBracket T γ = δ⁻¹ γᴴ T γ` is integral on `S ∪ S̄`: the lattice spanned by `γ`
contains its dual. -/
lemma isIntMatrix_inv_siegelBracket (hf : IsAutFunction W f)
    (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hT : T.det ≠ 0)
    (h_ne : A.shiftedMean B D T f P.point ≠ 0)
    (h_plus : ∀ a : Matrix Unit p (𝔸 E), A.shiftedMean B D T f P.point a ≠ 0 →
      IsIntMatrix (closureIntegers S) (P.γ⁻¹ * (aᴴ * P.lineScalar)))
    (h_minus : ∀ b : Matrix Unit p (𝔸 E), A.symm.shiftedMean B D T f P.point b ≠ 0 →
      IsIntMatrix (closureIntegers S) (P.γ⁻¹ * (bᴴ * P.dualScalar))) :
    IsIntMatrix (closureIntegers S) (siegelBracket T P.γ)⁻¹ := by
  -- A column `x` of the inverse gives a period `a` of φ⁺, the difference of two points of the
  -- support.
  intro i j
  let x : Matrix p Unit (𝔸 E) := replicateCol Unit fun k ↦ (siegelBracket T P.γ)⁻¹ k j
  let a : Matrix Unit p (𝔸 E) := idemAdele S.conjClosure • (P.γ * x * P.dualScalarᴴ)ᴴ
  have hx : IsIntMatrix (closureIntegers S) (siegelBracket T P.γ * x) := fun k _ ↦ by
    change (siegelBracket T P.γ * (siegelBracket T P.γ)⁻¹) k j ∈ closureIntegers S
    rw [mul_nonsing_inv _ (isUnit_det_siegelBracket hT (P.isUnit_det hD))]
    exact IsIntMatrix.one k j
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h_ne
  have hy_add : A.shiftedMean B D T f P.point (y + a) ≠ 0 :=
    (P.shiftedMean_add_of_isIntMatrix hf hD hT h_minus hx y).trans_ne hy
  have h_diff : P.γ⁻¹ * ((y + a)ᴴ * P.lineScalar) - P.γ⁻¹ * (yᴴ * P.lineScalar) = idemAdele
    S.conjClosure • x := by
    simp [a, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, P.conjTranspose_mul,
      P.isUnit_det hD]
  have h_part := (h_plus _ hy_add).sub (h_plus y hy)
  rw [h_diff] at h_part
  simpa [x, mem_closureIntegers_iff, ← mul_assoc] using h_part i ()

end StraightPoint

/-- After Freitag: a singular form is governed by its unimodular coefficients.

Let `f` be an automorphic function that is right invariant under the integral points supported on
`S ∪ S̄` (`hK`, `hf`), and let the splittings `A`, `B` be adapted to the integral structure. Let the
frame of `D` be that of `B` inside the complement of the plane split off by `A` (`hD`), let
`det T ≠ 0`, and let `U` be a nonempty set of finite places. Suppose that the partial means f⁺ and
f⁻ are invariant under the shears for `U` (`ShearInvariant … (idemAdele U)`; in the proof this lets
f⁺ drop a left factor `A.radicalElement c z` taken on `S ∪ S̄`) at the points that fix the frame of
`D` off `S ∪ S̄` (`h_shear`, `h_shear_symm`). Suppose that the Fourier coefficient of `f` along `D`
at `T` vanishes at the points that act on the frame by `γ` on `S ∪ S̄` and trivially elsewhere,
whenever `siegelBracket T γ = δ⁻¹ γᴴ T γ` and a left inverse of it are integral on `S ∪ S̄`
(`h_unimodular`). Then the coefficient vanishes at all points that fix the frame of `D` off
`S ∪ S̄`. -/
theorem centreCoeff_eq_zero_of_unimodular (hK : HasLevel f (stdLevel E n ⊓ supportedOn n S))
    (hf : IsAutFunction W f)
    {T : Matrix p p E} {s₂ : n₂ → ℤˣ} {W₀ : Space E ((p ⊕ p) ⊕ n₂) (hyperbolicSigns p ⊕ᵥ s₂)}
    {W₂ : Space E n₂ s₂} {U : Set (FinPlace E)}
    (A : W.Splitting W₀ Unit) (B : W₀.Splitting W₂ p) [IsBaseAdapted A] [IsBaseAdapted B]
    (hD : D.kAdelic = A.iAdelic * B.kAdelic) (hT : T.det ≠ 0) (hU_ne : U.Nonempty)
    (h_shear : ∀ g ∈ D.frameStabilizer (1 - idemAdele S.conjClosure),
      A.ShearInvariant B D T f (idemAdele U) g)
    (h_shear_symm : ∀ g ∈ D.frameStabilizer (1 - idemAdele S.conjClosure),
      A.symm.ShearInvariant B D T f (idemAdele U) g)
    (h_unimodular : ∀ (X : G E s) (γ : Matrix p p (𝔸 E)),
      D.ActsOnFrame X (idemAdele S.conjClosure • γ + (1 - idemAdele S.conjClosure) • 1) →
      IsPrimitiveMatrix (closureIntegers S) (siegelBracket T γ) → D.centreCoeff T f X = 0)
    {g : G E s} (hg : g ∈ D.frameStabilizer (1 - idemAdele S.conjClosure)) :
    D.centreCoeff T f g = 0 := by
  -- Otherwise some straight point has φ⁺ ≠ 0. For one with the least index, φ⁺ and φ⁻ are supported
  -- on its lattice up to the scales `P.lineScalar`, `P.dualScalar`. The lattice is then self-dual,
  -- and `h_unimodular` makes φ⁺ zero.
  by_contra hg_ne
  have h_exists : {P : StraightPoint S A B D | A.shiftedMean B D T f P.point ≠ 0}.Nonempty := by
    -- φ⁺ determines the coefficient at `g`, so it is not zero; straighten a shift of `g`
    obtain ⟨a, ha⟩ := Function.ne_iff.1 <|
      mt (centreCoeff_eq_zero_of_shiftedMean_eq_zero hD hf hT) hg_ne
    obtain ⟨κ, α, β, γ, hκ, h_flag⟩ :=
      exists_mem_stdLevel_actsOnFrame_fromBlocks A B (A.lineShift B a * g)
    obtain ⟨P, -, hP⟩ := exists_straightPoint hK hf hD hU_ne h_shear
      (AgreesOnClosure.lineShift_mul hD ⟨rfl, hg⟩ a) hκ h_flag ha
    exact ⟨P, hP⟩
  obtain ⟨P, hP, h_least⟩ :=
    (measure fun P : StraightPoint S A B D ↦ dualIndex S T P.γ).wf.has_min _ h_exists
  have h_min (Q : StraightPoint S A B D) (hQ : A.shiftedMean B D T f Q.point ≠ 0) :
      dualIndex S T P.γ ≤ dualIndex S T Q.γ := not_lt.1 (h_least Q hQ)
  have h_min_symm (Q : StraightPoint S A.symm B D) (hQ : A.symm.shiftedMean B D T f Q.point ≠ 0) :
      dualIndex S T P.γ ≤ dualIndex S T Q.γ :=
    h_min Q.symm (mt (shiftedMean_symm_eq_zero hD hf hT) hQ)
  have h_plus (a : Matrix Unit p (𝔸 E)) (ha : A.shiftedMean B D T f P.point a ≠ 0) :
      IsIntMatrix (closureIntegers S) (P.γ⁻¹ * (aᴴ * P.lineScalar)) :=
    P.isIntMatrix_of_shiftedMean_ne_zero hK hf hD hT hU_ne h_shear h_min ha
  have h_minus (b : Matrix Unit p (𝔸 E)) (hb : A.symm.shiftedMean B D T f P.point b ≠ 0) :
      IsIntMatrix (closureIntegers S) (P.γ⁻¹ * (bᴴ * P.dualScalar)) :=
    P.symm.isIntMatrix_of_shiftedMean_ne_zero hK hf hD hT hU_ne h_shear_symm h_min_symm hb
  have h_prim : IsPrimitiveMatrix (closureIntegers S) (siegelBracket T P.γ) :=
    ⟨P.isIntMatrix_siegelBracket hK hf hD hP, _,
      P.isIntMatrix_inv_siegelBracket hf hD hT hP h_plus h_minus,
      nonsing_inv_mul _ (isUnit_det_siegelBracket hT (P.isUnit_det hD))⟩
  obtain ⟨Y, v, hY, hv, hY_ne⟩ := P.exists_centreCoeff_ne_zero hD hP
  exact hY_ne (h_unimodular Y P.γ (hY.actsOnFrame hv) h_prim)

end SingularForms

end New.Exchange

end
