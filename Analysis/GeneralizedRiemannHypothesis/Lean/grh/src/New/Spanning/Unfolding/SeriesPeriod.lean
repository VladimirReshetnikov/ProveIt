import Lib.Adelic.QuotientMeasure.MovingTheQuotient
import Lib.Weil.Periods.RealAndFinitePoints
import New.Spanning.Unfolding.BesselFormula
import New.Spanning.Unfolding.FillingAdmissible
import New.UpperBound.Objects.PoincareMap

/-!
# The Poincaré map as a Poincaré series of the Bessel function

There are a real point `g₀` and a linear form `t` for which the form `D.poincareAt g₀ t φ`, which
represents the Bessel period of `φ`, is the Poincaré series of the Bessel function; the map
`D.poincare` is defined by such a choice. Pair the series with a form `y` of the conjugate type.
Unfolding gives a sum over the classes `c` of integrals over `U_c \ G(F_∞)`. Insert the integral
formula of the Bessel function, an integral over `R(F_∞)`, and move the quotient by `U_c` to that
variable; the conjugate kernel reproduces `y`, and the sum
`∑_c ∫_{U_c \ R(F_∞)} 𝒲 (s, h_c) y (s g₀, h_c) ds` remains. The period is a multiple of the same
sum, because `[R] / J'` is the disjoint union of the `U_c \ R(F_∞)`.

Notions from other files:
* `S.Fits V l kw Y η`: the space `V` with the grading `Y` and the central element `η` fits the
  filling data `S`; it identifies the adelic group of `V` with that of `S`.
* `h.poincareSeries φ`: the series `g ↦ ∑_a φ_a ∑_{γ ∈ G(F)} h.cutBessel a (γ g)`, where `a` runs
  over the pairs `(c, i)` of a class and a coordinate, and `h.cutBessel (c, i)` is `β_c` times the
  `i`-th coordinate of the Bessel function on `G(F_∞) × h_c J` and zero elsewhere.
* `Y.besselGroup`, `Y.unipotent`, `Y.inclX`: the group `R(𝔸)`, its unipotent radical and the
  inclusion of `H(𝔸)`, the unitary group of the form on the part `𝔰.κ` of the basis;
  `Y.ratBessel` is `R(F)`, `Y.besselReal` is `R(F_∞)`, `Y.besselFin` is `R(𝔸_fin)`, and
  `Y.besselMeasure` computes integrals over `[R] = R(F) \ R(𝔸)`.
* `J = S.stdPrincipalLevel` is the principal level, and `J' = R(𝔸_fin) ∩ J`.
* `h_c = h.classPoint c`, `U_c = S.classUnipotent c`, `β_c = S.classCutoff c`: the image in
  `R(𝔸_fin)` of `c.out * η⁻¹`, with `c.out` the representative of the class `c`; the group of
  rational unipotents `u` with `h_c⁻¹ u h_c ∈ J`; and a weight at the infinite places whose
  translates under `U_c` add up to one. An integral over a quotient by `U_c` is written as an
  integral against `β_c`.
* `h.besselChar`: the character of `R(𝔸)` given by the entries at the simple roots. The hypothesis
  `hj_genericConst` is `ȷ Y.genericConst = -(M ϖ)⁻¹`, with `ȷ = WeilData.j`, `M = S.M`,
  `ϖ = S.deltaE` and `Y.genericConst` the constant of `ψ_U = Y.unipotentChar`; it makes
  `h.besselChar` equal to `ψ_U` on `U(𝔸)`.
* `Y.sourceFn t φ`: the function `𝒲 (u a) = ψ_U (u) t (ǎ_∞⁻¹ φ (a_fin))` on `R(𝔸)`, where `ǎ_∞`
  is the action `conjWeylRep` of the real component `a_∞` of `a`.

## Relation to the literature

Unfolding a Poincaré series against an automorphic form is standard.
-/

noncomputable section

section Fits

open Matrix Fintype Subgroup AddChar Function Fin

namespace New.Filling.Fits

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}
  {ε : 𝔰.BesselIndex → ℤˣ} {l : NumberField.InfinitePlace E → HCParam ε}
  {kw : NumberField.InfinitePlace E → ℕ → ℕ} {V : Space E 𝔰.BesselIndex ε}
  {Y : Grading V S.N 𝔰.κ (2 * 𝔰.ϱ + 1)} {η : Gf E 𝔰.κ} [DiscreteSeries.UnitarySignFrame 𝔰 ε]

/-! ### Rational points and the character of `R(𝔸)` -/

/-- If `V` fits `S` (`h`) and `u` is a rational point lying in the Bessel unipotent group `besselU`,
then its image `h.ratEquiv u` lies in the unipotent group `Y.unipotent` of `Y`. -/
lemma ratEquiv_mem_unipotent (h : S.Fits V l kw Y η) {u : S.G E} (hu : u ∈ besselU) :
    (h.ratEquiv u : New.G E ε) ∈ Y.unipotent := by
  rw [h.mem_unipotent_iff_mem_besselU, h.adelicEquiv_ratEquiv]
  exact hu.map_mem_agreeWithOneOn toAdele

/-- If `V` fits `S` (`h`) and `σ` is a rational point of the unitary group of `S` whose image
`h.ratEquiv σ` lies in the Bessel group `Y.besselGroup`, then `σ` lies in the Bessel subgroup
`besselS`. -/
lemma mem_besselS_of_ratEquiv_mem_besselGroup (h : S.Fits V l kw Y η) {σ : S.G E}
    (hσ : (h.ratEquiv σ : New.G E ε) ∈ Y.besselGroup) : σ ∈ besselS := by
  rw [h.mem_besselGroup_iff_mem_besselS, h.adelicEquiv_ratEquiv] at hσ
  -- The equations that define `besselS` descend from the adeles to `E`.
  intro a b hab
  have h_entry : toAdele ((σ : GL 𝔰.BesselIndex E) a b) =
      (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸 E)) a b := hσ a b hab
  exact toAdele.injective (by simpa [Matrix.one_apply] using h_entry)

/-- The character `h.besselChar` is multiplicative on the Bessel group `R(𝔸)`. -/
lemma besselChar_mul (h : S.Fits V l kw Y η) {r r' : New.G E ε}
    (hr : r ∈ Y.besselGroup) (hr' : r' ∈ Y.besselGroup) :
    h.besselChar (r * r') = h.besselChar r * h.besselChar r' := by
  rw [h.mem_besselGroup_iff_mem_besselS] at hr hr'
  simp only [besselChar, map_mul h.adelicEquiv, simpleRootSum_mul hr hr', mul_add, map_add_eq_mul,
    Circle.coe_mul]

/-- The identification `h.adelicEquiv` of the adelic groups of `V` and `S` carries the inclusion
`Y.inclX` of `H(𝔸)` to the standard inclusion `toBesselH`. -/
lemma adelicEquiv_inclX (h : S.Fits V l kw Y η) (a : New.G E (1 : 𝔰.κ → ℤˣ)) :
    h.adelicEquiv (Y.inclX a) =
      toBesselH 𝔰 (S.N : 𝔸 E) ⟨(G.toUnitary a).1, by simpa using (G.toUnitary a).2⟩ := by
  -- Both sides act on the block of `a` and fix the other basis vectors; compare the entries.
  have h_mat : (h.adelicEquiv (Y.inclX a)).val.val =
      gradedBlocks Y.indexEquiv Y.indexEquiv a.adeleMatrix 1 := Y.ratCoordMatrix_inclX a
  have h_block (i j : 𝔰.κ) : a.adeleMatrix i j = (G.toUnitary a).1.1 i j := rfl
  refine Subtype.ext (Units.ext (Matrix.ext fun i j ↦ ?_))
  rw [h_mat]
  -- What is left after `simp` compares positions in the string.
  obtain i | (i | i) | i := i <;> obtain j | (j | j) | j := j <;>
    simp [h.index_eq, Shape.besselIndexEquiv, toBesselH, Matrix.one_apply, Fin.ext_iff, h_block] <;>
    lia

/-- The character `h.besselChar` of `R(𝔸)` is trivial on the image under `Y.inclX` of the adelic
unitary group `H(𝔸)` of the standard definite space on `κ`: `h.besselChar (Y.inclX a) = 1`. -/
lemma besselChar_inclX (h : S.Fits V l kw Y η) (a : New.G E (1 : 𝔰.κ → ℤˣ)) :
    h.besselChar (Y.inclX a) = 1 := by
  rw [besselChar, h.adelicEquiv_inclX, simpleRootSum_eq_zero_of_mem_besselH (toBesselH_mem _),
    mul_zero, map_zero_eq_one, Circle.coe_one]

/-- For `r` in the Bessel group `Y.besselGroup` and any adelic point `a` of the unitary group of the
standard definite space, `h.besselChar` takes the same value at `r * (Y.inclX a)⁻¹` as at `r`. -/
lemma besselChar_mul_inv_inclX (h : S.Fits V l kw Y η) {r : New.G E ε}
    (hr : r ∈ Y.besselGroup) (a : New.G E (1 : 𝔰.κ → ℤˣ)) :
    h.besselChar (r * (Y.inclX a)⁻¹) = h.besselChar r := by
  rw [← map_inv, h.besselChar_mul hr (Y.inclX_mem_besselGroup _), besselChar_inclX, mul_one]

/-- Suppose the space `V` with the grading `Y` fits the filling data `S`; in particular `Y` labels
the basis of `V` in the standard way. Then the shift `𝔢 = Y.shift` of the grading is `c C`, where
`c = Y.genericConst` and `C` is `besselCharMatrix` at the middle block `S.ratMiddle` of the form of
`S`. -/
lemma shift_eq_smul_besselCharMatrix (h : S.Fits V l kw Y η) :
    Y.shift = toAdele (Y.genericConst : E) • besselCharMatrix (S.ratMiddle (𝔸 E)) := by
  rcases 𝔰 with ⟨_ | ϱ⟩
  · -- For `ϱ = 0` the string has one vector, and both matrices vanish.
    simp [Grading.shift, besselCharMatrix, ← ext_iff, h.index_eq, Shape.besselIndexEquiv]
  · -- Compare the entries block by block. What remains says for which positions in the string an
    -- entry is nonzero, which is linear arithmetic.
    simp [Grading.shift, besselCharMatrix, ← ext_iff, h.index_eq, Shape.besselIndexEquiv, splitGram,
      middleGram, besselFrame, forall_fin_succ', ← castSucc_succ, Finset.sum_add_distrib,
      Nat.Prime.ne_zero, Matrix.one_apply]
    -- Without the context, `grind` is much faster.
    clear * -
    grind (splits := 20) [map_natCast]

/-- Suppose `V` with the grading `Y` fits the filling data `S`, and let `h.besselChar r` be the
standard additive character of `E` at `-(M ϖ)⁻¹ σ`. Here `M = S.M`, `ϖ = S.deltaE`, and `σ` is the
sum `simpleRootSum` of the entries of `r` at the simple roots, read in the adelic group of `S`. Let
`c = Y.genericConst` be the constant of the generic character `ψ_U = Y.unipotentChar`, and assume
`ȷ c = -(M ϖ)⁻¹`, with `ȷ = WeilData.j`. Then `h.besselChar u = ψ_U u` for every `u` in
`Y.unipotent`, the unipotent radical of the Bessel group. -/
lemma besselChar_eq_unipotentChar [WeilData E] (h : S.Fits V l kw Y η)
    (hj_genericConst : WeilData.j * Y.genericConst = -(S.M * S.deltaE : E)⁻¹) {u : New.G E ε}
    (hu : u ∈ Y.unipotent) :
    h.besselChar u = Y.unipotentChar u := by
  -- With `σ` the sum of the entries at the simple roots, the trace is `c * (σ - star σ)`, and
  -- the standard character at `x` depends only on `(x + star x) / 2`. Take `x = j * c * σ` and use
  -- `star j = -j`, `star c = c`.
  let σ : 𝔸 E := simpleRootSum (h.adelicEquiv u)
  have h_trace : (Y.shift * V.ratCoordMatrix u).trace = toAdele (Y.genericConst : E) *
    (σ - star σ) := by
    have h_mat : V.ratCoordMatrix u = (h.adelicEquiv u).val.val := rfl
    rw [h.shift_eq_smul_besselCharMatrix, smul_mul_assoc, trace_smul, h_mat,
      trace_besselCharMatrix_mul, simpleRootSum_inv _ (h.mem_besselGroup_iff_mem_besselS.mp
        (Y.unipotent_le_besselGroup hu)), star_neg, ← sub_eq_add_neg, smul_eq_mul]
  have h_half : toAdele (WeilData.j / 2 : E) * (toAdele (Y.genericConst : E) * (σ - star σ)) =
    toAdele 2⁻¹ *
      (toAdele (WeilData.j * Y.genericConst : E) * σ + star
        (toAdele (WeilData.j * Y.genericConst : E) * σ)) := by
    simp [Y.genericConst.2, div_eq_inv_mul, sub_eq_add_neg, mul_add, mul_assoc]
  rw [besselChar, Grading.unipotentChar, h_trace, h_half, stdAddChar_inv_two_mul_add_star,
    hj_genericConst]

/-- Let `ȷ c = -(M ϖ)⁻¹`, with `ȷ = WeilData.j`, `c = Y.genericConst`, `M = S.M` and
`ϖ = S.deltaE`, so that `h.besselChar` extends the generic character `ψ_U`. Then `sourceFn t φ` at
`r ∈ R(𝔸)` is `h.besselChar r` times the coefficient `algFormCoeff 1 t φ` at the `H`-part
`Y.leviPart r` of `r`. -/
lemma sourceFn_eq_besselChar_mul [WeilData E] (h : S.Fits V l kw Y η)
    (hj_genericConst : WeilData.j * Y.genericConst = -(S.M * S.deltaE : E)⁻¹)
    (t : (WeylIndex 𝔰.κ kw → ℂ) →ₗ[ℂ] ℂ) (φ : AlgForm (E := E) 𝔰.κ kw 0) (r : Y.besselGroup) :
    Y.sourceFn t φ r = h.besselChar r * algFormCoeff 1 t φ (Y.leviPart r) := by
  rw [Grading.sourceFn,
    ← h.besselChar_eq_unipotentChar hj_genericConst (Y.mul_inv_inclX_leviPart_mem r),
    h.besselChar_mul_inv_inclX r.2]

open MeasureTheory Measure ComplexConjugate

/-! ### The points `h_c` and the groups `U_c` -/

/-- The point `h_c` is the image under `H → R` of the representative of `c` times `η⁻¹`. -/
lemma classPoint_eq_inclXFin (h : S.Fits V l kw Y η) (c : S.Classes) :
    h.classPoint c = Y.inclXFin (c.out * η⁻¹) := by
  rw [classPoint, MulEquiv.symm_apply_eq, finiteEquiv_inclXFin, ← (h.central c.out).inv_left.eq,
    map_mul, map_inv]

/-- The point `h.classPoint c` that represents the class `c` lies in `Y.besselFin`, the finite
points `g` such that `(1, g)` lies in the Bessel group `Y.besselGroup`. -/
lemma classPoint_mem_besselFin (h : S.Fits V l kw Y η) (c : S.Classes) :
    h.classPoint c ∈ Y.besselFin := by
  rw [classPoint_eq_inclXFin]
  exact Y.snd_mem_besselFin (Y.inclX_mem_besselGroup (1, c.out * η⁻¹))

/-- A finite point `t` lies in the coset `h.classPoint c * S.stdPrincipalLevel` if and only if
`S.inclHFin η * h.finiteEquiv t`, in the lattice basis of `S`, lies in
`S.classRep c * S.principalLevel`. -/
lemma inv_classPoint_mul_mem_iff (h : S.Fits V l kw Y η) (c : S.Classes) (t : Gf E 𝔰.BesselIndex) :
    (h.classPoint c)⁻¹ * t ∈ S.stdPrincipalLevel ↔
      (S.classRep c)⁻¹ * (S.inclHFin η * h.finiteEquiv t) ∈ S.principalLevel := by
  simp [h.mem_stdPrincipalLevel_iff, classPoint, mul_assoc]

/-- For `u` in `S.classUnipotent c`, its image `h.ratEquiv u` in the discrete subgroup of `V` lies
in the Bessel group `Y.besselGroup`. -/
lemma ratEquiv_classUnipotent_mem_besselGroup (h : S.Fits V l kw Y η) {c : S.Classes}
    (u : S.classUnipotent c) : (h.ratEquiv u : New.G E ε) ∈ Y.besselGroup :=
  Y.unipotent_le_besselGroup (h.ratEquiv_mem_unipotent (mem_inf.mp u.2).1)

/-- The point `(s, h_c)` of `R(𝔸)`, for a class `c` and a real point `s` of `R`. -/
def classSection (h : S.Fits V l kw Y η) (c : S.Classes) (s : Y.besselReal) : Y.besselGroup :=
  Y.besselProdEquiv (s, ⟨h.classPoint c, h.classPoint_mem_besselFin c⟩)

/-- The homomorphism `u ↦ u_∞` from `U_c = S.classUnipotent c` to `R(F_∞)`. -/
def classUnipotentToReal (h : S.Fits V l kw Y η) (c : S.Classes) :
    S.classUnipotent c →* Y.besselReal where
  toFun u := ⟨(h.ratEquiv u : New.G E ε).1, Y.fst_mem_besselReal
    ⟨h.ratEquiv u, Y.unipotent_le_besselGroup (h.ratEquiv_mem_unipotent (mem_inf.mp u.2).1)⟩⟩
  map_one' := by simp
  map_mul' := by simp

/-- Suppose `V` fits the admissible filling data `S`, and let `c` be a class. Then
`∑_{u ∈ U_c} β_c (u_∞ x) = 1` for every `x ∈ G(F_∞)`. -/
lemma tsum_classCutoff_realHomeomorph [WeilData E]
    (h : S.Fits V l kw Y η) [S.IsAdmissible] (c : S.Classes) (x : GInf E ε) :
    ∑' u : S.classUnipotent c,
      S.classCutoff c (h.realHomeomorph (h.classUnipotentToReal c u * x)) = 1 := by
  have h_inf (u : S.classUnipotent c) :
      h.realHomeomorph (h.classUnipotentToReal c u * x) = S.ratToInf u * h.realHomeomorph x := by
    rw [ratToInf, MonoidHom.comp_apply, ← h.adelicEquiv_ratEquiv]
    exact h.realHomeomorph_mul (h.ratEquiv u) (x, 1)
  simp only [h_inf, tsum_classCutoff_eq_one]

/-- An element `u` of `U_c` moves `(x, h_c)` to `(u_∞ x, h_c)` up to a right factor in the principal
level, namely `h_c⁻¹ u_fin h_c`. -/
lemma exists_ratEquiv_mul_classPoint (h : S.Fits V l kw Y η) {c : S.Classes}
    (u : S.classUnipotent c) :
    ∃ k : Y.besselFin, (k : Gf E 𝔰.BesselIndex) ∈ S.stdPrincipalLevel ∧ ∀ x : GInf E ε,
      (h.ratEquiv u : New.G E ε) * (x, h.classPoint c) =
        (h.classUnipotentToReal c u * x, h.classPoint c) * (1, (k : Gf E 𝔰.BesselIndex)) := by
  obtain ⟨-, hu_level⟩ := mem_inf.mp u.2
  have hu : (h.ratEquiv u : New.G E ε).2 ∈ Y.besselFin :=
    Y.snd_mem_besselFin (h.ratEquiv_classUnipotent_mem_besselGroup u)
  have hc : h.classPoint c ∈ Y.besselFin := h.classPoint_mem_besselFin c
  refine ⟨⟨(h.classPoint c)⁻¹ * ((h.ratEquiv u : New.G E ε).2 * h.classPoint c),
    mul_mem (inv_mem hc) (mul_mem hu hc)⟩, ?_, fun x ↦ by simp [classUnipotentToReal, Prod.mul_def]⟩
  rw [inv_classPoint_mul_mem_iff, map_mul, finiteEquiv_eq_conj_adelicToFin, adelicEquiv_ratEquiv]
  simpa [classPoint, ratToFin, mul_assoc] using hu_level

/-! ### The Bessel function as an integral over `R(F_∞)` -/

/-- Suppose `V` fits `S` and `ȷ Y.genericConst = -(M ϖ)⁻¹`, with `ȷ = WeilData.j`, `M = S.M` and
`ϖ = S.deltaE`, so that `h.besselChar` extends `ψ_U`. Let `ψ` be an algebraic form on `H`, let `t`
be any linear form on its space of values, and let `𝒲` be `sourceFn t` of the translate of `ψ` by
`η`. Let `s = u a` be a real point of `R = U ⋊ H`, so that `a_∞ = (Y.leviPart (s, 1)).1` is the real
component of its `H`-part, and let `h.classSection c s = (s, h_c)`. Then
`𝒲 (s, h_c) = ψ_U (u) t (ǎ_∞⁻¹ ψ (c.out))`, where `ǎ_∞` is the action of `a_∞` by `conjWeylRep` and
`ψ_U (u)` is written `h.besselChar (s, 1)`. -/
lemma sourceFn_classSection [WeilData E] (h : S.Fits V l kw Y η)
    (hj_genericConst : WeilData.j * Y.genericConst = -(S.M * S.deltaE : E)⁻¹)
    (t : (WeylIndex 𝔰.κ kw → ℂ) →ₗ[ℂ] ℂ) (ψ : AlgForm (E := E) 𝔰.κ kw 0) (c : S.Classes)
    (s : Y.besselReal) :
    Y.sourceFn t (algFormRep kw 0 η ψ) (h.classSection c s) =
      h.besselChar (s.1, 1) *
        t (conjWeylRep kw 0 (Y.leviPart ⟨(s.1, 1), s.2⟩).1⁻¹ (ψ.val c.out)) := by
  have h_split : h.classSection c s =
      ⟨(s.1, 1), s.2⟩ * ⟨Y.inclX (1, c.out * η⁻¹), Y.inclX_mem_besselGroup _⟩ := Subtype.ext <| by
    simp [classSection, Grading.besselProdEquiv, classPoint_eq_inclXFin, Y.inclX_inr]
  have h_levi : (Y.leviPart ⟨(s.1, 1), s.2⟩).2 = 1 := Y.leviPart_snd_eq_one rfl
  rw [h_split, Y.sourceFn_mul_inclX, h.sourceFn_eq_besselChar_mul hj_genericConst,
    algFormCoeff_apply, h_levi]
  simp

/-- **The integral formula of the Bessel function, paired with the value of a form on `H`.** Suppose
`V` fits `S` and `ȷ Y.genericConst = -(M ϖ)⁻¹`, with `ȷ = WeilData.j`, `M = S.M` and `ϖ = S.deltaE`.
Then there are a real point `g₀` and a linear form `t` with the following property for every form
`ψ` on `H`, class `c` and real point `x` of the group of `V`. The value of `ψ` at the representative
`c.out`, taken to the coordinates of the Bessel function by the linear isomorphism
`h.weylBesselEquiv`, paired with the full, uncut Bessel function `S.besselFn .full` at the image of
`x` in the real group of `S`, is `∫_{R(F_∞)} conj e (g₀⁻¹ s⁻¹ x) 𝒲 (s, h_c) ds`. Here
`e = typeKernel l ε` is the kernel of the type, `(s, h_c) = h.classSection c s` with `h_c` the
finite point of `c`, and `𝒲 = sourceFn t` of the translate of `ψ` by `η`. -/
theorem exists_dotProduct_besselFn_eq_integral [WeilData E] (h : S.Fits V l kw Y η)
    (hj_genericConst : WeilData.j * Y.genericConst = -(S.M * S.deltaE : E)⁻¹) :
    ∃ (g₀ : GInf E ε) (t : (WeylIndex 𝔰.κ kw → ℂ) →ₗ[ℂ] ℂ),
      ∀ (ψ : AlgForm (E := E) 𝔰.κ kw 0) (c : S.Classes) (x : GInf E ε),
        h.weylBesselEquiv (ψ.val c.out) ⬝ᵥ S.besselFn .full (h.realHomeomorph x) =
          ∫ s : Y.besselReal, conj (typeKernel l ε (g₀⁻¹ * s.1⁻¹ * x)) *
            Y.sourceFn t (algFormRep kw 0 η ψ) (h.classSection c s) ∂haar := by
  -- Invert the variable, as `R(F_∞)` is unimodular, and compare the integrands.
  obtain ⟨g₀, t, h_formula⟩ := h.exists_besselFn_eq_integral
  have := Y.isMulRightInvariant_haar_besselReal_besselFin.1
  have : SecondCountableTopology Y.besselReal := inferInstance
  refine ⟨g₀, t, fun ψ c x ↦ ?_⟩
  rw [h_formula, ← integral_inv_eq_self]
  refine integral_congr_ae (.of_forall fun s ↦ ?_)
  let s' : Y.besselGroup := ⟨(s.1, 1), s.2⟩
  have h_inv : (⟨((s⁻¹).1, 1), (s⁻¹).2⟩ : Y.besselGroup) = s'⁻¹ := Subtype.ext (by simp [s'])
  have h_char : (h.besselChar ((s⁻¹).1, 1))⁻¹ = h.besselChar (s.1, 1) :=
    inv_eq_of_mul_eq_one_left <| by
      simp [s', ← h.besselChar_mul s'.2 (r' := ((s⁻¹).1, 1)) (s⁻¹).2, ← h.besselChar_inclX 1]
  simp only [h.sourceFn_classSection hj_genericConst, h_char, h_inv, map_inv]
  rfl

/-- **Moving the quotient by `U_c` from `G(F_∞)` to `R(F_∞)`.** Suppose `V` fits the admissible
filling data `S`, and let `G(F_∞) = GInf E ε` and `R(F_∞) = Y.besselReal`. Let `y` be a form of type
`e` (`V.IsForm e y`), for an integrable continuous `e`, and of level `S.stdPrincipalLevel`. Let `W`
on `R(F_∞)` be measurable, left invariant under `U_c` and integrable over `U_c \ R(F_∞)`. Then
`∫_{U_c \ G(F_∞)} (∫_{R(F_∞)} e (g₀⁻¹ s⁻¹ x) W (s) ds) y (x, h_c) dx` equals
`∫_{U_c \ R(F_∞)} W (s) y (s g₀, h_c) ds`. -/
lemma integral_classCutoff_integral_mul [WeilData E]
    (h : S.Fits V l kw Y η) [S.IsAdmissible] (c : S.Classes)
    {e : GInf E ε → ℂ} (he_cont : Continuous e) (he : Integrable e) (g₀ : GInf E ε)
    {y : New.G E ε → ℂ} (hy : V.IsForm e y)
    (hy_level : HasLevel y S.stdPrincipalLevel.toSubgroup)
    {W : Y.besselReal → ℂ} (hW : Measurable W)
    (hW_inv : ∀ (u : S.classUnipotent c) (s : Y.besselReal),
      W (h.classUnipotentToReal c u * s) = W s)
    (hW_int : Integrable
      (fun s : Y.besselReal ↦ (S.classCutoff c (h.realHomeomorph s)).toReal • W s) haar) :
    ∫ x : GInf E ε, (S.classCutoff c (h.realHomeomorph x)).toReal •
        (∫ s : Y.besselReal, e (g₀⁻¹ * s.1⁻¹ * x) * W s ∂haar) * y (x, h.classPoint c) =
      ∫ s : Y.besselReal, (S.classCutoff c (h.realHomeomorph s)).toReal •
        (W s * y (s * g₀, h.classPoint c)) ∂haar := by
  let F (p : Y.besselReal × GInf E ε) : ℂ :=
    W p.1 * (e (g₀⁻¹ * p.1.1⁻¹ * p.2) * y (p.2, h.classPoint c))
  have hy_cont : Continuous y := hy.continuous
  have hF_inv (u : S.classUnipotent c) (s : Y.besselReal) (x : GInf E ε) :
      F (h.classUnipotentToReal c u * s, h.classUnipotentToReal c u * x) = F (s, x) := by
    obtain ⟨k, hk, h_eq⟩ := h.exists_ratEquiv_mul_classPoint u
    have hy_inv : y (h.classUnipotentToReal c u * x, h.classPoint c) = y (x, h.classPoint c) := by
      rw [← hy_level k hk, ← h_eq, hy.rat_mul _ (h.ratEquiv u).2]
    simp [F, hW_inv, hy_inv, mul_assoc]
  -- All converges: `y` is bounded, `e` is integrable, and `W` is integrable over `U_c \ R(F_∞)`.
  have hF_int : Integrable (fun p ↦
      (S.classCutoff c (h.realHomeomorph p.1)).toReal • F p) (haar.prod volume) := by
    obtain ⟨C, hC⟩ := hy.bounded
    have hy_meas : AEStronglyMeasurable
        (fun p : Y.besselReal × GInf E ε ↦ y (p.2, h.classPoint c)) (haar.prod volume) := by
      fun_prop
    simpa only [F, smul_mul_assoc, mul_assoc] using
      (integrable_mul_comp_inv_mul hW_int he g₀⁻¹).mul_bdd hy_meas (.of_forall fun p ↦ hC _)
  -- The kernel `e` reproduces `y`.
  have h_fix (s : Y.besselReal) : ∫ x : GInf E ε, F (s, x) = W s * y (s * g₀, h.classPoint c) := by
    rw [← congrFun (hy.realConv_eq he) (s * g₀, h.classPoint c), realConv, ← integral_const_mul,
      ← integral_mul_left_eq_self _ (s * g₀ : GInf E ε)]
    simp [F, mul_assoc]
  calc _ = ∫ x, (S.classCutoff c (h.realHomeomorph x)).toReal • ∫ s, F (s, x) ∂haar := by
        simp only [F, smul_mul_assoc, ← integral_mul_const, mul_assoc, mul_left_comm (W _)]
    _ = ∫ s, (S.classCutoff c (h.realHomeomorph s.1)).toReal • (∫ x, F (s, x)) ∂haar :=
        integral_cutoff_swap volume haar (h.classUnipotentToReal c) (by fun_prop)
          (h.tsum_classCutoff_realHomeomorph c) (by fun_prop) hF_inv hF_int
    _ = _ := by simp only [h_fix]

/-! ### The period, class by class -/

/-- The finite part of a point of the unipotent group of `Y`, in the lattice basis of `S`, lies in
the Bessel unipotent group `besselU`. -/
lemma adelicToFin_adelicEquiv_mem_besselU (h : S.Fits V l kw Y η) {u : New.G E ε}
    (hu : u ∈ Y.unipotent) : S.adelicToFin (h.adelicEquiv u) ∈ besselU :=
  toLatticeBasis_mem_besselU.mpr ((h.mem_unipotent_iff_mem_besselU.mp hu).map_mem_agreeWithOneOn _)

/-- Suppose `V` fits `S` (`h`). Let `k` be a point of `Y.besselFin` that lies in the principal level
`S.stdPrincipalLevel`. Then `(1, k) = u * Y.inclX (1, a)` for some `a` in the level `S.sourceLevel`
and some `u` in the unipotent subgroup `Y.unipotent` of the grading with `h.besselChar u = 1`. -/
lemma exists_eq_unipotent_mul_inclX (h : S.Fits V l kw Y η) [S.IsAdmissible]
    {k : Gf E 𝔰.BesselIndex} (hk : k ∈ Y.besselFin) (hk_level : k ∈ S.stdPrincipalLevel) :
    ∃ u ∈ Y.unipotent, ∃ a ∈ S.sourceLevel,
      h.besselChar u = 1 ∧ ((1, k) : New.G E ε) = u * Y.inclX (1, a) := by
  -- Take the finite parts of the two factors of `(1, k)` in `R = U ⋊ H`.
  let a : Gf E 𝔰.κ := (Y.leviPart ⟨(1, k), hk⟩).2
  let u : New.G E ε := (1, k * (Y.inclXFin a)⁻¹)
  have hu : u ∈ Y.unipotent := by
    have h_snd : (Y.inclX (Y.leviPart ⟨(1, k), hk⟩)).2 = Y.inclXFin a :=
      (congrArg Prod.snd (Y.inclX_mk_one_snd _)).symm
    simpa [h_snd] using Y.mk_one_snd_mem_unipotent (Y.mul_inv_inclX_leviPart_mem ⟨(1, k), hk⟩)
  have hu_conj : h.finiteEquiv u.2 ∈ besselU := by
    rw [finiteEquiv_eq_conj_adelicToFin]
    -- The group `besselS`, which contains the image of `η⁻¹`, normalizes `besselU`.
    simpa using (besselS_le_normalizer_besselU (mem_partialUnitriangularGroup_of_mem_floorGroup
      (inclHFin_mem_besselH η⁻¹)) _).1 (h.adelicToFin_adelicEquiv_mem_besselU hu)
  have hk' : h.finiteEquiv u.2 * S.inclHFin a ∈ S.principalLevel := by
    simpa [u, finiteEquiv_inclXFin] using h.mem_stdPrincipalLevel_iff.mp hk_level
  -- The factor in `H` of an element of the level lies in the level, and then so does `u`.
  have ha : S.inclHFin a ∈ S.principalLevel := by
    rw [principalLevel_eq_unitaryLevel] at hk' ⊢
    exact mem_unitaryLevel_of_besselU_mul hu_conj (inclHFin_mem_besselH a) hk'
  have h_char : S.unipotentChar (S.adelicToFin (h.adelicEquiv u)) = S.unipotentChar 1 :=
    unipotentChar_eq_of_mem_principalLevel (one_mem _)
      (h.adelicToFin_adelicEquiv_mem_besselU hu) η <| by
      rw [← finiteEquiv_eq_conj_adelicToFin]
      simpa using mul_mem hk' (inv_mem ha)
  refine ⟨u, hu, a, IsAdmissible.sourceLevel_eq.ge ha, ?_, by simp [u, Y.inclX_inr]⟩
  -- The real part of `u` is trivial, so the adelic character at `u` is the finite character.
  have h_real : S.adelicToInf (h.adelicEquiv u) = 1 := by
    simpa [u] using (h.realHomeomorph_mul u 1).symm
  have h_quot : h.besselChar u / S.unipotentChar (S.adelicToFin (h.adelicEquiv u)) = 1 := by
    rw [besselChar, ← S.prod_wave_simpleRootSum_adelicToInf, h_real]
    simp [simpleRootSum_eq_zero_of_mem_besselH (one_mem _), wave]
  rwa [h_char, unipotentChar_one, div_one] at h_quot

/-- Suppose `V` fits `S` (`h`), `S` is admissible and `ȷ c = -(M ϖ)⁻¹`, with `ȷ = WeilData.j`,
`c = Y.genericConst`, `M = S.M`, `ϖ = S.deltaE`. Let `t` be a linear functional and `ψ` an algebraic
form fixed by `S.sourceLevel`. Let `𝒲 = Y.sourceFn t (algFormRep kw 0 η ψ)`, built from the
translate of `ψ` by `η`. Then `𝒲 (r * Y.besselProdEquiv (1, k)) = 𝒲 (r)` for `r` in `Y.besselGroup`
and `k` in `Y.besselFin` lying in the principal level `S.stdPrincipalLevel`. -/
lemma sourceFn_mul_of_mem_stdPrincipalLevel [WeilData E] (h : S.Fits V l kw Y η) [S.IsAdmissible]
    (hj_genericConst : WeilData.j * Y.genericConst = -(S.M * S.deltaE : E)⁻¹)
    (t : (WeylIndex 𝔰.κ kw → ℂ) →ₗ[ℂ] ℂ)
    (ψ : levelSpace (algFormRep kw 0) S.sourceLevel) (r : Y.besselGroup) {k : Y.besselFin}
    (hk : (k : Gf E 𝔰.BesselIndex) ∈ S.stdPrincipalLevel) :
    Y.sourceFn t (algFormRep kw 0 η ψ.1) (r * Y.besselProdEquiv (1, k)) =
      Y.sourceFn t (algFormRep kw 0 η ψ.1) r := by
  obtain ⟨u, hu, a, ha, h_char, h_eq⟩ := h.exists_eq_unipotent_mul_inclX k.2 hk
  let u' : Y.besselGroup := ⟨u, Y.unipotent_le_besselGroup hu⟩
  have h_split : Y.besselProdEquiv (1, k) = u' * ⟨_, Y.inclX_mem_besselGroup (1, a)⟩ :=
    Subtype.ext h_eq
  have h_fix : algFormRep kw 0 a (algFormRep kw 0 η ψ.1) = algFormRep kw 0 η ψ.1 := by
    have h_level : algFormRep kw 0 a ψ.1 = ψ.1 := by simpa using ψ.2 ⟨a, ha⟩
    rw [← Module.End.mul_apply, ← map_mul, ← (h.central a).eq, map_mul, Module.End.mul_apply,
      h_level]
  rw [h_split, ← mul_assoc, Y.sourceFn_mul_inclX, h_fix,
    h.sourceFn_eq_besselChar_mul hj_genericConst, h.sourceFn_eq_besselChar_mul hj_genericConst,
    map_mul, (Y.leviPart_eq_one_iff (r := u')).mpr hu, mul_one,
    Subgroup.coe_mul, h.besselChar_mul r.2 u'.2, h_char, mul_one]

/-- Suppose `V` fits `S` (`h`) and `S` is admissible. Every point `r` of the Bessel group
`Y.besselGroup` can be moved by a rational point `γ` of `Y.ratBessel` so that the finite part of
`γ * r` lies in `h_c J` for some `c` in `S.Classes`. -/
lemma exists_ratBessel_mul_mem_coset (h : S.Fits V l kw Y η) [S.IsAdmissible] (r : Y.besselGroup) :
    ∃ γ ∈ Y.ratBessel, ∃ c : S.Classes,
      (h.classPoint c)⁻¹ * (γ * r : New.G E ε).snd ∈ S.stdPrincipalLevel := by
  -- Write `r = n a` and `a_fin η = δ c k` with `δ` rational, `c` a class and `k` in the level of
  -- the source forms, and approximate `n` by a rational unipotent `u`. Then `γ = δ⁻¹ u⁻¹` serves.
  let a : New.G E (1 : 𝔰.κ → ℤˣ) := Y.leviPart r
  let n : New.G E ε := r * (Y.inclX a)⁻¹
  obtain ⟨c, δ, k, h_dec⟩ : ∃ (c : S.Classes) (δ : U (stdSpace E 𝔰.κ).J) (k : S.sourceLevel),
      a.2 * η = stdEmbFin δ * c.out * k :=
    exists_eq_map_mul_rep_mul stdEmbFin S.sourceLevel (fun c ↦ c.out_eq) _
  let err (u : S.G E) := (S.inclHFin (a.2 * η))⁻¹ *
    ((S.adelicToFin (h.adelicEquiv n))⁻¹ * S.ratToFin u) * S.inclHFin (a.2 * η)
  obtain ⟨u, hu, h_approx⟩ : ∃ u ∈ besselU, err u ∈ S.principalLevel := exists_besselU_approx
    (h.adelicToFin_adelicEquiv_mem_besselU (Y.mul_inv_inclX_leviPart_mem r)) _
  let δ' : New.G E (1 : 𝔰.κ → ℤˣ) := (stdSpace E 𝔰.κ).ratEmbed δ⁻¹
  have hδ'_fin : δ'.2 = (stdEmbFin δ)⁻¹ := map_inv stdEmbFin δ
  have hu_rat : (h.ratEquiv u⁻¹ : New.G E ε) ∈ Y.ratBessel := mem_inf.mpr
    ⟨(h.ratEquiv u⁻¹).2, Y.unipotent_le_besselGroup (h.ratEquiv_mem_unipotent (inv_mem hu))⟩
  refine ⟨Y.inclX δ' * h.ratEquiv u⁻¹, mul_mem (Y.inclX_mem_ratBessel ⟨δ⁻¹, rfl⟩) hu_rat, c, ?_⟩
  -- Seen from the class `c`, the moved point is `k` divided by the error of the approximation.
  have h_eq : (S.classRep c)⁻¹ * (S.inclHFin η *
      h.finiteEquiv (Y.inclX δ' * h.ratEquiv u⁻¹ * (n * Y.inclX a)).2) =
      S.inclHFin k * (err u)⁻¹ := by
    simp only [finiteEquiv_eq_conj_adelicToFin, map_mul h.adelicEquiv, map_mul S.adelicToFin,
      adelicEquiv_ratEquiv]
    simp [err, adelicToFin_adelicEquiv_inclX, hδ'_fin, eq_mul_inv_of_mul_eq h_dec, ratToFin,
      mul_assoc]
  rw [inv_classPoint_mul_mem_iff, ← inv_mul_cancel_right r.1 (Y.inclX a), h_eq]
  exact mul_mem (IsAdmissible.sourceLevel_eq.le k.2) (inv_mem h_approx)

/-- Let `c`, `d` be classes, `J = S.stdPrincipalLevel` the principal level, and
`U_c = S.classUnipotent c`. Suppose the finite part of `g` lies in `h.classPoint d * J`, `γ` is in
`Y.ratBessel`, and the finite part of `γ g` lies in `h.classPoint c * J`. Then `c = d` and
`γ = h.ratEquiv u` for some `u` in `U_c`. -/
lemma eq_and_exists_classUnipotent_of_mem_coset (h : S.Fits V l kw Y η) [S.IsAdmissible]
    {c d : S.Classes} {g γ : New.G E ε} (hg : (h.classPoint d)⁻¹ * g.2 ∈ S.stdPrincipalLevel)
    (hγ : γ ∈ Y.ratBessel) (hγg : (h.classPoint c)⁻¹ * (γ * g).2 ∈ S.stdPrincipalLevel) :
    c = d ∧ ∃ u : S.classUnipotent c, (h.ratEquiv u : New.G E ε) = γ := by
  obtain ⟨hγ_rat, hγ_bessel⟩ : γ ∈ V.Γ ∧ γ ∈ Y.besselGroup := mem_inf.mp hγ
  obtain ⟨σ, rfl⟩ : ∃ σ : S.G E, (h.ratEquiv σ : New.G E ε) = γ :=
    ⟨h.ratEquiv.symm ⟨γ, hγ_rat⟩, by simp⟩
  have h_mem_level : S.translateByClassReps c d σ ∈ S.principalLevel := by
    rw [inv_classPoint_mul_mem_iff] at hg hγg
    simpa [translateByClassReps, ratToFin, mul_assoc,
      h.finiteEquiv_eq_conj_adelicToFin (h.ratEquiv σ),
      adelicEquiv_ratEquiv] using mul_mem hγg (inv_mem hg)
  obtain ⟨hcd, hσ⟩ := eq_and_mem_classUnipotent_of_besselS
    (h.mem_besselS_of_ratEquiv_mem_besselGroup hγ_bessel) h_mem_level
  exact ⟨hcd, ⟨σ, hσ⟩, rfl⟩

variable [WeilData E]

open scoped Classical in
/-- The weight on `R(𝔸)` that is `β_c (r_∞)` if `r_fin` lies in `h_c J` and zero otherwise, where
`β_c` is the cutoff of the class `c`. -/
def classWeight (h : S.Fits V l kw Y η) (c : S.Classes) (r : Y.besselGroup) : ENNReal :=
  if (h.classPoint c)⁻¹ * (r : New.G E ε).2 ∈ S.stdPrincipalLevel then
    S.classCutoff c (h.realHomeomorph (r : New.G E ε).1)
  else
    0

/-- For each class `c`, the weight `h.classWeight c` on the Bessel group `Y.besselGroup` is a
measurable function. -/
@[fun_prop]
lemma measurable_classWeight (h : S.Fits V l kw Y η) [S.IsAdmissible] (c : S.Classes) :
    Measurable (h.classWeight c) :=
  .indicator (by fun_prop) S.stdPrincipalLevel.isOpen'.preimage_of_continuous.measurableSet

/-- Suppose `V` fits `S` (`h`). The sum over classes `c` of `h.classWeight c r` is a cutoff for the
action of `R(F) = Y.ratBessel` on `R(𝔸) = Y.besselGroup`: it is measurable and sums to 1 over each
`R(F)`-orbit. -/
lemma isCutoff_sum_classWeight (h : S.Fits V l kw Y η) [S.IsAdmissible] :
    IsCutoff (count : Measure (Y.ratBessel.subgroupOf Y.besselGroup))
      fun r : Y.besselGroup ↦ ∑ c : S.Classes, h.classWeight c r := by
  refine ⟨by fun_prop, fun r ↦ ?_⟩
  rw [lintegral_count]
  -- Move `r` into `G(F_∞) × h_d J`.
  wlog hr : ∃ d : S.Classes, (h.classPoint d)⁻¹ * (r : New.G E ε).2 ∈ S.stdPrincipalLevel
    generalizing r with h_moved
  · obtain ⟨γ, hγ, hγr⟩ := h.exists_ratBessel_mul_mem_coset r
    let γ' : Y.ratBessel.subgroupOf Y.besselGroup := ⟨⟨γ, (mem_inf.mp hγ).2⟩, hγ⟩
    rw [← (Equiv.mulRight γ').tsum_eq]
    simpa only [Equiv.coe_mulRight, mul_smul] using h_moved (γ' • r) hγr
  obtain ⟨d, hd⟩ := hr
  -- Only the class `d` and the elements of `U_d` contribute, and they give `∑_u β_d (u r_∞) = 1`.
  let ι (u : S.classUnipotent d) : Y.ratBessel.subgroupOf Y.besselGroup :=
    have hu := h.ratEquiv_classUnipotent_mem_besselGroup u
    ⟨⟨h.ratEquiv u, hu⟩, (h.ratEquiv u).2, hu⟩
  have hι : Injective ι := fun u u' h_eq ↦ Subtype.ext <| h.ratEquiv.injective <|
    Subtype.ext (congrArg (fun γ ↦ (γ.1 : New.G E ε)) h_eq)
  have h_ne (γ) (c : S.Classes) (hc : h.classWeight c (γ • r) ≠ 0) : c = d ∧ γ ∈ Set.range ι := by
    obtain ⟨rfl, u, hu⟩ := h.eq_and_exists_classUnipotent_of_mem_coset hd γ.2
      (by_contra fun h_not ↦ hc (ite_eq_right h_not))
    exact ⟨rfl, u, Subtype.ext (Subtype.ext hu)⟩
  have h_term (u : S.classUnipotent d) : h.classWeight d (ι u • r) =
      S.classCutoff d (h.realHomeomorph (h.classUnipotentToReal d u * (r : New.G E ε).1)) := by
    obtain ⟨k, hk, h_eq⟩ := h.exists_ratEquiv_mul_classPoint u
    have h_fin : (h.ratEquiv u : New.G E ε).2 * h.classPoint d = h.classPoint d * k :=
      congrArg Prod.snd (h_eq 1)
    have h_mem : (h.classPoint d)⁻¹ * ((h.ratEquiv u : New.G E ε).2 * (r : New.G E ε).2) ∈
        S.stdPrincipalLevel := by
      simpa [eq_mul_inv_of_mul_eq h_fin, mul_assoc] using mul_mem hk hd
    exact ite_eq_left h_mem
  calc ∑' γ : Y.ratBessel.subgroupOf Y.besselGroup, ∑ c, h.classWeight c (γ • r)
      = ∑' γ : Y.ratBessel.subgroupOf Y.besselGroup, h.classWeight d (γ • r) :=
        tsum_congr fun γ ↦ sum_eq_single d fun c hc ↦
          by_contra fun h_nonzero ↦ hc (h_ne γ c h_nonzero).1
    _ = ∑' u : S.classUnipotent d, h.classWeight d (ι u • r) :=
        (hι.tsum_eq fun γ hγ ↦ (h_ne γ d hγ).2).symm
    _ = 1 := by simp only [h_term, tsum_classCutoff_realHomeomorph]

/-- **The quotient `[R] / J'` is the disjoint union of the `U_c \ R(F_∞)`.** Suppose `V` fits the
admissible filling data `S`.

There is a constant `volJ' ≠ 0` such that, with `J' = R(𝔸_fin) ∩ J` and `R(𝔸_fin) = Y.besselFin`,
the following holds for every measurable function `F` on `R(𝔸)` that is left invariant under `R(F)`,
right invariant under `J'` and integrable over `[R]`. Each function `s ↦ F (s, h_c)` is integrable
over `U_c \ R(F_∞)`, and `∫_{[R]} F = volJ' ∑_c ∫_{U_c \ R(F_∞)} F (s, h_c) ds`. -/
theorem exists_integral_besselMeasure_eq_sum (h : S.Fits V l kw Y η) [S.IsAdmissible] :
    ∃ volJ' : ℝ, volJ' ≠ 0 ∧ ∀ {F : Y.besselGroup → ℂ}, Measurable F →
      (Y.ratBessel.subgroupOf Y.besselGroup).FixesLeft F →
      (∀ (r : Y.besselGroup) (k : Y.besselFin), (k : Gf E 𝔰.BesselIndex) ∈ S.stdPrincipalLevel →
        F (r * Y.besselProdEquiv (1, k)) = F r) →
      Integrable F Y.besselMeasure →
        (∀ c : S.Classes, Integrable (fun s : Y.besselReal ↦
          (S.classCutoff c (h.realHomeomorph s)).toReal • F (h.classSection c s)) haar) ∧
        ∫ r : Y.besselGroup, F r ∂Y.besselMeasure =
          volJ' * ∑ c : S.Classes, ∫ s : Y.besselReal,
            (S.classCutoff c (h.realHomeomorph s)).toReal • F (h.classSection c s) ∂haar := by
  -- Compute the integral over `[R]` with the cutoff `∑_c classWeight c`. The term of `c` lives on
  -- `R(F_∞) × h_c J'`, where `F` depends only on the real point.
  have : IsLevel S.stdPrincipalLevel.toSubgroup := ⟨levelOf_le_stdLevel, S.stdPrincipalLevel.isOpen⟩
  obtain ⟨volJ', h_vol, h_coset⟩ :=
    Y.exists_integral_eq_mul_integral_besselReal S.stdPrincipalLevel.toSubgroup
  refine ⟨volJ', h_vol, fun {F} hF hF_rat hF_level hF_int ↦ ?_⟩
  let Φ (c : S.Classes) (s : Y.besselReal) : ℂ :=
    (S.classCutoff c (h.realHomeomorph s)).toReal • F (h.classSection c s)
  have h_cut : IsCutoff (count : Measure (Y.ratBessel.subgroupOf Y.besselGroup))
      fun r : Y.besselGroup ↦ ∑ c : S.Classes, h.classWeight c r := h.isCutoff_sum_classWeight
  have h_inv (γ : Y.ratBessel.subgroupOf Y.besselGroup) (r : Y.besselGroup) : F (γ • r) = F r :=
    hF_rat γ γ.2 r
  have h_fin : ∀ᵐ r : Y.besselGroup ∂haar, ∑ c, h.classWeight c r < ⊤ := h_cut.ae_cutoff_lt_top
  have h_int (c : S.Classes) : Integrable (fun r ↦ (h.classWeight c r).toReal • F r) haar := by
    have h_sum : Integrable (fun r ↦ (∑ c, h.classWeight c r).toReal • F r) haar :=
      (h_cut.integrable_orbitMeasure_iff h_inv hF).mp hF_int
    refine h_sum.mono (by fun_prop) (h_fin.mono fun r hr ↦ ?_)
    simp only [norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    gcongr
    exacts [hr.ne, Finset.single_le_sum (f := fun c ↦ h.classWeight c r) (by simp) (by simp)]
  have h_prod (c : S.Classes) (s : Y.besselReal) (k : Y.besselFin) :
      (h.classWeight c (h.classSection c s * Y.besselProdEquiv (1, k))).toReal •
          F (h.classSection c s * Y.besselProdEquiv (1, k)) =
        Φ c s * (S.stdPrincipalLevel.toSubgroup : Set (Gf E 𝔰.BesselIndex)).indicator 1 k.1 := by
    by_cases hk : k.1 ∈ S.stdPrincipalLevel
    · rw [hF_level _ k hk]
      simp [Φ, classWeight, classSection, Grading.besselProdEquiv, hk]
    · simp [classWeight, classSection, Grading.besselProdEquiv, hk]
  have h_class (c : S.Classes) : Integrable (Φ c) haar ∧
      ∫ r, (h.classWeight c r).toReal • F r ∂haar = volJ' * ∫ s, Φ c s ∂haar :=
    h_coset ⟨h.classPoint c, h.classPoint_mem_besselFin c⟩ (fun s k ↦ by
      simpa only [classSection, ← map_mul, Prod.mk_mul_mk, mul_one] using h_prod c s k) (h_int c)
  refine ⟨fun c ↦ (h_class c).1, ?_⟩
  calc ∫ r, F r ∂Y.besselMeasure
      = ∫ r, (∑ c, h.classWeight c r).toReal • F r ∂haar := h_cut.integral_orbitMeasure h_inv
    _ = ∫ r, ∑ c, (h.classWeight c r).toReal • F r ∂haar := by
        refine integral_congr_ae (h_fin.mono fun r hr ↦ ?_)
        simp only [ENNReal.toReal_sum fun c hc ↦ (ENNReal.sum_lt_top.mp hr c hc).ne,
          Finset.sum_smul]
    _ = ∑ c, ∫ r, (h.classWeight c r).toReal • F r ∂haar :=
        integral_finsetSum _ fun c _ ↦ h_int c
    _ = _ := by simp only [fun c ↦ (h_class c).2, Finset.mul_sum, Φ]

/-! ### The series represents the period -/

omit [WeilData E] in
/-- The coordinate `(c, i)` of a source form `ψ` is the `i`-th coordinate of its value at the
representative of the class `c`. -/
lemma sourceFormCoords_apply (h : S.Fits V l kw Y η)
    (ψ : levelSpace (algFormRep kw 0) S.sourceLevel) (c : S.Classes) (i : S.BesselCoord) :
    h.sourceFormCoords ψ (c, i) =
      h.weylBesselEquiv ((ψ : AlgForm (E := E) 𝔰.κ kw 0).val c.out) i :=
  rfl

/-- **The Poincaré series represents a Bessel period.** Suppose `V` with the grading `Y` fits the
admissible filling data `S`: the type, the indexing and the lattice of `V` agree with those of `S`,
up to the central element `η` of `H(𝔸_fin)`. Let `ȷ Y.genericConst = -(M ϖ)⁻¹`, with
`ȷ = WeilData.j`, `M = S.M` and `ϖ = S.deltaE`, so that the character of the filling data is `ψ_U`.
There are a real point `g₀` and a linear form `t` with `∫_{[G]} y · 𝒫 ψ = ∫_{[R]} 𝒲 (r) y (r g₀) dr`
for every source form `ψ` and every form `y` of the conjugate type and principal level. Here `𝒫 ψ`
is the series over `G(F)` of the Bessel function, with coefficients the values
`h.sourceFormCoords ψ` of `ψ` at the class representatives, and `𝒲` is `sourceFn t` of the translate
of `ψ` by `η`. -/
theorem exists_integral_poincareSeries_eq_period (h : S.Fits V l kw Y η) [S.IsAdmissible]
    (hj_genericConst : WeilData.j * Y.genericConst = -(S.M * S.deltaE : E)⁻¹) :
    ∃ (g₀ : GInf E ε) (t : (WeylIndex 𝔰.κ kw → ℂ) →ₗ[ℂ] ℂ),
      ∀ (ψ : levelSpace (algFormRep kw 0) S.sourceLevel) {y : New.G E ε → ℂ},
        V.IsForm (star (typeKernel l ε)) y → HasLevel y S.stdPrincipalLevel.toSubgroup →
        ∫ x : New.G E ε, (y * h.poincareSeries (h.sourceFormCoords ψ)) x ∂V.Γ.quotMeasure =
          ∫ r : Y.besselGroup, Y.sourceFn t (algFormRep kw 0 η ψ.1) r *
            y (r.1 * (g₀, 1)) ∂Y.besselMeasure := by
  -- Both sides are multiples of `∑_c ∫_{U_c \ R(F_∞)} 𝒲 (s, h_c) y (s g₀, h_c) ds`; the ratio of
  -- the two factors goes into the linear form.
  obtain ⟨g₀, t, h_bessel⟩ := h.exists_dotProduct_besselFn_eq_integral hj_genericConst
  obtain ⟨volJ', h_vol, h_classes⟩ := h.exists_integral_besselMeasure_eq_sum
  let volJ : ℝ := volume.real S.stdPrincipalLevel.carrier
  refine ⟨g₀, (volJ / volJ' : ℂ) • t, fun ψ y hy hy_level ↦ ?_⟩
  let W : Y.besselGroup → ℂ := Y.sourceFn t (algFormRep kw 0 η ψ.1)
  have hW : Y.IsEquivariant W := Y.isEquivariant_sourceFn (odd_two_mul_add_one _) _ _
  have hW_cont : Continuous W := hW.continuous
  have hy_cont : Continuous y := hy.continuous
  have hW_rat : (Y.ratBessel.subgroupOf Y.besselGroup).FixesLeft W :=
    fun γ hγ ↦ hW.rat_mul γ (mem_subgroupOf.mp hγ).1
  have hW_level (r) (k : Y.besselFin) (hk : k.1 ∈ S.stdPrincipalLevel) :
      W (r * Y.besselProdEquiv (1, k)) = W r :=
    h.sourceFn_mul_of_mem_stdPrincipalLevel hj_genericConst t ψ r hk
  -- The function `𝒲` is integrable over each `U_c \ R(F_∞)`, since `[R]` is compact.
  obtain ⟨hW_int, -⟩ := h_classes hW_cont.measurable hW_rat hW_level
    (integrable_of_isCocompact Y.isCocompact_ratBessel hW_cont hW_rat)
  have hW_inv (c : S.Classes) (u : S.classUnipotent c) (s : Y.besselReal) :
      W (h.classSection c (h.classUnipotentToReal c u * s)) = W (h.classSection c s) := by
    obtain ⟨k, hk, h_eq⟩ := h.exists_ratEquiv_mul_classPoint u
    let γ : Y.besselGroup := ⟨h.ratEquiv u, h.ratEquiv_classUnipotent_mem_besselGroup u⟩
    have h_move : γ * h.classSection c s = h.classSection c (h.classUnipotentToReal c u * s) *
        Y.besselProdEquiv (1, k) := Subtype.ext (h_eq s)
    rw [← hW_level _ k hk, ← h_move, hW.rat_mul γ (h.ratEquiv u).2]
  -- The period integrates a function `F` on `[R]` that is right invariant under `J'`.
  let F (r : Y.besselGroup) : ℂ := W r * y (r.1 * (g₀, 1))
  have hF_rat : (Y.ratBessel.subgroupOf Y.besselGroup).FixesLeft F := fun γ hγ r ↦ by
    simp [F, hW_rat γ hγ r, mul_assoc, hy.rat_mul _ (mem_subgroupOf.mp hγ).1]
  have hF_level (r) (k : Y.besselFin) (hk : k.1 ∈ S.stdPrincipalLevel) :
      F (r * Y.besselProdEquiv (1, k)) = F r := by
    simp only [F, hW_level r k hk, ← hy_level k hk (r.1 * (g₀, 1))]
    simp [Grading.besselProdEquiv, mul_assoc]
  obtain ⟨-, h_period⟩ :=
    h_classes (by fun_prop) hF_rat hF_level (hW.integrable_mul hy.toIsAutomorphic (g₀, 1))
  calc _ = (volJ : ℂ) * ∑ c, ∫ x, (S.classCutoff c (h.realHomeomorph x)).toReal •
          (∫ s : Y.besselReal, conj (typeKernel l ε (g₀⁻¹ * s.1⁻¹ * x)) *
            W (h.classSection c s) ∂haar) * y (x, h.classPoint c) := by
        simpa only [W, ← h_bessel, dotProduct, sourceFormCoords_apply, Pi.mul_apply] using
          integral_mul_poincareSeries_eq_sum_classes (X := h) (h.sourceFormCoords ψ) hy hy_level
    _ = (volJ : ℂ) * ∑ c, ∫ s : Y.besselReal, (S.classCutoff c (h.realHomeomorph s)).toReal •
          (W (h.classSection c s) * y (s * g₀, h.classPoint c)) ∂haar := by
        congr 2 with c
        exact h.integral_classCutoff_integral_mul c h.isIdempotentKernel.continuous.star
          ((starL' ℝ).integrable_comp_iff.2 h.isIdempotentKernel.integrable) g₀ hy hy_level
          (by unfold classSection; fun_prop) (hW_inv c) (hW_int c)
    _ = (volJ / volJ' : ℂ) * ∫ r : Y.besselGroup, F r ∂Y.besselMeasure := by
        simp [h_period, ← mul_assoc, h_vol, F, classSection, Grading.besselProdEquiv]
    _ = _ := by simp only [F, W, Grading.sourceFn_smul_left, mul_assoc, integral_const_mul]

end New.Filling.Fits

end Fits

namespace New.Data

variable {P : Parameters} (D : Data P)

/-- Let `D` be admissible data for the parameters `P`. They give the CM field `D.E`, the hermitian
spaces `X₀` and `Y₀`, the source forms and the filling data `D.filling` with their Bessel function.
For a real point `g` of the unitary group of `Y₀` and a linear form `t` on the space of values of
the source forms, `D.poincareAt g t φ` is the form on `Y₀` of the chosen type and level whose
Petersson product with every such form is the Bessel period of the source form `φ` (Riesz
representation). There are `g` and `t` such that, for every `φ`, it is the Poincaré series of the
Bessel function with the coefficients `D.sourceFormCoords φ`: the values at the class
representatives of the translate of `φ` by the central element `D.latticeScale 0`, in the
coordinates of the Bessel function. -/
theorem exists_poincareAt_eq_poincareMap_comp :
    ∃ (g : GInf D.E (D.signsY 0)) (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ),
      D.poincareAt g t = D.filling_fits.poincareMap ∘ₗ D.sourceFormCoords.toLinearMap := by
  -- Both forms have the same inner product, the Bessel period, with every form `y`.
  have hj_genericConst : WeilData.j * (D.gradingY 0).genericConst =
      -(D.filling.M * D.filling.deltaE : D.E)⁻¹ := by
    have hj_ne_zero : (WeilData.j : D.E) ≠ 0 := WeilData.j_ne_zero
    simp [gradingY, filling, M, field]
  obtain ⟨g, t, h_period⟩ :=
    D.filling_fits.exists_integral_poincareSeries_eq_period hj_genericConst
  refine ⟨g, t, LinearMap.ext fun φ ↦ ext_inner_left ℂ fun y ↦ ?_⟩
  -- `D.sourceFormCoords φ` are the coordinates of the translate `ψ` of `φ` by the central element
  -- `D.latticeScale 0`; translating back by its inverse gives `φ`.
  let ψ : D.SourceForm := D.centralRep (D.latticeScale 0) φ
  have h_back : algFormRep D.columnCount 0 (scalarFin (D.X 0) (D.latticeScale 0))⁻¹ ψ.1 = φ.1 :=
    (algFormRep D.columnCount 0).inv_self_apply _ φ.1
  let f : New.G D.E (D.signsY 0) → ℂ := y.1
  have hf_form : (D.spaceY 0).IsForm (typeKernel D.paramW (D.signsY 0)) f := y.1.2
  have hf_level : HasLevel (star f) D.filling.stdPrincipalLevel.toSubgroup := by
    intro k hk x
    have h_fix : f (x * (1, k)) = f x :=
      (congrFun (congrArg Subtype.val (y.2 ⟨k, hk⟩)) x).trans (by simp [f])
    exact congrArg star h_fix
  calc inner ℂ y (D.poincareAt g t φ)
      = ∫ r : (D.gradingY 0).besselGroup, (D.gradingY 0).sourceFn t φ.1 r *
          star f (r.1 * (g, 1)) ∂(D.gradingY 0).besselMeasure := D.inner_poincareAt g t φ y
    _ = ∫ x : New.G D.E (D.signsY 0), (star f *
          D.filling_fits.poincareSeries (D.sourceFormCoords φ)) x
          ∂(D.spaceY 0).Γ.quotMeasure := by
        rw [← h_back]
        exact (h_period ψ hf_form.conj hf_level).symm
    _ = inner ℂ y (D.filling_fits.poincareMap (D.sourceFormCoords φ)) := by
        rw [← D.filling_fits.coe_poincareMap]
        rfl

/-- A chosen real point `g` at which, for a suitable linear form `t`, the form `D.poincareAt g t φ`
that represents the Bessel period of every source form `φ` is the Poincaré series of the Bessel
function. -/
def besselPoint : GInf D.E (D.signsY 0) := D.exists_poincareAt_eq_poincareMap_comp.choose

/-- A chosen linear form for which, at the point `D.besselPoint`, the Bessel period is represented
by the Poincaré series. -/
def besselForm : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ :=
  D.exists_poincareAt_eq_poincareMap_comp.choose_spec.choose

/-- The Poincaré map at the chosen point `besselPoint` and linear form `besselForm`: it sends a
source form to the form on `Y₀` that represents its Bessel period, which for this choice is the
Poincaré series of the Bessel function. -/
def poincare : D.SourceForm →ₗ[ℂ] D.principalForms (D.spaceY 0) :=
  D.poincareAt D.besselPoint D.besselForm

/-- The Poincaré map sends a source form `φ` to the Poincaré series of the Bessel function with the
coefficients `D.sourceFormCoords φ`, the values at the class representatives of the central
translate of `φ` by `D.latticeScale 0`. -/
theorem poincare_eq_poincareMap_comp :
    D.poincare = D.filling_fits.poincareMap ∘ₗ D.sourceFormCoords.toLinearMap :=
  D.exists_poincareAt_eq_poincareMap_comp.choose_spec.choose_spec

end New.Data

end
