import Lib.Weil.Seesaw
import New.UpperBound.Objects.AuxiliaryPair
import New.UpperBound.Objects.Columns
import New.UpperBound.Objects.Parameters

/-!
# Spaces Y_j and W_j, the forms on them, and the target parameter

This file treats the hermitian spaces Y_j and W_j and the forms on them, for admissible data
`New.Data` and a tame character ϑ with modulus Q. The chosen places are the prime divisors of
`New.Data.piM`, written π̄₀π̄₁ as one symbol, with conjugate `New.Data.piMBar` written π₀π₁. These
are one half of the places above M = p₀p₁, and N = ππ̄ is the level. The target parameter ς
(`New.Data.targetParameter`) is a staircase whose lower steps are at least the gap h = 2h₂ apart, so
the spaces of forms `New.Data.principalForms` are finite-dimensional. This file also sets up the
levels and Weil representation data along the spaces Y_j, the gaps of the target parameter, and the
Harish-Chandra parameters on the descent pairs (W_j, V_j).

## Main definitions and results

* `New.Data.spaceY`: the spaces Y_j with their lattices; `New.Data.spaceW`: the diagonal spaces W_j.
* `New.Data.goodForms`: the image of the idempotent e₀ on forms of principal level at the chosen
  places.
* `New.Data.isCuspKernel_typeKernel_paramW`: for signs such that entries of ς at indices of opposite
  sign differ by at least h, the kernel of this parameter (`New.Data.paramW` = 2ς) is a cusp kernel
  of order h₂.
* `New.Data.paramsCorrespond_descentPair`, `New.Data.fitsParams_descentPair`: the parameters on W_j
  and V_j correspond, by insertion of the block of the centre −w_j, and the descent pair (W_j, V_j)
  satisfies `New.DescentPair.FitsParams`.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.Data.TameChar`: a character of U(1)(𝔸) of weight 0 with tame part supported on a finite set Q
  of places of norm prime to MN, Q disjoint from its conjugate.
* `New.Data.liftWeight`: the weight w_j = κ(σ) + j·h + h₂ at the infinite place σ, with
  κ = `New.Data.weight`, h the gap and h₂ half the gap.
-/

noncomputable section

/-- The bijection from κ plus a string of length 2ϱ + 1 to the basis indices
`New.Shape.BesselIndex`: κ goes to the x_i, and the string index a goes to e_a if a < ϱ, to z if
a = ϱ and to e*_{2ϱ−a} if a > ϱ (e and e* numbered from 0). -/
def New.Shape.besselIndexEquiv (𝔰 : Shape) : 𝔰.κ ⊕ Fin (2 * 𝔰.ϱ + 1) ≃ 𝔰.BesselIndex :=
  -- The inverse sends `e_i` to `i`, keeps `κ`, sends `z` to `ϱ` and `e*_i` to `2 ϱ - i`.
  Equiv.symm <|
    Equiv.ofBijective
        (Sum.elim (fun i ↦ Sum.inr ⟨i, by grind⟩)
          (Sum.elim (Sum.elim Sum.inl fun _ ↦ Sum.inr ⟨𝔰.ϱ, by grind⟩) fun i ↦
            Sum.inr ⟨2 * 𝔰.ϱ - i, by grind⟩)) <| by
      -- an injection between finite sets of the same size
      simp [↓Fintype.bijective_iff_injective_and_card, Function.Injective]
      grind

namespace New.Data

open Ideal Seesaw

variable {P : Parameters} (D : Data P) (ϑ : D.TameChar) (j : ℕ) {s : D.RowIndex → ℤˣ}
  (V : Space D.E D.RowIndex s) {w : FinPlace D.E}

/-! ### Sizes and places -/

/-- The number ϱ lies between m/4 and m, so that `exp (logX / 2 - 4) ≤ ϱ ≤ exp (logX / 2 + 2)`;
`u` chooses between the upper and the lower bound. -/
instance {u : Bool} : D.HasLogBound u D.ϱ (D.logX / 2 + (if u then 2 else -4)) := by
  have h_mem : (D.ϱ : ℝ) ∈ Set.Icc (D.m / 4 : ℝ) D.m := by
    have h_nat : D.m ≤ 4 * D.ϱ ∧ D.ϱ ≤ D.m := by grind [ten_thousand_le_m]
    simpa [field] using mod_cast h_nat
  exact .of_mem_Icc (D.m / 4) D.m h_mem (by cases u <;> grind [D.scale_inequalities])

/-- A place w of the modulus Q of ϑ, or the conjugate of one, divides the product `ϑ.normQ` of
the norms of the places of Q, and divides neither π̄₀π̄₁ (`D.piM`) nor the level N. -/
lemma normQ_mem_and_notMem_of_mem_Q (hw : w ∈ ϑ.Q ∨ star w ∈ ϑ.Q) :
    (ϑ.normQ : NumberField.RingOfIntegers D.E) ∈ w.asIdeal ∧
      D.piM ∉ w.asIdeal ∧
      (D.N : NumberField.RingOfIntegers D.E) ∉ w.asIdeal := by
  -- `w` contains its norm `q w = q (star w)`, a factor of `ϑ.normQ`.
  have h_dvd : w.q ∣ ϑ.normQ := by grind [Finset.dvd_prod_of_mem, q_star]
  have h_mem : (ϑ.normQ : NumberField.RingOfIntegers D.E) ∈ w.asIdeal :=
    mem_of_dvd _ (Nat.cast_dvd_cast h_dvd) (absNorm_mem _)
  -- `ϑ.normQ` is prime to `D.M * D.N`, where `D.M = D.piM * star D.piM`.
  have h_notMem : D.piM * star D.piM * D.N ∉ w.asIdeal := by
    grind [piM_mul_star, w.isPrime.notMem_of_isCoprime_of_mem ϑ.coprime.cast]
  exact ⟨h_mem, fun h ↦ h_notMem (mul_mem_right _ _ (mul_mem_right _ _ h)),
    fun h ↦ h_notMem (mul_mem_left _ _ h)⟩

/-- The system of places (`New.LevelPlaces`) formed by the chosen places above p₀, p₁ and the places
of the modulus Q of ϑ. -/
def levelPlaces : LevelPlaces D.E where
  ChosenIndex := (i : Fin 2) × D.ChosenPlace i
  TwistIndex := ϑ.Q
  chosenPlace := D.chosenPlace
  twistPlace := (↑)
  -- A chosen place contains `D.piM`; by `normQ_mem_and_notMem_of_mem_Q` a place of `ϑ.Q` or
  -- its conjugate does not.
  apart :=
    { injective := by
        have h_ne (x : Σ i : Fin 2, D.ChosenPlace i) (u : ϑ.Q) : D.chosenPlace x ≠ u := by
          grind [→ normQ_mem_and_notMem_of_mem_Q, Data.chosenPlace]
        exact D.isConjApart_chosenPlace.injective.sumElim Subtype.val_injective h_ne
      star_ne := by
        grind [D.isConjApart_chosenPlace.star_ne, → normQ_mem_and_notMem_of_mem_Q, Data.chosenPlace,
          ϑ.star_notMem, star_star] }

/-- The modulus `ϖ^c Q` if `b` is `true` (the default) and `ϖ^c` if `b` is `false`. Here `ϖ` is the
product of the chosen places above p₀, p₁, and `Q` is the product of the places of the modulus of
`ϑ` (`New.LevelPlaces.levelModulus`). -/
abbrev twistModulus (c : ℕ) (b : Bool := true) : Modulus D.E := (D.levelPlaces ϑ).levelModulus c b

/-- For `c ≠ 0` some place divides the modulus `D.twistModulus ϑ c b`, which is `ϖ^c Q` or `ϖ^c`
with `ϖ` the product of the chosen places. -/
lemma nonempty_modulus_places {D : Data P} {ϑ : D.TameChar} {c : ℕ} {b : Bool} [NeZero c] :
    Nonempty (D.twistModulus ϑ c b).places := by
  -- Any chosen place `x` above `D.levelPrime 0` divides the product of the chosen places.
  let x : Σ i : Fin 2, D.ChosenPlace i := ⟨0, chosenEquiv 0 1⟩
  refine ⟨D.chosenPlace x, ?_⟩
  calc
    (D.twistModulus ϑ c b).ideal ≤ (∏ i, (D.chosenPlace i).asIdeal) ^ c := mul_le_left
    _ ≤ ∏ i, (D.chosenPlace i).asIdeal := pow_le_self NeZero.out
    _ ≤ (D.chosenPlace x).asIdeal := Rows.prod_places_le_iff.2 ⟨x, rfl⟩

/-! ### Ideles, lattices and spaces -/

/-- A finite idele that generates the ideal `(π̄₀ π̄₁)` and is `1` away from the chosen places;
see `valued_chosenIdele` and `chosenIdele_apply_of_not_isChosen`. The ideal is a modulus because
the conjugate of a chosen place is not chosen. -/
def chosenIdele : (𝔸f D.E)ˣ :=
  Modulus.generator
    { ideal := span {D.piM}
      ne_bot := by simp
      not_le_star := by simpa [IsChosen] using fun _ ↦ IsChosen.not_star }

/-- The order of `chosenIdele` at `w` is the multiplicity of `w` in the ideal `(π̄₀ π̄₁)`, where
`π̄₀ π̄₁` is `D.piM`. -/
lemma valued_chosenIdele (w : FinPlace D.E) :
    Valued.v (D.chosenIdele.val w) = .exp (-multiplicity w.asIdeal (span {D.piM})) :=
  Modulus.valued_generator _ w

lemma chosenIdele_apply_of_not_isChosen (hw : ¬D.IsChosen w) : D.chosenIdele.val w = 1 := by
  have h_not_le : ¬span {D.piM} ≤ w.asIdeal := by rwa [span_singleton_le_iff_mem]
  exact (Modulus.generator_spec _).right.left w h_not_le

/-- The finite idele α/β, with α the idele of the Weil data (`New.WeilData`) and β the
conjugate of `chosenIdele`, which generates the ideal (π₀π₁); it generates the fractional ideal
𝔞 = 𝔞₀/π₀π₁, where 𝔞₀ is the ideal of α. -/
def ideleA : (𝔸f D.E)ˣ := WeilData.α / star D.chosenIdele

/-- The principal finite idele of E given by the nonzero element π. -/
def piNIdele : (𝔸f D.E)ˣ := principalIdele (Units.mk0 D.piN (by simp) : D.Eˣ)

/-- The principal idele of `π` satisfies `N = π π̄`, is a uniformiser at the places `D.piNPlaces`
that divide `π` and a unit elsewhere, and no place of `D.piNPlaces` has its conjugate there. -/
lemma isSplitSquarefree_piNIdele : IsSplitSquarefree D.piNPlaces D.N D.piNIdele := by
  refine ⟨?_, fun w ↦ ?_, D.isSplitLevel_piNPlaces.star_notMem⟩
  · simp [piNIdele, ← map_mul, ← coe_star_ringOfIntegers, piN_mul_star]
  · have h_val : Valued.v (D.piNIdele.val w) = w.intValuation D.piN :=
      v_algebraMap_eq_intValuation _
    rw [h_val]
    split_ifs with hw
    · exact D.intValuation_piN (by simpa [piNPlaces] using hw)
    · simpa [piNPlaces] using hw

/-- For index j, the finite idele (a/ā) raised to ⌈(m−j)/2⌉, exponent zero for j ≥ m, where a is
the idele `New.Data.ideleA`. -/
def latticeScale : unitary (𝔸f D.E) := divStar D.ideleA ^ ((D.m - j + 1) / 2)

/-- For j < m, a bijection from the indices of X_j plus 2ϱ + 1 − j string indices to those of Y_j:
`New.Shape.besselIndexEquiv` for j = 0, an arbitrary one (the two sides have the same number of
elements) otherwise. -/
def indexEquivY : ∀ j < D.m, D.X j ⊕ Fin (2 * D.ϱ + 1 - j) ≃ D.Y j
  | 0, _ => D.shape.besselIndexEquiv
  | _ + 1, _ =>
    Fintype.equivOfCardEq <| by
      simp
      grind [n]

/-- There is a hermitian space with the signs of `Y_j` that is standard for `D.m ≤ j` and that, for
`j < D.m`, has the Gram matrix `gradedGram` (identity on `X_j`, antidiagonal on the string) and, up
to an integral change of basis that is trivial at the chosen places, the lattice basis
`gradedLatticeBasis`. The lattice basis of `V` is the finite part `V.xFin` of its point. -/
lemma exists_space_isStd_of_le_and_gram_eq_of_lt :
    ∃ V : Space D.E (D.Y j) (D.signsY j),
      -- (a) for `D.m ≤ j` the space is standard
      (D.m ≤ j → V.IsStd) ∧
      ∀ hj : j < D.m,
        -- (b) for `j < D.m` its Gram matrix is `gradedGram`
        V.J = gradedGram (D.indexEquivY j hj) (D.N : D.E) ∧
        -- (c) and its lattice basis is `gradedLatticeBasis` times an integral `k` that reduces
        -- to `1` at the chosen places
        ∃ k : intGL (D.Y j) (Ô D.E),
          (∀ x : Σ i : Fin 2, D.ChosenPlace i, intGL.map (reduceAt (D.chosenPlace x)) k = 1) ∧
          V.xFin.val =
            gradedLatticeBasis (D.indexEquivY j hj) D.ideleA D.piNIdele (D.latticeScale j) *
              (k : GL (D.Y j) (𝔸f D.E)).val := by
  by_cases! hj : D.m ≤ j
  · -- For `D.m ≤ j` all signs are `1` and the standard space does it.
    exact ⟨signedSpace D.E (D.signsY j), fun _ ↦ isStd_signedSpace (D.gridSigns_eq_one hj),
      fun h_lt ↦ absurd hj h_lt.not_ge⟩
  let J : Matrix (D.Y j) (D.Y j) D.E := gradedGram (D.indexEquivY j hj) (D.N : D.E)
  let L : Matrix (D.Y j) (D.Y j) (𝔸f D.E) :=
    gradedLatticeBasis (D.indexEquivY j hj) D.ideleA D.piNIdele (D.latticeScale j)
  -- The number of signs `-1` is half the length `2 * D.ϱ + 1 - j` of the string, rounded up; so at
  -- each infinite place there is a frame `y w` for `J` with the right signs.
  have h_frame (w : D.Φ) : ∃ y : GL (D.Y j) ℂ,
      y.val.conjTranspose * J.map (New.Φ w) * y.val = signMatrix (D.signsY j) := by
    have h_card : Exchange.negCount (D.signsY j) = (2 * D.ϱ + 1 - j + 1) / 2 :=
      (D.negCount_gridSigns false 0 j).trans (by grind)
    obtain ⟨y, hy, -⟩ :=
      exists_conjTranspose_mul_gradedGram_mul_eq_signMatrix (D.indexEquivY j hj) (New.Φ w)
        D.N_prime.pos h_card
    have hy_unit : IsUnit y :=
      isUnit_of_mul_isUnit_right (.of_mul_eq_one _ (by rw [hy, signMatrix_mul_self]))
    exact ⟨hy_unit.unit, hy⟩
  choose y hy using h_frame
  -- At the finite places, the lattice with basis `L` is unimodular, so has an orthonormal basis
  -- `L * l` with `l` integral.
  obtain ⟨l, hl, hl_orth⟩ : ∃ l ∈ intGL (D.Y j) (Ô D.E),
      l.val.conjTranspose * (L.conjTranspose * J.map (algebraMap D.E (𝔸f D.E)) * L) * l.val = 1 :=
    exists_orthonormal_Ô
      (isUnimodular_gradedLatticeBasis_gram _ D.isSplitSquarefree_piNIdele.algebraMap_eq_mul_star)
  have hL_unit : IsUnit L :=
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right (.of_mul_eq_one _ hl_orth))
  -- Correct `l` by an integral unitary `k` with the inverse reductions at the chosen places.
  obtain ⟨k, hk⟩ : ∃ k : stdLevel D.E (D.Y j),
      stdLevel.reduceFamily D.chosenPlace k = fun x ↦
        (intGL.map (reduceAt (D.chosenPlace x)) ⟨l, hl⟩)⁻¹ :=
    ⟨liftResidue _, reduceFamily_liftResidue _⟩
  let k' : intGL (D.Y j) (Ô D.E) := ⟨k.val.val, k.prop⟩
  let V : Space D.E (D.Y j) (D.signsY j) :=
    { J
      x := mkAdelicGL (y, hL_unit.unit * (l * k'.val))
      gram_point :=
        gram_mkAdelicGL hy (gram_mul_of_gram_eq rfl (gram_mul_of_gram_eq hl_orth k.val.prop)) }
  refine ⟨V, fun h_le ↦ absurd h_le hj.not_ge, fun _ ↦ ⟨rfl, ⟨l, hl⟩ * k', fun x ↦ ?_, by rfl⟩⟩
  have hk' : intGL.map (reduceAt (D.chosenPlace x)) k' =
      (intGL.map (reduceAt (D.chosenPlace x)) ⟨l, hl⟩)⁻¹ :=
    congrFun hk x
  rw [map_mul, hk', mul_inv_cancel]

/-- The hermitian space `Y_j` with its lattice `𝖬_j`, chosen as in
`exists_space_isStd_of_le_and_gram_eq_of_lt`. Its properties are `isStd_spaceY_of_le`,
`spaceY_gram_eq` and `exists_spaceY_xFin_eq`. -/
def spaceY : Space D.E (D.Y j) (D.signsY j) :=
  (D.exists_space_isStd_of_le_and_gram_eq_of_lt j).choose

/-- For `D.m ≤ j` the space `Y_j` is standard: all its signs are `1` and its point is `1`. -/
lemma isStd_spaceY_of_le (hj : D.m ≤ j) : (D.spaceY j).IsStd :=
  (D.exists_space_isStd_of_le_and_gram_eq_of_lt j).choose_spec.left hj

/-- For `j < D.m` the Gram matrix of `Y_j` is `gradedGram`: the identity on `X_j` and antidiagonal
on a string of `2 ϱ + 1 - j` further vectors, with entries `1` except for `-N` at the middle vector
if there is one. -/
lemma spaceY_gram_eq (hj : j < D.m) :
    (D.spaceY j).J = gradedGram (D.indexEquivY j hj) (D.N : D.E) :=
  ((D.exists_space_isStd_of_le_and_gram_eq_of_lt j).choose_spec.right hj).left

/-- For `j < D.m` the lattice basis `xFin` of `Y_j` is `gradedLatticeBasis` times a matrix `k` in
`intGL`, invertible over the integral finite adeles `Ô`, whose reduction (`reduceAt`) at each chosen
place is `1`. -/
lemma exists_spaceY_xFin_eq (hj : j < D.m) :
    ∃ k : intGL (D.Y j) (Ô D.E),
      (∀ x : Σ i : Fin 2, D.ChosenPlace i, intGL.map (reduceAt (D.chosenPlace x)) k = 1) ∧
      (D.spaceY j).xFin.val =
        gradedLatticeBasis (D.indexEquivY j hj) D.ideleA D.piNIdele (D.latticeScale j) *
          (k : GL (D.Y j) (𝔸f D.E)).val :=
  ((D.exists_space_isStd_of_le_and_gram_eq_of_lt j).choose_spec.right hj).right

/-- The last space Y_m is standard: all its signs are +1 and its point is 1. -/
instance isStd_spaceY_last : (D.spaceY D.m).IsStd := D.isStd_spaceY_of_le D.m le_rfl

/-- For index j, the diagonal hermitian space W_j of rank r over E whose diagonal entries are the
signs `D.signsW j`. -/
abbrev spaceW : Space D.E D.RowIndex (D.signsW j) := signedSpace D.E (D.signsW j)

/-! ### Forms and descent pairs -/

/-- The forms on V of parameter ς (`New.Data.paramW` is 2ς) that are fixed by the principal level
`levelOf D.chosenPlace ⊥` at the chosen places above p₀, p₁. The character is the trivial one,
written as a composite with the reduction map of the level. -/
abbrev principalForms : Submodule ℂ (V.Form (typeKernel D.paramW s)) :=
  levelSpace (V.formRep (typeKernel D.paramW s)) (levelOf D.chosenPlace ⊥)
    (MonoidHom.comp 1 (levelOf.reduction D.chosenPlace ⊥))

/-- The complex representation of 𝖦 = ∏ GL_r(𝔽_w), over the chosen places w, on the forms on V of
principal level: an element acts through an integral lift with the given reductions. -/
def principalRep : Representation ℂ D.chosenGL (D.principalForms V) :=
  levelRep (V.formRep (typeKernel D.paramW s)) 1 (MonoidHom.id D.chosenGL) (by simp)

/-- The good forms on V: the image of the idempotent e₀ of ℂ[𝖦] acting on forms of principal
level at the chosen places above p₀, p₁. -/
def goodForms : Submodule ℂ (D.principalForms V) :=
  ((D.principalRep V).asAlgebraHom D.e₀).range

/-- The target forms: the good forms (`New.Data.goodForms`) on the space Y₀. -/
abbrev targetForms : Submodule ℂ (D.principalForms (D.spaceY 0)) := D.goodForms (D.spaceY 0)

/-- The complex dimension of the space of target forms (`New.Data.targetForms`), the good forms on
Y₀. -/
abbrev targetDim : ℕ := Module.finrank ℂ D.targetForms

/-- The j-th descent pair (`New.DescentPair`) for ϑ: W = W_j of rank r, V = I_{r+t}, the character
μ_j⁰ϑ of weight −w_j, and the places `New.Data.levelPlaces`. The basis vectors of sign + are
numbered by `New.Data.basisNumber`, those of sign − in the reverse order. Let ς_τ denote the target
parameter `New.Data.targetParameter`. The column count `colsPlus` at height i (the bound variable
`gap` below) is the positive part of ς_τ(i − 1) − max(ς_τ(i), (t − 1)/2 − w_j(τ)) − 1. The column
count `colsMinus` at height i is the positive part of
min(ς_τ(r − i − 1), −w_j(τ) − (t − 1)/2) − ς_τ(r − i) − 1. -/
def descentPair : DescentPair D.E D.RowIndex (D.RowIndex ⊕ Fin D.t) where
  toLevelPlaces := D.levelPlaces ϑ
  signs := D.signsW j
  W := D.spaceW j
  incl := Function.Embedding.inl
  numbering c := if D.signsW j c = 1 then D.basisNumber c else D.r - 1 - D.basisNumber c
  colsPlus τ gap := (D.targetParameter τ (gap - 1) - D.targetParameter τ gap ⊔
    (D.t / 2 - D.liftWeight j τ) - 1).toNat
  colsMinus τ gap :=
      (D.targetParameter τ (D.r - gap - 1) ⊓ (-D.liftWeight j τ - D.t / 2) - D.targetParameter τ
        (D.r - gap) - 1).toNat
  u1Char := D.liftChar ϑ j
  weight := (-D.liftWeight j ·)
  tamePart := D.liftTamePart ϑ j
  hasWeight := D.hasWeight_liftChar
  -- Off the chosen places and `ϑ.Q` both factors of `D.liftTamePart ϑ j w` are trivial.
  tame_eq_one := by simp_all [liftTamePart, levelPlaces, ϑ.tamePart_eq_one, range_chosenPlace]
  rank_lt := by simp [D.t_odd.pos]

end New.Data

namespace New.Data

/-!
## Levels and Weil representation data along the chain of spaces

* `New.Data.levelY`: the integral points of `U(Y_j)` that reduce to 1 at all level places
  `New.Data.levelPlaces` (the chosen places above p₀p₁ and those of Q).
* `New.Data.LevelReductionsY`: the group of families of reductions at the level places.
* `New.Data.pointDatumY`: the datum named by the indicator of the inclusion `Y_j → Y_{j+1}` modulo
  the level places `New.Data.levelPlaces`.
-/

section ChainData

open stdLevel

variable {P : Parameters} {D : Data P} (ϑ : D.TameChar) (j : ℕ)

/-- The inclusion of the basis index set of Y_j in that of Y_{j+1} as the first summand. -/
abbrev inclY : D.Y j ↪ D.Y (j + 1) := Function.Embedding.inl

/-- At a place w of the modulus Q of ϑ the character `D.liftTamePart ϑ j w` = ω_w^j ψ_w equals the
tame part ψ_w = `ϑ.tamePart w` of ϑ, since w is not chosen and ω = `D.chiMLocal` is trivial at such
places. -/
lemma liftTamePart_eq_of_mem_Q (w : ϑ.Q) : D.liftTamePart ϑ j w = ϑ.tamePart w := by
  simp [liftTamePart, IsChosen, (D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl w.prop)).right.left]

/-- The subgroup of the lattice stabiliser K₀ for Y_j of elements reducing to 1 at every level
place: the chosen places and the places of the modulus Q of ϑ. -/
abbrev levelY : Subgroup (Gf D.E (D.Y j)) := levelOf (n := D.Y j) (D.levelPlaces ϑ).placeAt ⊥

/-- The group `levelY ϑ j` is contained in `D.chosenLevel`, that is, its elements reduce to 1 at the
chosen places. -/
lemma levelY_le_chosenLevel : levelY ϑ j ≤ D.chosenLevel :=
  Subgroup.map_mono fun _ hk ↦ funext fun i ↦ congrFun hk (.inl i)

/-- The group ∏_w GL(Y_j mod w) of families of invertible matrices indexed by the basis of Y_j, one
over the residue field of each level place w: the chosen places (the left summand of the index set)
and the places of the modulus Q of ϑ (the right summand). The reductions of an integral point of
U(Y_j) at the level places form such a family. -/
abbrev LevelReductionsY : Type :=
  ∀ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
    GL (D.Y j) (ResField ((D.levelPlaces ϑ).placeAt x))

/-- The datum `Υ_{j+1}` on `Hom(Y_j, Y_{j+1})`: at the level places (the chosen places and those of
`ϑ.Q`) it is the indicator function of the inclusion matrix modulo their product, and at the other
finite places it is the vacuum (`New.vacuumDatum`). -/
def pointDatumY : ((D.spaceY j).hom (D.spaceY (j + 1))).finitePart :=
  delta% vacuumDatum (D.spaceY j) (D.spaceY (j + 1)) (D.twistModulus ϑ 1)
    (Pi.single (inclMatrix (D.twistModulus ϑ 1).ResidueRing (D.inclY j)) 1)

/-- The Weil representation of U(Y_j) × U(Y_{j+1}) on data on Hom(Y_j, Y_{j+1}), with splitting
characters νυ^⌊n/2⌋ for the two ranks n, ν = μ⁰_{j+1}ϑ^{j+1}. -/
abbrev thetaKernelY :
    ThetaKernel (𝒮 ((D.spaceY j).hom (D.spaceY (j + 1)))) (D.spaceY j) (D.spaceY (j + 1)) :=
  pairThetaKer (D.spaceY j) (D.spaceY (j + 1)) (rankTwist (D.chainChar ϑ (j + 1)) (D.Y j))
    (rankTwist (D.chainChar ϑ (j + 1)) (D.Y (j + 1)))

/-- The tame part of the character μ⁰_{j+1}ϑ^{j+1} of lift j + 1, a family of characters of the
residue fields. -/
abbrev chainTamePart : (w : New.FinPlace D.E) → MulChar (ResField w) ℂ :=
  D.liftTamePart (TameChar.pow ϑ (j + 1)) (j + 1)

/-- Let `k`, `k'` be integral finite points of `U(Y_j)`, `U(Y_{j+1})` with reductions `g`, `g'` at
the level places. Assume `g' ι = ι g` at each of them, where `ι = inclMatrix _ (D.inclY j)` is the
matrix of the inclusion `Y_j → Y_{j+1}`, so that `g' ι` is the submatrix of the columns of `g'`
indexed by `Y_j`. Then in the Weil representation `New.Data.thetaKernelY` the pair `(k, k')`
multiplies the datum `New.Data.pointDatumY` by the product over the level places of
`ψ (det g') / ψ (det g)`, for `ψ` the tame character `New.Data.chainTamePart`. -/
lemma thetaKernelY_omega_pointDatumY_eq_smul {k : stdLevel D.E (D.Y j)}
    {k' : stdLevel D.E (D.Y (j + 1))} {g : LevelReductionsY ϑ j} {g' : LevelReductionsY ϑ (j + 1)}
    (hk : reduceFamily (D.levelPlaces ϑ).placeAt k = g)
    (hk' : reduceFamily (D.levelPlaces ϑ).placeAt k' = g')
    (h_incl : ∀ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
      (g' x).val.submatrix id (D.inclY j) =
        inclMatrix (ResField ((D.levelPlaces ϑ).placeAt x)) (D.inclY j) * (g x).val) :
    (thetaKernelY ϑ j).ω ((1, k), 1, k') (pointDatumY ϑ j) =
      (∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
          chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x) (g' x).val.det /
            chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x) (g x).val.det) •
        pointDatumY ϑ j := by
  subst hk hk'
  let 𝔪 : Modulus D.E := D.twistModulus ϑ 1
  -- `(k, k')` fixes the inclusion matrix modulo `𝔪`: check it at each place.
  have h_fixes :
      inclMatrix 𝔪.ResidueRing (D.inclY j) =
        (𝔪.reductionGL k')⁻¹.val * inclMatrix 𝔪.ResidueRing (D.inclY j) *
          (𝔪.reductionGL k).val := by
    refine (Modulus.matrix_eq_iff_map_modulusResidue_eq (𝔪 := D.twistModulus ϑ 1)
      (D.levelPlaces ϑ).apart.injective (D.levelPlaces ϑ).ideal_levelModulus_one).2 fun x ↦ ?_
    let w : New.FinPlace D.E := (D.levelPlaces ϑ).placeAt x
    have h_comm :
        inclMatrix (ResField w) (D.inclY j) * (stdLevel.reduceAt w k).val =
          (stdLevel.reduceAt w k').val * inclMatrix (ResField w) (D.inclY j) := by
      rw [mul_inclMatrix]
      exact (h_incl x).symm
    have h_place : inclMatrix (ResField w) (D.inclY j) = (stdLevel.reduceAt w k'⁻¹).val *
        (inclMatrix (ResField w) (D.inclY j) * (stdLevel.reduceAt w k).val) := by
      simp [h_comm]
    simpa [𝔪, ← map_inv, map_inclMatrix, Matrix.mul_assoc] using h_place
  have h_datum :
      (pointDatumY ϑ j : 𝒮 ((D.spaceY j).hom (D.spaceY (j + 1)))) =
        modDatum (D.spaceY j) (D.spaceY (j + 1)) 𝔪
          (Pi.single (inclMatrix 𝔪.ResidueRing (D.inclY j)) 1) Fock.vacVector :=
    (modDatum_vacVector (D.spaceY j) (D.spaceY (j + 1)) _).symm
  -- The tame part of the character is trivial away from the level places, so on integral points
  -- the character of the determinant is the product of the tame parts at the level places.
  have h_tame : ∀ u ∉ Set.range (D.levelPlaces ϑ).placeAt, chainTamePart ϑ j u = 1 :=
    (D.descentPair (TameChar.pow ϑ (j + 1)) (j + 1)).tame_eq_one
  have h_char :
      pairChar (rankTwist (D.chainChar ϑ (j + 1)) (D.Y j))
          (rankTwist (D.chainChar ϑ (j + 1)) (D.Y (j + 1)))
          (((1, k.val), 1, k'.val) : New.G D.E (D.signsY j) × New.G D.E (D.signsY (j + 1))) =
        ∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
          chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x)
              (reduceFamily (D.levelPlaces ϑ).placeAt k' x).val.det /
            chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x)
              (reduceFamily (D.levelPlaces ϑ).placeAt k x).val.det := by
    rw [Finset.prod_div_distrib]
    simp [D.hasWeight_liftChar.hasWeight_rankTwist.apply_det_eq_prod
      (D.levelPlaces ϑ).apart.injective h_tame, reduceFamily, chainTamePart, div_eq_mul_inv]
  rw [← h_char, h_datum]
  exact Exchange.pairWeil_modDatum_single k k' h_fixes

end ChainData

/-!
## Gaps of the target parameter and finiteness of spaces of forms

* `New.Data.hasGap_signsY_paramW`, `New.Data.hasGap_paramW`: for the signs of Y₀ and of W_j, entries
  of ς at indices of opposite sign differ by at least h (`New.HCParam.HasGap`).
-/

section RowKernel

variable {P : Parameters} (D : Data P) (j : ℕ) (v : D.Φ)

instance : (D.spaceW D.m).IsStd :=
  -- `D.posRank D.m = D.r`, so that every index has the sign `+1`
  isStd_signedSpace (funext fun i ↦ by simp [signsW, ← r_add_one])

grind_pattern targetParameter_add_liftWeight_gap => D.targetParameter τ p, D.liftWeight j τ

/-- At each infinite place, the doubled target parameter 2ς is a parameter of gap h for the signs
`New.Data.signsY` of Y₀. -/
instance hasGap_signsY_paramW :
    (toHCParam (n := D.RowIndex) (D.signsY 0) (D.paramW v)).HasGap D.gap :=
  D.hasGap_gridParam v false 0 0 0

/-- At each infinite place, the doubled target parameter 2ς is a parameter of gap h for the signs
`New.Data.signsW` of W_j. -/
instance hasGap_paramW : (toHCParam (D.signsW j) (D.paramW v)).HasGap D.gap :=
  { D.hasGap_signsY_paramW v with
    gap := by
      -- Entries of `targetParameter` at indices of opposite sign lie on either side of `-w_j`, at
      -- least `D.halfGap` from it.
      have h_far (p : ℕ) :
          if p < D.posRank j then D.halfGap ≤ D.targetParameter v p + D.liftWeight j v
          else D.targetParameter v p + D.liftWeight j v ≤ -D.halfGap :=
        D.targetParameter_add_liftWeight_gap j v p
      grind [paramW, signsW] }

variable {s : D.RowIndex → ℤˣ}

/-- If at each infinite place `v` the doubled parameter `D.paramW v` (twice the target parameter)
has gap `D.gap` for the signs `s`, then the product kernel `typeKernel D.paramW s` is a cusp kernel
of order `D.halfGap`, half the gap. -/
theorem isCuspKernel_typeKernel_paramW [hs : ∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap] :
    IsCuspKernel D.halfGap (typeKernel D.paramW s) := by
  -- `isCuspKernel_typeKernel` asks for the gap `500 r³ + halfGap`, and `500 r³ ≤ halfGap`.
  have h_size : 500 * D.r ^ 3 ≤ D.halfGap := D.nat_le_of_hasLogBound
  refine isCuspKernel_typeKernel fun v ↦ (hs v).mono ?_
  rw [gapThreshold, card_rowIndex, gap]
  omega

variable [∀ v : D.Φ, (toHCParam s (D.paramW v)).HasGap D.gap] in
/-- If at each infinite place 2ς is a parameter of gap h for the signs s of V, the forms on V of
parameter ς and principal level at the chosen places make up a finite-dimensional space. -/
instance {V : Space D.E D.RowIndex s} : Module.Finite ℂ (D.principalForms V) :=
  V.finite_levelSpace D.isCuspKernel_typeKernel_paramW ⟨levelOf D.chosenPlace ⊥, isOpen_levelOf⟩

end RowKernel

/-!
## Harish-Chandra parameters on the seesaw spaces and descent pairs

* `New.Data.isHCParam_paramY`: the parameters on Y_m are those of the weight of the algebraic forms
  on this space.

Parameters are doubled so as to be integers.
-/

section Parameters

open Finset Nat Fintype Exchange

variable {P : Parameters} (D : Data P)

attribute [-grind] m_even

/-- For `j ≤ m` the rank of `Y_j` is at most `n_m = k + m (t + 1)`. -/
lemma card_Y_le {j : ℕ} (hj : j ≤ D.m) : Fintype.card (D.Y j) ≤ D.n D.m := by
  have h_card : Fintype.card (D.Y j) = D.r + j * D.t := by simp [← D.card_rowIndex]
  grind [n, D.r_add_one, Nat.mul_le_mul_right D.t hj]

/-- The doubled parameter `D.paramY D.m` of `Y_m` lists, in some order, the entries of twice the
Harish-Chandra parameter λ + ρ of the weight λ with column numbers `D.columnsY` and determinant
exponent `D.lastEntry D.m`. -/
lemma isHCParam_paramY : IsHCParam D.columnsY (D.lastEntry D.m) (D.paramY D.m) := by
  intro τ
  -- The decreasing list `sortedParamY` is twice the Harish-Chandra parameter of the weight.
  have h_sorted (p : ℕ) (hp : p < D.n D.m - 1) :
      D.sortedParamY τ p = hcParameter D.columnsY (D.lastEntry D.m) (D.n D.m - 1) τ p := by
    have h_weight : 2 * D.weightY τ p = D.sortedParamY τ p - twiceBlockEntry (D.n D.m - 1) p :=
      D.two_mul_weightY τ
    rw [D.weightY_eq τ hp, twiceBlockEntry] at h_weight
    rw [hcParameter, diagramWeight_apply]
    linarith
  -- It remains to find every entry of the parameter in the decreasing list.
  suffices h_occurs : ∀ i : D.Y D.m, ∃ p < D.n D.m - 1, D.paramY D.m τ i = D.sortedParamY τ p by
    refine ⟨(D.hasGap_gridParam τ false 0 0 D.m).injective, fun i ↦ ?_⟩
    obtain ⟨p, hp, h_eq⟩ := h_occurs i
    rw [card_Y_m]
    exact ⟨p, hp, h_eq.trans (h_sorted p hp)⟩
  have h_rank (l : ℕ) (hl : l < D.m) : D.n l + (D.t + 1) ≤ D.n D.m :=
    (D.n_succ l).ge.trans (D.n_mono hl)
  have h_even : D.m % 2 = 0 := even_iff.1 D.m_even -- nothing is lowered
  refine (D.gridBlockEquiv (z := false) (i := 0)).forall_congr_left.2 ?_
  rintro ((⟨y, hy⟩ | ⟨⟨-, ⟨⟩⟩, -⟩) | ⟨l, b⟩)
  · -- The entry `y` of the target parameter; the summand indexed by `Fin 0` is empty.
    suffices h_row : ∃ p < D.n D.m - 1, 2 * D.targetParameter τ y = D.sortedParamY τ p by
      simpa [paramY, gridParam, h_even] using h_row
    by_cases h_head : y + 1 < D.k
    · -- An entry of `[k - 1]` keeps its position.
      exact ⟨y, by grind [D.k_le_n D.m], (ite_eq_left h_head).symm⟩
    · -- The entry `halfGap - w_{i + 1}` of the target parameter stands just above block `i + 1`.
      obtain ⟨i, rfl⟩ : ∃ i : ℕ, y = D.k - 1 + i := Nat.exists_eq_add_of_le (by omega)
      have hi : i < D.m := by grind [D.r_add_one]
      exact ⟨D.n i - 1, by grind [D.n_pos i, h_rank i hi], (D.sortedParamY_n_sub_one i τ).symm⟩
  · -- Entry `b` of block `l + 1`.
    refine ⟨D.n l + b, by grind [h_rank l l.isLt], ?_⟩
    have h_entry : D.paramY D.m τ ((D.gridBlockEquiv (z := false) (i := 0) (j := D.m)).symm
        (.inr ⟨l, b⟩)) = twiceBlockEntry D.t b - 2 * D.liftWeight (l + 1) τ := by
      simp [paramY, gridParam, h_even, twiceBlockEntry]
      ring
    rw [h_entry, D.sortedParamY_block l τ b.isLt]

lemma card_rowIndex_sum_fin : Fintype.card (D.RowIndex ⊕ Fin D.t) = D.r + D.t := by
  rw [Fintype.card_sum, card_rowIndex, Fintype.card_fin]

/-- If q singles out the basis indices whose number lies in [a, b), and b ≤ r, there are b − a of
them (natural subtraction). -/
lemma card_filter_basisNumber {q : D.RowIndex → Prop} [DecidablePred q] (a b : ℕ)
    (hq : ∀ x : D.RowIndex, q x ↔ ↑(D.basisNumber x) ∈ Ico a b) (hb : b ≤ D.r) :
    #{x : D.RowIndex | q x} = b - a := by
  -- The numbering `D.basisNumber` matches the set with the interval `Ico a b` inside `Fin D.r`.
  have h_lt : ∀ p ∈ Ico a b, p < D.r := fun p hp ↦ (mem_Ico.1 hp).right.trans_le hb
  calc #{x : D.RowIndex | q x}
    _ = #((Ico a b).attachFin h_lt) := card_equiv D.basisNumber (by simp [hq])
    _ = b - a := by rw [card_attachFin, card_Ico]

/-- At `τ`, the doubled parameter 2ς = `D.paramW τ` is strictly decreasing in the basis number:
`D.paramW τ a < D.paramW τ b` exactly when `D.basisNumber b < D.basisNumber a`. -/
lemma paramW_lt_iff (τ : D.Φ) {a b : D.RowIndex} :
    D.paramW τ a < D.paramW τ b ↔ D.basisNumber b < D.basisNumber a := by
  simp [paramW, (D.targetParameter_strictAnti τ).lt_iff_gt]

/-- For 1 ≤ j ≤ m, the space W_j has exactly m − j minus signs. -/
lemma negCount_signsW (j : D.LiftIndex) : negCount (D.signsW j) = D.m - j := by
  have h_neg (x : D.RowIndex) :
      D.signsW j x = -1 ↔ (D.basisNumber x : ℕ) ∈ Ico (D.posRank j) D.r := by
    simp [signsW]
  have h_rank : D.r + 1 = D.k + D.m := D.r_add_one
  have h_j : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ D.m := j.prop
  rw [negCount, Fintype.card_subtype, D.card_filter_basisNumber _ _ h_neg le_rfl, posRank]
  omega

/-- Let `ϑ` be a tame character, `τ` an infinite place and `1 ≤ j ≤ m`. The weight at `τ` of the
forms on the space `V_j` of the `j`-th descent pair, of rank `r + t = card (D.RowIndex ⊕ Fin D.t)`,
has `columnCount τ i = colsPlus τ i + colsMinus τ (r + t - i)` columns of height `i`. The number of
columns of height `i` with `D.posRank j < i < r + t`, where `D.posRank j = k + j - 1` is the number
of plus signs of `W_j`, is the sum of `colsMinus τ i` over `1 ≤ i < r + t`. -/
lemma sum_Ioo_posRank_columnCount_descentPair (ϑ : D.TameChar) (τ : D.Φ) (j : D.LiftIndex) :
    ∑ i ∈ Ioo (D.posRank j) (card (D.RowIndex ⊕ Fin D.t)), (D.descentPair ϑ j).columnCount τ i =
      ∑ i ∈ Ico 1 (card (D.RowIndex ⊕ Fin D.t)), (D.descentPair ϑ j).colsMinus τ i := by
  have h_card : card (D.RowIndex ⊕ Fin D.t) = D.r + D.t := D.card_rowIndex_sum_fin
  calc ∑ i ∈ Ioo (D.posRank j) (card (D.RowIndex ⊕ Fin D.t)), (D.descentPair ϑ j).columnCount τ i
    _ = ∑ i ∈ Ico 1 (card (D.RowIndex ⊕ Fin D.t)),
          (D.descentPair ϑ j).colsMinus τ (D.r + D.t - i) := by
      refine sum_subset_zero_on_sdiff (by grind) (fun i hi ↦ ?_) fun i hi ↦ ?_
      · -- For `i ≤ D.posRank j` the count `colsMinus` vanishes at height `r + t - i`.
        grind [descentPair]
      · -- For `D.posRank j < i` the count `colsPlus` vanishes at height `i`.
        grind [descentPair]
    _ = ∑ i ∈ Ico 1 (card (D.RowIndex ⊕ Fin D.t)), (D.descentPair ϑ j).colsMinus τ i := by
      rw [sum_Ico_reflect ((D.descentPair ϑ j).colsMinus τ) 1 h_card.le.step, h_card]
      simp

/-- Let `ϑ` be a tame character, `τ` an infinite place, `j` a lift index and `p < r + t`. At `τ`,
entry `p` of twice the Harish-Chandra parameter (`hcParameter`) of the weight of forms on
`V = I_{r+t}` of the `j`-th descent pair `D.descentPair ϑ j` is `r - 2 a + 2 ℓ`. With
`a = D.posRank j`, `ς = D.targetParameter τ` and `w = D.liftWeight j τ`:
* `ℓ = ς_p + w` for `p < a`;
* `ℓ = ⌊t / 2⌋ - (p - a)` for `a ≤ p < a + t`;
* `ℓ = ς_{p - t} + w` for `a + t ≤ p`. -/
lemma hcParameter_descentPair (ϑ : D.TameChar) (τ : D.Φ) (j : D.LiftIndex) {p : ℕ}
    (hp : p < card (D.RowIndex ⊕ Fin D.t)) :
    hcParameter (D.descentPair ϑ j).columnCount (D.descentPair ϑ j).detExp
      (card (D.RowIndex ⊕ Fin D.t)) τ p =
      D.r - 2 * D.posRank j +
        2 * (if p < D.posRank j then D.targetParameter τ p + D.liftWeight j τ
          else if p < D.posRank j + D.t then D.t / 2 - (p - D.posRank j)
          else D.targetParameter τ (p - D.t) + D.liftWeight j τ : ℤ) := by
  have h_card : card (D.RowIndex ⊕ Fin D.t) = D.r + D.t := D.card_rowIndex_sum_fin
  let a : ℕ := D.posRank j
  let ℓ (p : ℕ) : ℤ :=
    if p < a then D.targetParameter τ p + D.liftWeight j τ
    else if p < a + D.t then D.t / 2 - (p - a)
    else D.targetParameter τ (p - D.t) + D.liftWeight j τ
  let L (p : ℕ) : ℤ := D.r - 2 * a + 2 * ℓ p
  have ha : a < card (D.RowIndex ⊕ Fin D.t) := by grind [j.prop, D.t_odd.pos, D.r_add_one]
  -- The columns of `descentPair` are defined as the steps of the list `L`.
  have h_step (p : ℕ) (hp : p + 1 < card (D.RowIndex ⊕ Fin D.t)) :
      L p = L (p + 1) + 2 * (D.descentPair ϑ j).columnCount τ (p + 1) + 2 := by
    -- Entries `ς_q + w` are at least `halfGap` for `q < a` and at most `-halfGap` otherwise, and
    -- `t / 2 < halfGap`. This decides each maximum, minimum and positive part in the column counts.
    have h_far (q : ℕ) : if q < a then D.halfGap ≤ D.targetParameter τ q + D.liftWeight j τ
        else D.targetParameter τ q + D.liftWeight j τ ≤ -D.halfGap :=
      D.targetParameter_add_liftWeight_gap j τ q
    have h_gap : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
    have h_columnCount : (D.descentPair ϑ j).columnCount τ (p + 1) =
        (D.descentPair ϑ j).colsPlus τ (p + 1) +
          (D.descentPair ϑ j).colsMinus τ (D.r + D.t - (p + 1)) := by
      grind
    rw [h_columnCount]
    by_cases h_above : p < a
    · -- Only `colsPlus` counts: the step from `ς_p + w` to `ς_{p+1} + w` or to the string.
      have h_anti : D.targetParameter τ (p + 1) < D.targetParameter τ p :=
        D.targetParameter_strictAnti τ p.lt_add_one
      have h_minus : (D.descentPair ϑ j).colsMinus τ (D.r + D.t - (p + 1)) = 0 := by
        grind [descentPair]
      rw [h_minus]
      grind [descentPair]
    have h_plus : (D.descentPair ϑ j).colsPlus τ (p + 1) = 0 := by grind [descentPair]
    rw [h_plus]
    -- Only `colsMinus` counts: inside the string there are no columns, and below it the step is to
    -- `ς_{p+1-t} + w` from the string or `ς_{p-t} + w`.
    have h_anti : D.targetParameter τ (p - D.t + 1) < D.targetParameter τ (p - D.t) :=
      D.targetParameter_strictAnti τ (p - D.t).lt_add_one
    grind [descentPair]
  have h_agree : L a =
      hcParameter (D.descentPair ϑ j).columnCount (D.descentPair ϑ j).detExp
        (card (D.RowIndex ⊕ Fin D.t)) τ a := by
    -- The columns above height `a` cancel the exponent `detExp`.
    have h_odd : D.t % 2 = 1 := Nat.odd_iff.1 D.t_odd
    have hL : L a = D.r - 2 * a + 2 * (D.t / 2) := by
      simp [L, ℓ, D.t_odd.pos]
    rw [hL, hcParameter, diagramWeight_apply, sum_Ioo_posRank_columnCount_descentPair,
      DescentPair.detExp, h_card]
    omega
  exact hcParameter_eq_of_steps τ L h_step ha h_agree p hp

/-- The system of centres (`New.CentreSystem`) at τ for the j-th descent pair: its stem is the
doubled target parameter {2ς_p : p < r}, and its only centre is the down centre `.inr (j - 1)`, at
−w_j and with a block of length t. -/
def descentCentres (τ : D.Φ) (j : D.LiftIndex) : CentreSystem (ℕ ⊕ ℕ) :=
  { D.gridCentres τ false with centres := {.inr (j - 1)} }

/-- The value of the centre `.inr (j - 1)` of `D.descentCentres τ j` is `-D.liftWeight j τ`, minus
the weight at `τ` of the character of the `j`-th lift. -/
lemma descentCentres_centre (τ : D.Φ) (j : D.LiftIndex) :
    (D.descentCentres τ j).centre (.inr (j - 1)) = -D.liftWeight j τ := by
  simp [descentCentres, gridCentres, Nat.sub_add_cancel j.prop.1]

/-- When the block of the only centre of `New.Data.descentCentres` is present, every entry has the
sign +. -/
lemma sign_descentCentres (τ : D.Φ) (j : D.LiftIndex) (y : ℤ) :
    (D.descentCentres τ j).sign (insert (.inr (j - 1)) ∅) y = 1 := by
  simp [CentreSystem.sign, descentCentres]

/-- The doubled parameter `D.paramW τ` (2ς on W_j), with signs `D.signsW j` and read as a vector by
`toHCParam`, is a parameter of the centre system `D.descentCentres τ j` with no block (∅) and global
sign 1. Its entries are those of the stem {2ς_p : p < r}, and the sign is − exactly at the entries
below −2w_j, with w_j = `D.liftWeight j τ`. -/
lemma isParam_paramW (τ : D.Φ) (j : D.LiftIndex) :
    (D.descentCentres τ j).IsParam ∅ 1 (toHCParam (D.signsW j) (D.paramW τ)) := by
  have h_lowering : (D.descentCentres τ j).lowering ∅ = 0 := by simp [CentreSystem.lowering]
  refine ⟨?_, ?_, fun x ↦ ?_⟩
  · rw [card_rowIndex, CentreSystem.rank, Finset.sum_empty]
    exact (D.card_stem_gridCentres τ false).symm
  · rw [h_lowering]
    ext y
    simp [CentreSystem.entries, descentCentres, gridCentres, paramW,
      D.basisNumber.exists_congr_left, Fin.exists_iff]
  · have h_pos : 0 < D.halfGap := D.nat_le_of_hasLogBound
    have h_counts : (D.descentCentres τ j).CountsFor (.inr (j - 1)) (D.paramW τ x) ↔
        D.posRank j ≤ D.basisNumber x := by
      have h_far : if D.basisNumber x < D.posRank j then
            D.halfGap ≤ D.targetParameter τ (D.basisNumber x) + D.liftWeight j τ
          else D.targetParameter τ (D.basisNumber x) + D.liftWeight j τ ≤ -D.halfGap :=
        D.targetParameter_add_liftWeight_gap j τ (D.basisNumber x)
      rw [CentreSystem.CountsFor, descentCentres_centre,
        ite_eq_right (by simp [descentCentres, gridCentres]), paramW]
      split_ifs at h_far <;> omega
    rw [h_lowering, add_zero, one_mul, signsW,
      CentreSystem.sign_eq_ite_sign_insert (mem_singleton_self _) (notMem_empty _),
        sign_descentCentres]
    exact if_congr h_counts.symm rfl rfl

/-- For p < r + t: entry p of the doubled parameter `hcParameter` of `D.descentPair ϑ j` at τ, in
decreasing order, lowered by 2u − 1 for u = m − j + w_j − (r − 1)/2. With a = `D.posRank j` and
ς = `D.targetParameter τ`, the entries are: first 2ς_p for p < a, then the t entries
2(−w_j) + t − 1 − 2(p − a) (the doubled block of length t centred at −w_j), then 2ς_(p−t). -/
lemma hcParameter_descentPair_sub (ϑ : D.TameChar) (τ : D.Φ) (j : D.LiftIndex) {p : ℕ}
    (hp : p < D.r + D.t) :
    hcParameter (D.descentPair ϑ j).columnCount (D.descentPair ϑ j).detExp
      (card (D.RowIndex ⊕ Fin D.t)) τ p -
        2 * (D.m - j + D.liftWeight j τ - D.r / 2) + 1 =
      if p < D.posRank j then 2 * D.targetParameter τ p
      else if p < D.posRank j + D.t then
        2 * -(D.liftWeight j τ : ℤ) + D.t - 1 - 2 * (p - D.posRank j : ℕ)
      else 2 * D.targetParameter τ (p - D.t) := by
  rw [D.hcParameter_descentPair ϑ τ j (hp.trans_eq D.card_rowIndex_sum_fin.symm)]
  grind [D.r_add_one, D.r_odd, D.t_odd]

/-- Let ϑ be a tame character, τ an infinite place, 1 ≤ j ≤ m, w_j = `D.liftWeight j τ` and
u = m − j + w_j − ⌊r/2⌋. Let l = `paramV τ` − 2u, where `paramV τ` is twice the Harish-Chandra
parameter at τ on the positive definite space V_j of rank r + t of the j-th descent pair. The system
`New.Data.descentCentres` has the stem {2ς_p : p < r}, with ς = `D.targetParameter τ`, and one
centre, with index `.inr (j - 1)`, value −w_j and block {−2w_j + t − 1 − 2b : b < t}. Then l is the
parameter of this system with the block present and common sign 1: the ranks agree, the numbers l
x + 1 are the entries of the stem and of the block, and each of them has the sign +. -/
lemma isParam_paramV (ϑ : D.TameChar) (τ : D.Φ) (j : D.LiftIndex) :
    (D.descentCentres τ j).IsParam (insert (.inr (j - 1)) ∅) 1
      (toHCParam 1 fun x : D.RowIndex ⊕ Fin D.t ↦
        (D.descentPair ϑ j).paramV τ x - 2 * (D.m - j + D.liftWeight j τ - D.r / 2)) := by
  have h_stem : #(D.descentCentres τ j).stem = D.r := D.card_stem_gridCentres τ false
  have h_lowering : (D.descentCentres τ j).lowering (insert (.inr (j - 1)) ∅) = 1 := by
    simp [CentreSystem.lowering, h_stem, D.r_odd]
  refine ⟨?_, ?_, fun x ↦ by rw [sign_descentCentres, one_mul, Pi.one_apply]⟩
  · rw [card_rowIndex_sum_fin, CentreSystem.rank, h_stem]
    simp [descentCentres, gridCentres]
  · have h_posRank : D.posRank j ≤ D.r := by grind [j.prop, D.r_add_one]
    have h_card : card (D.RowIndex ⊕ Fin D.t) = D.r + D.t := D.card_rowIndex_sum_fin
    let shift (y : ℤ) : ℤ := y - 2 * (D.m - j + D.liftWeight j τ - D.r / 2) + 1
    have h_image : univ.image (shift ∘ (D.descentPair ϑ j).paramV τ) =
        (range (card (D.RowIndex ⊕ Fin D.t))).image
          (shift ∘ hcParameter (D.descentPair ϑ j).columnCount
          (D.descentPair ϑ j).detExp (card (D.RowIndex ⊕ Fin D.t)) τ) := by
      rw [← image_image, ← image_image, (D.descentPair ϑ j).isHCParam_paramV.image_eq τ]
    rw [h_lowering, CentreSystem.entries_insert, CentreSystem.block, descentCentres_centre]
    refine h_image.trans (Finset.ext fun y ↦ ?_)
    -- Unfold both sides to entries of the shifted parameter, of the stem and of the block.
    simp only [CentreSystem.entries, biUnion_empty, union_empty, descentCentres, gridCentres,
      mem_union, mem_image, Finset.mem_range, mem_centredBlock, Function.comp_apply, Sum.elim_inr,
      Bool.toNat_false, Nat.sub_zero, Nat.cast_zero, add_zero, shift]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [D.hcParameter_descentPair_sub ϑ τ j (hp.trans_eq h_card)]
      split_ifs
      · exact .inl ⟨p, by omega, rfl⟩
      · exact .inr ⟨p - D.posRank j, by omega, rfl⟩
      · exact .inl ⟨p - D.t, by omega, rfl⟩
    · rintro (⟨p, hp, rfl⟩ | ⟨b, hb, rfl⟩)
      · -- An entry of `ς` keeps its position above the block and moves down by `t` below it.
        by_cases h_above : p < D.posRank j
        · refine ⟨p, by omega, ?_⟩
          rw [D.hcParameter_descentPair_sub ϑ τ j (by omega), ite_eq_left h_above]
        · refine ⟨p + D.t, by omega, ?_⟩
          rw [D.hcParameter_descentPair_sub ϑ τ j (by omega)]
          grind
      · refine ⟨D.posRank j + b, by omega, ?_⟩
        rw [D.hcParameter_descentPair_sub ϑ τ j (by omega)]
        grind

/-- Let `ϑ` be a tame character and 1 ≤ j ≤ m. The doubled parameter 2ς = `D.paramW` on W_j (signs
`D.signsW j`) and the doubled parameter `paramV` of the j-th descent pair `D.descentPair ϑ j` on V_j
(all signs +) correspond: at every infinite place τ they satisfy the block rule `New.IsBlockRule`
for two weights. The first is the number `negCount (D.signsW j)` of minus signs of W_j, which is
m − j (`negCount_signsW`). The second is ⌊(r + t)/2⌋ − w_j(τ). -/
lemma paramsCorrespond_descentPair (ϑ : D.TameChar) (j : D.LiftIndex) :
    ParamsCorrespond (fun _ : D.Φ ↦ negCount (D.signsW j))
      (fun τ : D.Φ ↦ (card (D.RowIndex ⊕ Fin D.t) / 2 : ℕ) + -(D.liftWeight j τ : ℤ))
      D.paramW (D.descentPair ϑ j).paramV (D.signsW j) 1 := by
  intro τ
  obtain ⟨h_one_le, h_le⟩ : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ D.m := j.prop
  let u : ℤ := D.m - j + D.liftWeight j τ - D.r / 2
  have h_centre : Sum.inr (j - 1 : ℕ) ∈ (D.gridCentres τ false).centres := by
    simpa [gridCentres] using Nat.sub_one_lt_of_le h_one_le h_le
  have h_gap : 500 * (card D.RowIndex + card (D.RowIndex ⊕ Fin D.t)) ^ 3 ≤ D.gap - D.t - 2 := by
    have h_size : 500 * (D.r + (D.r + D.t)) ^ 3 + D.t + 2 ≤ D.gap := D.nat_le_of_hasLogBound
    grind [card_rowIndex_sum_fin, card_rowIndex]
  -- Insert the block of the centre `-w_j`, then raise the first weight by `u`.
  have h_rule : IsBlockRule (-D.liftWeight j τ + card D.RowIndex / 2)
      (-D.liftWeight j τ + card (D.RowIndex ⊕ Fin D.t) / 2) (toHCParam (D.signsW j) (D.paramW τ))
      (toHCParam 1 fun x : D.RowIndex ⊕ Fin D.t ↦ (D.descentPair ϑ j).paramV τ x - 2 * u) := by
    rw [← descentCentres_centre]
    exact (D.isParam_paramW τ j).isBlockRule_insert_of_down (D.isParam_paramV ϑ τ j) rfl
      ((D.isSeparated_gridCentres τ false).subset (singleton_subset_iff.2 h_centre))
      (empty_subset _) (mem_singleton_self _) (notMem_empty _) h_gap rfl
  have h_weight : (negCount (D.signsW j) : ℤ) = -D.liftWeight j τ + card D.RowIndex / 2 + u := by
    grind [negCount_signsW, card_rowIndex]
  rw [h_weight]
  simpa [add_comm] using h_rule.shift u 0

/-- The doubled parameter 2ς = `D.paramW` on W_j fits the j-th descent pair (W_j, V_j), that is:
* it corresponds to the doubled parameter `paramV` on V_j;
* at every infinite place, `numbering c` is the position, counted from 0, of the basis vector c of
  W_j among those of its sign, ordered by decreasing ς for the sign + and increasing ς for −;
* `colsPlus τ i` vanishes if i exceeds the number of basis vectors of sign +, and `colsMinus τ i`
  vanishes if i exceeds the number of basis vectors of sign −. -/
lemma fitsParams_descentPair (ϑ : D.TameChar) (j : D.LiftIndex) :
    (D.descentPair ϑ j).FitsParams D.paramW := by
  let a : ℕ := D.posRank j
  refine ⟨D.paramsCorrespond_descentPair ϑ j, fun τ c ↦ ?_, fun τ i hi ↦ ?_, fun τ i hi ↦ ?_⟩
  · -- As ς decreases, the vectors that precede c are those of its sign with a smaller number
    -- (sign 1) or a larger number (sign -1).
    dsimp [descentPair, signsW]
    split
    · have h_count :
          #{x : D.RowIndex | a ≤ D.basisNumber x ∧ D.basisNumber c < D.basisNumber x} =
            D.r - (D.basisNumber c + 1) :=
        D.card_filter_basisNumber _ _ (by grind) le_rfl
      simpa [a, paramW_lt_iff, tsub_tsub, add_comm] using h_count.symm
    · have h_count : #{x : D.RowIndex | D.basisNumber x < a ∧ D.basisNumber x < D.basisNumber c} =
          D.basisNumber c :=
        D.card_filter_basisNumber 0 _ (by grind) (D.basisNumber c).isLt.le
      simpa [a, paramW_lt_iff, lt_tsub_iff_right] using h_count.symm
  · -- There are `a` vectors of sign 1; above that height `ς_(i-1)` is at most `(t - 1) / 2 - w_j`.
    have h_card : Fintype.card {c : D.RowIndex // D.signsW j c = 1} = a := by
      grind [D.card_filter_basisNumber 0 a, signsW, units_ne_neg_self, Fintype.card_subtype]
    have h_above : a < i := h_card.symm.trans_lt hi
    simp only [descentPair, Int.toNat_eq_zero]
    grind
  · -- There are `m - j` vectors of sign -1; above that height `ς_(r-i)` is at least
    -- `-w_j - (t - 1) / 2`.
    have h_above : D.m - j < i := (D.negCount_signsW j).symm.trans_lt hi
    simp only [descentPair, Int.toNat_eq_zero]
    grind

end Parameters

end New.Data

end
