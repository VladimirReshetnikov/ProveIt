import New.UpperBound.Seesaw.EdgePairEvaluation

/-!
# The neighbour lattice of a pair of edges

Take definite spaces with bases indexed by `X ⊕ Unit`, `X'` and `X'' ⊕ Unit`, written `X`, `X'`,
`X''` for short, and let `e` and `e''` be the last basis vectors of the first and of the third. An
explicit unitary carries the standard lattice of `Hom (X', X⁻ ⊕ X'')` to `neighbourLattice`. Away
from `N` this lattice is the standard one with scaled rows. Above `N` it is a neighbour of the
standard lattice, and the translations `neighbourTranslation` represent it modulo its integral
points. The sums `neighbourCosetRep` of these and of scaled rows away from `N` represent the whole
lattice modulo its integral points.

Notions from other files:
* `𝔸f E` is the ring of finite adeles of the CM field `E` and `Ô E` its subring of integral adeles;
  `star` is complex conjugation and `idem S` is the adele that is `1` on `S` and `0` off it.
* `IsSplitLevel P N`: the places above the prime `N` are those in `P` and their conjugates, all
  split of degree one and unramified.
* `IsSplitSquarefree P N π`: the idele `π` is a uniformiser on `P` and a unit elsewhere,
  `N = π π̄`, and `P` does not meet its conjugate.
* `stdLattice E ι` consists of the vectors with integral entries, `integralBox ι S` of those whose
  entries are integral at the places of `S`; `S.conjClosure` is `S` with its conjugate places.
* `residueOverN y` is the adele `y / N` at `P`, for residues `y` modulo `N` at the places of `P`.
* `Gf E ι` is the group of unitary matrices over `𝔸f E` with rows and columns indexed by `ι`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

namespace New.Seesaw

noncomputable section

open Matrix Space WeilData Kronecker Exchange Finset Weil Valued stdLattice

section Denominators

open NumberField

variable {E n n₀ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {q : ℕ}

/-- The denominators allowed on `X⁻ ⊕ X''`: the integral adele `β` on the first block of indices
and its conjugate on the second. -/
def selfOrConj {ι κ : Type*} (β : Ô E) (j : ι ⊕ κ) : 𝔸f E :=
  if j.isLeft then (β : 𝔸f E) else star (β : 𝔸f E)

omit [IsCMField E] in
/-- A vector `x` lies in `weightedTranslations q d` if and only if, for each index `i` and each
finite place `w` not dividing `q`, the absolute values `v` at `w` of `d i` and `x i` have product at
most one. -/
lemma mem_weightedTranslations {ι : Type*} {d x : ι → 𝔸f E} :
    x ∈ weightedTranslations q d ↔
      ∀ (i : ι) (w : FinPlace E), ↑q ∉ w.asIdeal → v (d i w) * v (x i w) ≤ 1 := by
  simp [weightedTranslations]

/-- The group `weightedTranslations q d` consists of the vectors `y` with denominators `d` away from
`q`: for every index `i` and every place `w` not dividing `q` one has `v (d i w) * v (y i w) ≤ 1`.
The adjoint of an integral matrix `M` maps this group to the one for `d'`, provided that `M i j`
vanishes at the conjugate place `star w` whenever `d i` and `d' j` have different valuations at
`w`. -/
lemma conjTranspose_mulVec_mem_weightedTranslations {M : Matrix n n₀ (𝔸f E)}
    (hM_int : IsIntMatrix (Ô E) M) {d y : n → 𝔸f E} {d' : n₀ → 𝔸f E}
    (hy : y ∈ weightedTranslations q d) (hM_zero : ∀ (i : n) (j : n₀) (w : FinPlace E),
      v (d i w) ≠ v (d' j w) → M i j (star w) = 0) :
    Mᴴ *ᵥ y ∈ weightedTranslations q d' := by
  -- `Mᴴ y` is the sum over the rows `i` of the conjugate of row `i` times `y i`.
  have h_rows : Mᴴ *ᵥ y = ∑ i, fun j ↦ star (M i j) * y i :=
    funext fun j ↦ by simp [mulVec, dotProduct]
  rw [h_rows]
  refine sum_mem fun i _ ↦ mem_weightedTranslations.2 fun j w hw ↦ ?_
  by_cases h_val : v (d i w) = v (d' j w)
  · calc v (d' j w) * v ((star (M i j) * y i) w)
        = v (M i j (star w)) * (v (d i w) * v (y i w)) := by simp [h_val, mul_left_comm]
      _ ≤ 1 :=
        mul_le_one' (mem_Ô.1 (hM_int i j) (star w)) (mem_weightedTranslations.1 hy i w hw)
  · simp [hM_zero i j w h_val]

/-- If `x` lies in `weightedTranslations q d`, then `i ↦ c * star (x (f i))` lies in
`weightedTranslations q` for `i ↦ star (d (f i))`. Here `c` is integral (`hc`) and `f` is any change
of indices. -/
lemma star_mem_weightedTranslations {ι X : Type*} {c : 𝔸f E} (hc : c ∈ Ô E) {d x : ι → 𝔸f E}
    (hx : x ∈ weightedTranslations q d) (f : X → ι) :
    (fun i : X ↦ c * star (x (f i))) ∈ weightedTranslations q fun i : X ↦ star (d (f i)) := by
  refine mem_weightedTranslations.2 fun i w hw ↦ ?_
  calc v (star (d (f i)) w) * v ((c * star (x (f i))) w)
      = v (c w) * v ((d (f i) * x (f i)) (star w)) := by simp [mul_left_comm]
    _ ≤ 1 := mul_le_one' (mem_Ô.1 hc w) (hx (f i) (star w) (by simpa using hw))

end Denominators

/-- The basis indices of the sum `X⁻ ⊕ X''` of two definite spaces: those of the first space are
`X ⊕ Unit` and those of the second `X'' ⊕ Unit`, `Unit` indexing a last basis vector. -/
abbrev PairIndex (X X'' : Type) : Type := (X ⊕ Unit) ⊕ X'' ⊕ Unit

/-- The index of the last basis vector `e` of the first space. -/
abbrev PairIndex.lastSource {X X'' : Type} : PairIndex X X'' := Sum.inl (Sum.inr ())

/-- The index of the last basis vector `e''` of the second space. -/
abbrev PairIndex.lastTarget {X X'' : Type} : PairIndex X X'' := Sum.inr (Sum.inr ())

open PairIndex

section Neighbour

variable {E X X' X'' : Type} [Field E] [CMType E] [WeilData E]

/-- The gluing conditions on a vector `x` of `X⁻ ⊕ X''` and an adele `c`, which in the application
is the coefficient of an isotropic vector: `x` is integral except at `e` and `e''`, where it has
denominator at most `π̄`, and its entries there, divided by `π`, are congruent to `c` and `η̄ c`. -/
structure IsNeighbourVector (π : (𝔸f E)ˣ) (δ c : 𝔸f E) (x : PairIndex X X'' → 𝔸f E) : Prop where
  /-- The coefficient `c` is unchanged by `δ`. -/
  mul_coeff : δ * c = c
  /-- The entries other than those at `e` and `e''` are integral. -/
  mem_of_ne (i : PairIndex X X'') (h_source : i ≠ lastSource) (h_target : i ≠ lastTarget) :
    x i ∈ Ô E
  /-- All entries have denominator at most `π̄`. -/
  star_mul_mem (i : PairIndex X X'') : star (π : 𝔸f E) * x i ∈ Ô E
  /-- The entry at `e`, divided by `π`, differs from `c` by an integral adele. -/
  sub_source_mem : c - ↑π⁻¹ * x lastSource ∈ Ô E
  /-- The entry at `e''`, divided by `π`, differs from `η̄ c` by an integral adele, where `η` is the
  unit `normNegOne` of norm `-1`. -/
  sub_target_mem : star (normNegOne (E := E) : 𝔸f E) * c - ↑π⁻¹ * x lastTarget ∈ Ô E

/-- The factors `κ` by which the rows of the standard lattice are scaled at the places dividing
`β` and `β̄`: each is `1` or a fixed adele `δ` of norm one, and nothing happens above `N`. In the
application `β β̄` is the auxiliary level `M` and `δ` generates the ideal `(β / β̄)`. -/
structure IsScalingAtM (N : ℕ) (β : Ô E) (δ : 𝔸f E) (κ : PairIndex X X'' → 𝔸f E) : Prop where
  /-- `δ` has norm one. -/
  mul_star_self_eq_one : δ * star δ = 1
  /-- `δ` is `1` above `N`. -/
  apply_eq_one (w : FinPlace E) (hw : ↑N ∈ w.asIdeal) : δ w = 1
  /-- `β` is a unit above `N`. -/
  v_eq_one (w : FinPlace E) (hw : ↑N ∈ w.asIdeal) : v ((β : 𝔸f E) w) = 1
  /-- Each factor is `1` or `δ`. -/
  eq_one_or_eq (b : PairIndex X X'') : κ b = 1 ∨ κ b = δ
  /-- Each factor has denominator at most `β̄`. -/
  star_mul_mem (b : PairIndex X X'') : star (β : 𝔸f E) * κ b ∈ Ô E
  /-- The factors on `X⁻` have denominator at most `β`, those on `X''` at most `β̄`. -/
  selfOrConj_mul_mem (b : PairIndex X X'') : selfOrConj β b * κ b ∈ Ô E

variable [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X'']

variable (X X'') (P : Finset (FinPlace E)) (π : (𝔸f E)ˣ)

/-- The vector `ρ = e + η̄ j̄ e''`, where `j` is the idempotent of `P` and `η` the unit of norm
`-1`. It is `e` except at the places conjugate to `P`, where it is `e + η̄ e''`. It has norm one
when `P` is disjoint from its conjugate. -/
def neighbourAxis : PairIndex X X'' → 𝔸f E :=
  (0 ⊕ᵥ fun _ ↦ 1) ⊕ᵥ (0 ⊕ᵥ fun _ ↦ star ((normNegOne (E := E) : 𝔸f E) * idem P))

/-- The adele `A` such that, when `P` is disjoint from its conjugate, `1 + A` is `π` at `P`, `π̄⁻¹`
at the conjugate places and `1` elsewhere. -/
def neighbourScale : 𝔸f E :=
  idem P * ((π : 𝔸f E) - 1) + star (idem P) * (star (↑π⁻¹ : 𝔸f E) - 1)

/-- The matrix `γ = 1 + A ρ ρ*`. When `P` is disjoint from its conjugate, so that `ρ` has norm one,
it scales `ρ` by `1 + A` and fixes its orthogonal complement; its columns then span a neighbour at
`N` of the standard lattice. -/
def neighbourMatrix : Matrix (PairIndex X X'') (PairIndex X X'') (𝔸f E) :=
  1 + neighbourScale P π • vecMulVec (neighbourAxis X X'' P) (star (neighbourAxis X X'' P))

/-- The coefficient of the isotropic vector that goes with each column of `neighbourMatrix`; it is
zero except for the columns of `e` and `e''`. -/
def neighbourCoeff : PairIndex X X'' → 𝔸f E :=
  (0 ⊕ᵥ fun _ ↦ neighbourScale P π * (↑π⁻¹ : 𝔸f E) * star (idem P)) ⊕ᵥ
    (0 ⊕ᵥ fun _ ↦ neighbourScale P π * (↑π⁻¹ : 𝔸f E) * ((normNegOne (E := E) : 𝔸f E) * idem P))

/-- The translation `n y` attached to residues `y` at `P`: the matrix with row `η ȳ / N` at `e`,
row `-ȳ / N` at `e''` and zero elsewhere. It is supported at the places conjugate to `P`. -/
def neighbourTranslation {P : Finset (FinPlace E)} {N : ℕ} (y : X' → P → ZMod N)
    (i : PairIndex X X'' × X') : 𝔸f E :=
  Sum.elim (0 ⊕ᵥ fun _ ↦ (normNegOne (E := E) : 𝔸f E) * star (residueOverN (y i.2)))
    (0 ⊕ᵥ fun _ ↦ -star (residueOverN (y i.2))) i.1

end Neighbour

variable {E X X' X'' : Type} [Field E] [CMType E] [WeilData E] [Fintype X]
  [Fintype X'] [DecidableEq X'] [Fintype X''] {N : ℕ} {P : Finset (FinPlace E)}

section Unitary

variable {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E} {κ : PairIndex X X'' → 𝔸f E}

section Relations

omit [WeilData E] [Fintype X] [Fintype X'] [Fintype X'']

/-- The matrix that scales a unit vector `ρ` by a factor `1 + A` of norm one and fixes its
orthogonal complement is unitary. -/
lemma conjTranspose_mul_one_add_smul_vecMulVec {R n : Type*} [CommRing R] [StarRing R] [Fintype n]
    [DecidableEq n] {ρ : n → R} {A : R} (hρ : star ρ ⬝ᵥ ρ = 1) (hA : star (1 + A) * (1 + A) = 1) :
    (1 + A • vecMulVec ρ (star ρ))ᴴ * (1 + A • vecMulVec ρ (star ρ)) = 1 := by
  -- The projection `Q = ρ ρ*` is hermitian and idempotent.
  set Q : Matrix n n R := vecMulVec ρ (star ρ) with hQ
  have h_adj : Qᴴ = Q := by rw [hQ, conjTranspose_vecMulVec, star_star]
  have h_sq : Q * Q = Q := by rw [hQ, vecMulVec_mul_vecMulVec, hρ, one_smul]
  have h_sum : star A + A + star A * A = 0 := by grind [star_one]
  calc (1 + A • Q)ᴴ * (1 + A • Q)
    _ = 1 + (star A + A + star A * A) • Q := by
      simp [h_adj, add_mul, mul_add, smul_smul, h_sq, add_smul, add_assoc, mul_comm]
    _ = 1 := by simp [h_sum]

lemma IsSplitSquarefree.isConjDisjoint (hπ : IsSplitSquarefree P (N : E) π) :
    Set.IsConjDisjoint (P : Set (FinPlace E)) :=
  Set.disjoint_left.2 hπ.star_notMem

lemma IsSplitSquarefree.natCast_eq_mul_star (hπ : IsSplitSquarefree P (N : E) π) :
    (N : 𝔸f E) = π * star (π : 𝔸f E) := by
  simpa using hπ.algebraMap_eq_mul_star

lemma IsSplitSquarefree.mem_integralAdeles (hπ : IsSplitSquarefree P (N : E) π) :
    (π : 𝔸f E) ∈ Ô E := by
  refine mem_Ô.2 fun w ↦ ?_
  rw [hπ.v_apply]
  split_ifs
  exacts [(WithZero.exp_le_exp.2 (by simp)).trans_eq WithZero.exp_zero, le_rfl]

lemma IsSplitSquarefree.star_mem_integralAdeles (hπ : IsSplitSquarefree P (N : E) π) :
    star (π : 𝔸f E) ∈ Ô E :=
  star_mem_Ô hπ.mem_integralAdeles

/-- If `π` is a uniformiser on `P` and a unit elsewhere, then `π⁻¹` is integral off `P`. -/
lemma IsSplitSquarefree.one_sub_idem_mul_inv_mem (hπ : IsSplitSquarefree P (N : E) π) :
    (1 - idem P) * (↑π⁻¹ : 𝔸f E) ∈ Ô E := by
  rw [← idem_compl, idem_mul_mem_Ô]
  intro w (hw : w ∉ P)
  simp [idele_inv_apply_and_ne_zero, hπ.v_apply, hw]

lemma star_idem_mul_self (S : Set (FinPlace E)) :
    star (idem S) * star (idem S) = (star (idem S) : 𝔸f E) := by
  rw [← star_mul', idem_mul_self]

lemma star_mul_star_inv (π : (𝔸f E)ˣ) : star (π : 𝔸f E) * star (↑π⁻¹ : 𝔸f E) = 1 := by
  rw [← star_mul', π.mul_inv, star_one]

/-- Every scaling factor has norm one. -/
lemma IsScalingAtM.apply_mul_star_eq_one (hκ : IsScalingAtM N β δ κ) (i : PairIndex X X'') :
    κ i * star (κ i) = 1 := by
  rcases hκ.eq_one_or_eq i with h | h <;> simp [h, hκ.mul_star_self_eq_one]

/-- If the places above `N` are `P` and its conjugate, the scaling adele `δ`, which is `1` above
`N`, is `1` at `P`. -/
lemma IsScalingAtM.idem_mul [Fact N.Prime] (hκ : IsScalingAtM N β δ κ)
    (hP : IsSplitLevel P N) : idem P * δ = idem P := by
  ext w
  by_cases hw : w ∈ P <;> simp [hw, hκ.apply_eq_one, hP.natCast_mem_iff]

/-- If the places above `N` are `P` and its conjugate, the scaling adele `δ`, which is `1` above
`N`, is `1` at the places conjugate to `P`. -/
lemma IsScalingAtM.star_idem_mul [Fact N.Prime] (hκ : IsScalingAtM N β δ κ)
    (hP : IsSplitLevel P N) : star (idem P) * δ = star (idem P) := by
  rw [star_idem]
  ext w
  by_cases hw : star w ∈ P
  · simp [hκ.apply_eq_one w ((hP.natCast_mem_iff w).2 (Or.inr hw))]
  · simp [hw]

/-- Let `N = π π̄` with `π` a uniformiser on `P` and a unit elsewhere, and let `P` be disjoint from
its conjugate (`IsSplitSquarefree`). The adele `A = neighbourScale P π`, which is `π - 1` at `P`,
`π̄⁻¹ - 1` at the conjugate places and `0` elsewhere, has denominator at most `π̄`: the product
`π̄ A` is integral. -/
lemma star_mul_neighbourScale_mem (hπ : IsSplitSquarefree P (N : E) π) :
    star (π : 𝔸f E) * neighbourScale P π ∈ Ô E := by
  have h_eq : star (π : 𝔸f E) * neighbourScale P π =
      star (π : 𝔸f E) * (idem P * (π : 𝔸f E) - idem P - star (idem P)) + star (idem P) := by
    rw [neighbourScale]
    linear_combination star (idem P) * star_mul_star_inv π
  have hj : idem P ∈ Ô E := idem_mem_Ô _
  rw [h_eq]
  exact add_mem (mul_mem hπ.star_mem_integralAdeles
    (sub_mem (sub_mem (mul_mem hj hπ.mem_integralAdeles) hj) (star_mem_Ô hj))) (star_mem_Ô hj)

/-- The adele `neighbourScale P π` vanishes at each place outside `P` and its conjugate. -/
lemma neighbourScale_apply_of_notMem {w : FinPlace E} (hw : w ∉ P) (hw_star : star w ∉ P) :
    evalAt w (neighbourScale P π) = 0 := by
  simp [neighbourScale, star_idem, hw, hw_star]

end Relations

section Entries

omit [Fintype X] [Fintype X'] [Fintype X'']

omit [WeilData E] in
/-- Let `π` be split squarefree for `N` at the finite set of places `P` (`IsSplitSquarefree`):
`N = π π̄`, the idele `π` is a uniformiser at each place of `P` and a unit at all others, and no
place of `P` has its conjugate in `P`. For `A = neighbourScale P π` the adele `1 + A`, which is `π`
at `P`, `π̄⁻¹` at the conjugate places and `1` elsewhere, has norm one: its product with its own
conjugate is `1`. -/
lemma star_one_add_neighbourScale_mul (hπ : IsSplitSquarefree P (N : E) π) :
    star (1 + neighbourScale P π) * (1 + neighbourScale P π) = 1 := by
  -- For an idempotent `e`, the map `u ↦ 1 + e (u - 1)` takes inverses to inverses.
  have h_inv {e u u' : 𝔸f E} (he : e * e = e) (hu : u * u' = 1) :
      (1 + e * (u - 1)) * (1 + e * (u' - 1)) = 1 := by
    linear_combination (u - 1) * (u' - 1) * he + e * hu
  have h_factor : 1 + neighbourScale P π =
      (1 + idem P * ((π : 𝔸f E) - 1)) * (1 + star (idem P) * (star (↑π⁻¹ : 𝔸f E) - 1)) := by
    rw [neighbourScale]
    linear_combination
      -((π : 𝔸f E) - 1) * (star (↑π⁻¹ : 𝔸f E) - 1) * idem_mul_star hπ.isConjDisjoint
  calc star (1 + neighbourScale P π) * (1 + neighbourScale P π)
    _ = (1 + idem P * ((π : 𝔸f E) - 1)) * (1 + idem P * ((↑π⁻¹ : 𝔸f E) - 1)) *
        ((1 + star (idem P) * (star (π : 𝔸f E) - 1)) *
          (1 + star (idem P) * (star (↑π⁻¹ : 𝔸f E) - 1))) := by
      simp only [h_factor, star_add, star_sub, star_mul', star_one, star_star]
      ring
    _ = 1 := by simp [h_inv, idem_mul_self, star_idem_mul_self, π.mul_inv, star_mul_star_inv π]

lemma normNegOne_mem : (normNegOne (E := E) : 𝔸f E) ∈ Ô E :=
  SetLike.coe_mem _

lemma neighbourAxis_mem (i : PairIndex X X'') : neighbourAxis X X'' P i ∈ Ô E := by
  rcases i with (i | i) | (i | i) <;>
    simp [neighbourAxis, zero_mem, one_mem, star_mem_Ô, mul_mem, idem_mem_Ô]

/-- The entries of `γ = 1 + A ρ ρ*`, where `A = neighbourScale P π` and
`ρ = neighbourAxis X X'' P`. -/
lemma neighbourMatrix_apply [DecidableEq X] [DecidableEq X''] (i m : PairIndex X X'') :
    neighbourMatrix X X'' P π i m = (if i = m then 1 else 0) +
      neighbourScale P π * (neighbourAxis X X'' P i * star (neighbourAxis X X'' P m)) := by
  simp [neighbourMatrix, vecMulVec_apply, one_apply]

/-- Off `P` and its conjugate, `γ = neighbourMatrix X X'' P π` is the identity. -/
lemma neighbourMatrix_apply_of_notMem [DecidableEq X] [DecidableEq X'']
    {w : FinPlace E} (hw : w ∉ P) (hw_star : star w ∉ P) (i m : PairIndex X X'') :
    evalAt w (neighbourMatrix X X'' P π i m) = if i = m then 1 else 0 := by
  rw [neighbourMatrix_apply, map_add, map_mul, neighbourScale_apply_of_notMem hw hw_star]
  split_ifs <;> simp

/-- The coefficient `neighbourCoeff X X'' P π m` attached to each column `m` of `neighbourMatrix`
has component `0` at every place `w` outside `P` and its conjugate. -/
lemma neighbourCoeff_apply_of_notMem {w : FinPlace E} (hw : w ∉ P) (hw_star : star w ∉ P)
    (m : PairIndex X X'') : evalAt w (neighbourCoeff X X'' P π m) = 0 := by
  rcases m with (m | m) | (m | m) <;>
    simp only [neighbourCoeff, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, map_mul,
      neighbourScale_apply_of_notMem hw hw_star, zero_mul]

/-- Let `P` and its conjugates be the places above the prime `N` (`IsSplitLevel`). Let `δ` be the
scaling adele of `IsScalingAtM`, which is `1` above `N`. Then multiplying by `δ` does not change the
coefficient `neighbourCoeff X X'' P π m` of the isotropic vector that goes with column `m` of
`neighbourMatrix`. -/
lemma mul_neighbourCoeff [Fact N.Prime] (hP : IsSplitLevel P N) (hκ : IsScalingAtM N β δ κ)
    (m : PairIndex X X'') :
    δ * neighbourCoeff X X'' P π m = neighbourCoeff X X'' P π m := by
  have h_scale : δ * neighbourScale P π = neighbourScale P π := by
    rw [neighbourScale]
    linear_combination ((π : 𝔸f E) - 1) * hκ.idem_mul hP +
      (star (↑π⁻¹ : 𝔸f E) - 1) * hκ.star_idem_mul hP
  rcases m with (m | m) | (m | m) <;> simp [neighbourCoeff, ← mul_assoc, h_scale]

/-- Let `π` be split squarefree for `N` at `P`: `N = π π̄`, `π` is a uniformiser on `P` and a unit
elsewhere, and `P` does not meet its conjugate. The matrix `γ = neighbourMatrix X X'' P π` is
`1 + A ρ ρ*`, with rows and columns indexed by the bases of two spaces with last vectors `e`
(index `lastSource`) and `e''` (index `lastTarget`); here `A = neighbourScale P π`,
`j = idem P` is `1` at `P` and `0` elsewhere, `η = normNegOne` has norm `-1`, and
`ρ = e + η̄ j̄ e''`. The adele `neighbourCoeff X X'' P π m` is `A π⁻¹ j̄` for the column of `e`,
`A π⁻¹ η j` for that of `e''` and `0` for the others. This lemma computes it minus `π⁻¹` times
the entry `γ lastSource m`: it is `-ϖ` if `m` is the index of `e` and `0` otherwise, where
`ϖ = j + (1 - j) π⁻¹` is `1` at `P` and `π⁻¹` elsewhere. -/
lemma neighbourCoeff_sub_lastSource [DecidableEq X] [DecidableEq X'']
    (hπ : IsSplitSquarefree P (N : E) π) (m : PairIndex X X'') :
    neighbourCoeff X X'' P π m - (↑π⁻¹ : 𝔸f E) * neighbourMatrix X X'' P π lastSource m =
      -(idem P + (1 - idem P) * (↑π⁻¹ : 𝔸f E)) * if lastSource = m then 1 else 0 := by
  let π' : 𝔸f E := ↑π⁻¹
  have h_corner : neighbourScale P π * π' * star (idem P) - π' * (1 + neighbourScale P π) =
      -(idem P + (1 - idem P) * π') := by
    -- Off the places conjugate to `P`, the adele `A` is `π - 1` at `P` and `0` elsewhere.
    have hA_off : neighbourScale P π * (1 - star (idem P)) = idem P * ((π : 𝔸f E) - 1) := by
      rw [neighbourScale]
      linear_combination (1 - (π : 𝔸f E)) * idem_mul_star hπ.isConjDisjoint +
        (1 - star π') * star_idem_mul_self (P : Set (FinPlace E))
    linear_combination -π' * hA_off - idem P * π.mul_inv
  rw [neighbourMatrix_apply]
  rcases m with (m | m) | (m | m)
  case inl.inr => simpa [neighbourCoeff, neighbourAxis] using h_corner
  all_goals simp [neighbourCoeff, neighbourAxis, mul_assoc, mul_left_comm]

/-- Let `π` be split squarefree for `N` at `P`: `N = π π̄`, `π` is a uniformiser on `P` and a unit
elsewhere, and `P` does not meet its conjugate. The matrix `γ = neighbourMatrix X X'' P π` is
`1 + A ρ ρ*`, with rows and columns indexed by the bases of two spaces with last vectors `e`
(index `lastSource`) and `e''` (index `lastTarget`); here `A = neighbourScale P π`,
`j = idem P` is `1` at `P` and `0` elsewhere, `η = normNegOne` has norm `-1`, and
`ρ = e + η̄ j̄ e''`. The adele `neighbourCoeff X X'' P π m` is `A π⁻¹ j̄` for the column of `e`,
`A π⁻¹ η j` for that of `e''` and `0` for the others. This lemma computes `η̄` times it minus
`π⁻¹` times the entry `γ lastTarget m`: it is `-ϖ` if `m` is the index of `e''` and `0`
otherwise, where `ϖ = j + (1 - j) π⁻¹` is `1` at `P` and `π⁻¹` elsewhere. -/
lemma star_normNegOne_mul_neighbourCoeff_sub_lastTarget [DecidableEq X] [DecidableEq X'']
    (hπ : IsSplitSquarefree P (N : E) π) (m : PairIndex X X'') :
    star (normNegOne (E := E) : 𝔸f E) * neighbourCoeff X X'' P π m -
        (↑π⁻¹ : 𝔸f E) * neighbourMatrix X X'' P π lastTarget m =
      -(idem P + (1 - idem P) * (↑π⁻¹ : 𝔸f E)) * if lastTarget = m then 1 else 0 := by
  let η : 𝔸f E := normNegOne (E := E)
  let π' : 𝔸f E := ↑π⁻¹
  have h_corner : star η * (neighbourScale P π * π' * (η * idem P)) -
      π' * (1 + neighbourScale P π * (star η * star (idem P) * (η * idem P))) =
      -(idem P + (1 - idem P) * π') := by
    -- At `P` the adele `neighbourScale P π` is `π - 1`.
    have hA_on : neighbourScale P π * idem P = idem P * ((π : 𝔸f E) - 1) := by
      rw [neighbourScale]
      linear_combination ((π : 𝔸f E) - 1) * idem_mul_self (P : Set (FinPlace E)) +
        (star π' - 1) * idem_mul_star hπ.isConjDisjoint
    linear_combination
      neighbourScale P π * π' * idem P * star_normNegOne_mul_self (E := E) -
        π' * neighbourScale P π * (star η * η) * idem_mul_star hπ.isConjDisjoint -
        π' * hA_on - idem P * π.mul_inv
  rw [neighbourMatrix_apply]
  rcases m with (m | m) | (m | m)
  case inr.inr => simpa [neighbourCoeff, neighbourAxis] using h_corner
  all_goals simp [neighbourCoeff, neighbourAxis, mul_assoc, mul_left_comm]

/-- The coefficients of the isotropic vector are supported above `N`. -/
lemma idem_conjClosure_mul_neighbourCoeff (hπ : IsSplitSquarefree P (N : E) π)
    (m : PairIndex X X'') :
    idem (P : Set (FinPlace E)).conjClosure * neighbourCoeff X X'' P π m =
      neighbourCoeff X X'' P π m := by
  rw [idem_conjClosure_eq_add_star hπ.isConjDisjoint]
  rcases m with (m | m) | (m | m) <;>
    simp only [neighbourCoeff, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] <;>
    grind [idem_mul_self (P : Set (FinPlace E)), star_idem_mul_self (P : Set (FinPlace E)),
      idem_mul_star hπ.isConjDisjoint]

/-- Suppose that the places above the prime `N` are `P` and its conjugate, that `N = π π̄` with `π`
a uniformiser on `P` and a unit elsewhere, and that `κ` are factors `1` or `δ` for an adele `δ` of
norm one that is `1` above `N`, with the denominators bounded by `β` and `β̄` (`IsScalingAtM`). Let
`x` be column `m` of `γ = neighbourMatrix X X'' P π = 1 + A ρ ρ*` and `c` its coefficient
`neighbourCoeff`. Then `δ c = c`; `x` is integral except at `e` and `e''`; all of `π̄ x` is
integral; and `c - π⁻¹ x_e` and `η̄ c - π⁻¹ x_e''` are integral, with `η = normNegOne` of norm `-1`.
These are the conditions `IsNeighbourVector`. -/
lemma isNeighbourVector_col_neighbourMatrix [DecidableEq X] [DecidableEq X'']
    [Fact N.Prime] (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) (m : PairIndex X X'') :
    IsNeighbourVector π δ (neighbourCoeff X X'' P π m) ((neighbourMatrix X X'' P π).col m) := by
  have h_one (i : PairIndex X X'') : (if i = m then 1 else 0) ∈ Ô E := by
    split_ifs <;> simp [one_mem, zero_mem]
  have hϖ_mem : -(idem P + (1 - idem P) * (↑π⁻¹ : 𝔸f E)) ∈ Ô E :=
    neg_mem (add_mem (idem_mem_Ô _) hπ.one_sub_idem_mul_inv_mem)
  have h_entry (i : PairIndex X X'') : (neighbourMatrix X X'' P π).col m i =
      (if i = m then 1 else 0) +
        neighbourScale P π * (neighbourAxis X X'' P i * star (neighbourAxis X X'' P m)) :=
    neighbourMatrix_apply i m
  refine
    { mul_coeff := mul_neighbourCoeff hP hκ m
      mem_of_ne := fun i hi_source hi_target ↦ ?_
      star_mul_mem := fun i ↦ ?_
      sub_source_mem := ?_
      sub_target_mem := ?_ }
  · have h_axis : neighbourAxis X X'' P i = 0 := by
      rcases i with (i | i) | (i | i) <;> simp_all [neighbourAxis]
    simpa [neighbourMatrix_apply, h_axis] using h_one i
  · rw [h_entry, mul_add, ← mul_assoc]
    exact add_mem (mul_mem hπ.star_mem_integralAdeles (h_one i))
      (mul_mem (star_mul_neighbourScale_mem hπ)
      (mul_mem (neighbourAxis_mem i) (star_mem_Ô (neighbourAxis_mem m))))
  · rw [Matrix.col_apply, neighbourCoeff_sub_lastSource hπ]
    exact mul_mem hϖ_mem (h_one _)
  · rw [Matrix.col_apply, star_normNegOne_mul_neighbourCoeff_sub_lastTarget hπ]
    exact mul_mem hϖ_mem (h_one _)

end Entries

/-- The inner product of `ρ = e + η̄ j̄ e''` with a vector `x` is the sum of the entry at `e` and
`η j` times the entry at `e''`, where `j` is the idempotent of `P` and `η` the unit of norm `-1`. -/
lemma star_neighbourAxis_dotProduct (x : PairIndex X X'' → 𝔸f E) :
    star (neighbourAxis X X'' P) ⬝ᵥ x =
      x lastSource + (normNegOne (E := E) : 𝔸f E) * idem P * x lastTarget := by
  simp [neighbourAxis, dotProduct, Fintype.sum_sum_type]

/-- The vector `ρ = neighbourAxis X X'' P` satisfies `star ρ ⬝ᵥ ρ = 1` when `π` is a split
squarefree idele for `N` at `P` (`hπ`), so that `P` is disjoint from its conjugate. -/
lemma star_neighbourAxis_dotProduct_self (hπ : IsSplitSquarefree P (N : E) π) :
    star (neighbourAxis X X'' P) ⬝ᵥ neighbourAxis X X'' P = 1 := by
  rw [star_neighbourAxis_dotProduct]
  simp only [neighbourAxis, Sum.elim_inl, Sum.elim_inr, star_mul']
  -- The product at `e''` has the factor `j j̄ = 0`.
  grind [idem_mul_star hπ.isConjDisjoint]

/-- Multiplication by `γ = neighbourMatrix X X'' P π` adds to a vector `x` the multiple `A ⟨ρ, x⟩ ρ`
of `ρ`. Here `A` is `neighbourScale P π`, `ρ` is `neighbourAxis X X'' P`, and `⟨ρ, x⟩ = x
lastSource + normNegOne * idem P * x lastTarget`. -/
lemma neighbourMatrix_mulVec [DecidableEq X] [DecidableEq X'']
    (x : PairIndex X X'' → 𝔸f E) (i : PairIndex X X'') :
    (neighbourMatrix X X'' P π *ᵥ x) i = x i + neighbourScale P π *
      (x lastSource + (normNegOne (E := E) : 𝔸f E) * idem P * x lastTarget) *
        neighbourAxis X X'' P i := by
  simp [neighbourMatrix, add_mulVec, smul_mulVec, vecMulVec_mulVec, star_neighbourAxis_dotProduct,
    mul_comm, mul_left_comm]

variable (X X'') in
/-- The matrix `γ` (`neighbourMatrix`) as a finite point of the unitary group, for a split
squarefree idele `π` for `N` at `P`. -/
def neighbourUnitary [DecidableEq X] [DecidableEq X'']
    (hπ : IsSplitSquarefree P (N : E) π) : Gf E (PairIndex X X'') :=
  U.of isUnit_one (neighbourMatrix X X'' P π) <| by
    rw [mul_one]
    exact conjTranspose_mul_one_add_smul_vecMulVec (star_neighbourAxis_dotProduct_self hπ)
      (star_one_add_neighbourScale_mul hπ)

/-- The matrix of `neighbourUnitary` is `γ`. -/
lemma coe_neighbourUnitary [DecidableEq X] [DecidableEq X''] (hπ : IsSplitSquarefree P (N : E) π) :
    (neighbourUnitary X X'' hπ : Matrix (PairIndex X X'') (PairIndex X X'') (𝔸f E)) =
      neighbourMatrix X X'' P π :=
  rfl

omit [Fintype X] [Fintype X''] [WeilData E] in
/-- If `N` is prime, `P` is a split level for `N` (`IsSplitLevel P N`) and `κ` satisfies
`IsScalingAtM N β δ κ`, then each factor `κ i` is `1` at the places of `P`:
`idem P * κ i = idem P`. -/
lemma IsScalingAtM.idem_mul_apply [Fact N.Prime] (hκ : IsScalingAtM N β δ κ)
    (hP : IsSplitLevel P N) (i : PairIndex X X'') : idem P * κ i = idem P := by
  rcases hκ.eq_one_or_eq i with h | h <;> simp [h, hκ.idem_mul hP]

omit [Fintype X] [Fintype X''] [WeilData E] in
/-- If `N` is prime, `P` is a split level for `N` (`IsSplitLevel P N`) and `κ` satisfies
`IsScalingAtM N β δ κ`, then each factor `κ i` is `1` at the places conjugate to `P`:
`star (idem P) * κ i = star (idem P)`. -/
lemma IsScalingAtM.star_idem_mul_apply [Fact N.Prime] (hκ : IsScalingAtM N β δ κ)
    (hP : IsSplitLevel P N) (i : PairIndex X X'') : star (idem P) * κ i = star (idem P) := by
  rcases hκ.eq_one_or_eq i with h | h <;> simp [h, hκ.star_idem_mul hP]

variable [DecidableEq X] [DecidableEq X'']

/-- At a level prime `N` split as `P` and its conjugate, the matrix `γ` commutes with the diagonal
matrix of the scaling factors `κ`: it differs from `1` only above `N`, where all of these factors
are `1`. -/
lemma commute_neighbourMatrix_diagonal [Fact N.Prime] (hP : IsSplitLevel P N)
    (hκ : IsScalingAtM N β δ κ) : Commute (neighbourMatrix X X'' P π) (diagonal κ) := by
  have h_scale (i : PairIndex X X'') : neighbourScale P π * κ i = neighbourScale P π := by
    grind [neighbourScale, hκ.idem_mul_apply hP i, hκ.star_idem_mul_apply hP i]
  ext i m : 1
  rw [mul_diagonal, diagonal_mul]
  simp only [neighbourMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply]
  grind [h_scale i, h_scale m]

/-- The diagonal matrix of the factors `κ`, each of which has norm one, as a finite point of the
unitary group. -/
def scalingUnitary (hκ : IsScalingAtM N β δ κ) : Gf E (PairIndex X X'') :=
  U.of isUnit_one (diagonal κ) <| by simp [mul_comm (star _), hκ.apply_mul_star_eq_one]

section Vanishing

omit [WeilData E]

/-- The vectors that vanish at the places of `P` and at their conjugates. For a split level `N`
these are the places above `N`. -/
def vanishingAbove (ι : Type) (P : Finset (FinPlace E)) : AddSubgroup (ι → 𝔸f E) :=
  ((idem (P : Set (FinPlace E)).conjClosure : 𝔸f E) • AddMonoidHom.id (ι → 𝔸f E)).ker

lemma mem_vanishingAbove {ι : Type} {x : ι → 𝔸f E} :
    x ∈ vanishingAbove ι P ↔ (idem (P : Set (FinPlace E)).conjClosure : 𝔸f E) • x = 0 :=
  .rfl

lemma mulVec_mem_vanishingAbove {ι ι' : Type} {x : ι → 𝔸f E} [Fintype ι] (M : Matrix ι' ι (𝔸f E))
    (hx : x ∈ vanishingAbove ι P) : M *ᵥ x ∈ vanishingAbove ι' P := by
  rw [mem_vanishingAbove, ← mulVec_smul, mem_vanishingAbove.1 hx, mulVec_zero]

/-- The part of a vector off `P` and its conjugate vanishes at these places. -/
lemma sub_idem_smul_mem_vanishingAbove {ι : Type} (x : ι → 𝔸f E) :
    x - (idem (P : Set (FinPlace E)).conjClosure : 𝔸f E) • x ∈ vanishingAbove ι P := by
  rw [mem_vanishingAbove, smul_sub, smul_smul, idem_mul_self, sub_self]

end Vanishing

section Lattices

variable (X')
/-- The homomorphism `g ↦ g ⊗ 1`. Its values act on matrices with columns indexed by `X'` by left
multiplication with `g`. -/
def kroneckerOne (ι : Type) [Fintype ι] [DecidableEq ι] : Gf E ι →* Gf E (ι × X') :=
  (U.kroneckerHom (S := (1 : Matrix X' X' (𝔸f E))) (one_mul 1) (by simp)).comp
    (MonoidHom.inr (U (1 : Matrix X' X' (𝔸f E))) (Gf E ι))

/-- The unitary `(γ κ) ⊗ 1`. It carries the standard lattice of `Hom (X', X⁻ ⊕ X'')` to the lattice
that is the neighbour above `N` and has its rows scaled by `κ` elsewhere. -/
def latticeUnitary (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    Gf E (PairIndex X X'' × X') :=
  kroneckerOne X' (PairIndex X X'') (neighbourUnitary X X'' hπ * scalingUnitary hκ)

/-- The image of the standard lattice under `latticeUnitary`. For a pair of edges it is the lattice
`zeroTermLattice` of their splitting, by `DoubleLiftData.zeroTermLattice_splitting_eq`. -/
def neighbourLattice (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    AddSubgroup (PairIndex X X'' × X' → 𝔸f E) :=
  (stdLattice E (PairIndex X X'' × X')).map
    (DistribSMul.toAddMonoidHom (PairIndex X X'' × X' → 𝔸f E) (latticeUnitary X' hπ hκ))

/-- The elements of the lattice that vanish above `N`. -/
def awayLattice (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    AddSubgroup (PairIndex X X'' × X' → 𝔸f E) :=
  neighbourLattice X' hπ hκ ⊓ vanishingAbove (PairIndex X X'' × X') P

/-- The classes of `awayLattice` modulo its integral points. Only the rows scaled by `δ` can fail
to be integral. -/
abbrev AwayLatticeQuotient (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    Type :=
  awayLattice X' hπ hκ ⧸ (stdLattice E (PairIndex X X'' × X')).addSubgroupOf (awayLattice X' hπ hκ)

end Lattices

omit [WeilData E] in
/-- The matrix of `g ⊗ 1` is the Kronecker product of that of `g` with the identity. -/
lemma coe_kroneckerOne {ι : Type} [Fintype ι] [DecidableEq ι] (g : Gf E ι) :
    (kroneckerOne X' ι g : Matrix (ι × X') (ι × X') (𝔸f E)) =
      (g : Matrix ι ι (𝔸f E)) ⊗ₖ (1 : Matrix X' X' (𝔸f E)) := by
  simp [kroneckerOne]

omit [WeilData E] in
/-- The action of `g ⊗ 1` on a matrix `x` multiplies each column of `x` by `g`. -/
lemma kroneckerOne_smul {ι : Type} [Fintype ι] [DecidableEq ι] (g : Gf E ι) (x : ι × X' → 𝔸f E)
    (i : ι × X') :
    (kroneckerOne X' ι g • x) i = ((g : Matrix ι ι (𝔸f E)) *ᵥ fun l : ι ↦ x (l, i.2)) i.1 := by
  change ((kroneckerOne X' ι g : Matrix (ι × X') (ι × X') (𝔸f E)) *ᵥ x) i = _
  simp [coe_kroneckerOne, mulVec, dotProduct, Fintype.sum_prod_type, one_apply]

omit [WeilData E] in
/-- The conjugate of `residueOverN y` (the adele `y w / N` at `w ∈ P`, `0` elsewhere) is unchanged
by multiplication with the conjugate of `idem P`, so it is supported at the places conjugate to
`P`. -/
lemma star_idem_mul_star_residueOverN [Fact N.Prime] (y : P → ZMod N) :
    star (idem P) * star (residueOverN y) = star (residueOverN y) := by
  rw [← star_mul', idem_mul_residueOverN]

omit [Fintype X'] [DecidableEq X'] in
/-- Let `π` be split squarefree for `N` at `P`, `j = idem P` the adele `1` at `P` and `0` elsewhere
and `η = normNegOne` of norm `-1`. The matrix `x` has rows indexed by `PairIndex X X''`, with last
indices `e = lastSource` and `e'' = lastTarget`, and columns by `X'`. Let
`γ = neighbourMatrix X X'' P π`, let `ρ = neighbourAxis X X'' P = e + η̄ j̄ e''` and, for residues
`y` modulo `N` at the places of `P`, let `n y = neighbourTranslation X X'' y` be the matrix with row
`η ȳ / N` at `e`, row `-ȳ / N` at `e''` and zero elsewhere. After multiplication by `j̄`, each
column of `γ x + n y` is that of `x` plus `ρ` times `j̄ (π̄⁻¹ x_e + η ȳ / N) - j̄ x_e`. -/
lemma star_idem_mul_neighbour_add_translation (hπ : IsSplitSquarefree P (N : E) π)
    (x : PairIndex X X'' × X' → 𝔸f E) (y : X' → P → ZMod N) (i : PairIndex X X'' × X') :
    star (idem P) * ((neighbourMatrix X X'' P π *ᵥ fun l : PairIndex X X'' ↦ x (l, i.2)) i.1 +
        neighbourTranslation X X'' y i) =
      star (idem P) * x i + neighbourAxis X X'' P i.1 *
        (star (idem P) * (star (↑π⁻¹ : 𝔸f E) * x (lastSource, i.2) +
          (normNegOne (E := E) : 𝔸f E) * star (residueOverN (y i.2))) -
            star (idem P) * x (lastSource, i.2)) := by
  obtain ⟨b, a⟩ := i
  simp only [neighbourMatrix_mulVec, neighbourTranslation, neighbourScale]
  have h_star_sq : star (idem P) * star (idem P) = (star (idem P) : 𝔸f E) :=
    star_idem_mul_self _
  have h_disjoint : idem P * star (idem P) = (0 : 𝔸f E) := idem_mul_star hπ.isConjDisjoint
  have h_norm : star (normNegOne (E := E) : 𝔸f E) * (normNegOne (E := E) : 𝔸f E) = -1 :=
    star_normNegOne_mul_self
  rcases b with (b | b) | (b | b)
  -- The four kinds of row index differ only in the entries of `ρ` and of `n y`.
  all_goals
    simp only [neighbourAxis, star_mul', Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
    grind

/-- Let the prime `N` be split as `P` and its conjugate, let `π` be split squarefree for `N` at `P`,
let `η = normNegOne` have norm `-1` and, for residues `y` modulo `N` at the places of `P`, let
`residueOverN y` be the adele `y / N` at `P` and `0` elsewhere. Multiplication by the conjugate of
`idem P` keeps only the places conjugate to `P`. If `t` is integral there, then `π̄⁻¹ t + η ȳ / N`
is integral there for exactly one family of residues `y`, and otherwise for none. -/
lemma exists_class_star_idem_mul_mem_iff [Fact N.Prime] (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (t : 𝔸f E) :
    ∃ y₀ : P → ZMod N, ∀ y : P → ZMod N,
      star (idem P) * (star (↑π⁻¹ : 𝔸f E) * t +
        (normNegOne (E := E) : 𝔸f E) * star (residueOverN y)) ∈ Ô E ↔
      star (idem P) * t ∈ Ô E ∧ y₀ = y := by
  set η : 𝔸f E := ↑(normNegOne (E := E))
  have hη_norm : star η * η = -1 := star_normNegOne_mul_self
  have hη_mem : η ∈ Ô E := normNegOne_mem
  -- The map `w ↦ η w̄` preserves integrality in both directions.
  have h_twist (w : 𝔸f E) : η * star w ∈ Ô E ↔ w ∈ Ô E := by
    refine ⟨fun h ↦ ?_, fun h ↦ mul_mem hη_mem (star_mem_Ô h)⟩
    have h_inv : η * star (η * star w) = -w := by grind [star_mul', star_star]
    simpa only [h_inv, neg_mem_iff] using mul_mem hη_mem (star_mem_Ô h)
  -- It turns the left side into `z - y / N` at `P`.
  set z : 𝔸f E := η * ↑π⁻¹ * star t with hz
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : P → ZMod N, ∀ y : P → ZMod N,
      idem P * (z - residueOverN y) ∈ Ô E ↔ idem P * ((N : 𝔸f E) * z) ∈ Ô E ∧ y₀ = y :=
    hP.exists_sub_residueOverN_mem_iff z
  refine ⟨y₀, fun y ↦ ?_⟩
  have h_sub : η * star (star (idem P) * (star (↑π⁻¹ : 𝔸f E) * t + η * star (residueOverN y))) =
      idem P * (z - residueOverN y) := by
    simp only [hz, star_mul', star_add, star_star]
    grind
  -- `N z = η π̄ t̄`, and `π̄` is a unit at `P`.
  have h_mul : idem P * ((N : 𝔸f E) * z) = star (π : 𝔸f E) * (η * star (star (idem P) * t)) := by
    simp only [hz, hπ.natCast_eq_mul_star, star_mul', star_star]
    grind [π.mul_inv]
  have h_div : η * star (star (idem P) * t) =
      star ((1 - idem P) * (↑π⁻¹ : 𝔸f E)) * (idem P * ((N : 𝔸f E) * z)) := by
    simp only [h_mul, star_sub, star_one, star_mul', star_star]
    grind [idem_mul_star hπ.isConjDisjoint, star_mul_star_inv π]
  rw [← h_twist, h_sub, hy₀, ← h_twist (star (idem (P : Set (FinPlace E))) * t)]
  refine and_congr_left' ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h_div]
    exact mul_mem (star_mem_Ô hπ.one_sub_idem_mul_inv_mem) h
  · rw [h_mul]
    exact mul_mem hπ.star_mem_integralAdeles h

/-- Let the prime `N` be split as `P` and its conjugate and `π` split squarefree for `N` at `P`.
`kroneckerOne` lets the unitary `γ` act on each column. Let `η = normNegOne` have norm `-1`. For
residues `y` modulo `N` at `P`, `n y = neighbourTranslation X X'' y` has row `η ȳ / N` at `e`, row
`-ȳ / N` at `e''` and zero elsewhere. At the places conjugate to `P`, `γ x + n y` is integral for
exactly one `y` if `x` is integral there, and for none otherwise. -/
lemma exists_add_neighbourTranslation_mem_iff [Fact N.Prime] (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (x : PairIndex X X'' × X' → 𝔸f E) :
    ∃ y₀ : X' → P → ZMod N, ∀ y : X' → P → ZMod N,
      kroneckerOne X' (PairIndex X X'') (neighbourUnitary X X'' hπ) • x +
          neighbourTranslation X X'' y ∈ integralBox (PairIndex X X'' × X')
          (star ⁻¹' (P : Set (FinPlace E))) ↔
        x ∈ integralBox (PairIndex X X'' × X') (star ⁻¹' (P : Set (FinPlace E))) ∧ y₀ = y := by
  -- In column `a`, take the residues attached to the entry of `x` at `lastSource`.
  choose y₀ hy₀ using fun a : X' ↦ exists_class_star_idem_mul_mem_iff hP hπ (x (lastSource, a))
  refine ⟨y₀, fun y ↦ ?_⟩
  simp only [mem_integralBox, ← star_idem, Pi.add_apply, kroneckerOne_smul,
    coe_neighbourUnitary, star_idem_mul_neighbour_add_translation hπ]
  refine ⟨fun h ↦ ?_, fun ⟨hx, hy⟩ i ↦ ?_⟩
  · -- The row at `lastSource` decides the residues; then, times `j̄`, all entries differ from those
    -- of `x` by integral adeles.
    have h_row (a : X') : star (idem P) * (star (↑π⁻¹ : 𝔸f E) * x (lastSource, a) +
        (normNegOne (E := E) : 𝔸f E) * star (residueOverN (y a))) ∈ Ô E := by
      simpa [neighbourAxis] using h (lastSource, a)
    have h_residues (a : X') : star (idem P) * x (lastSource, a) ∈ Ô E ∧ y₀ a = y a :=
      (hy₀ a (y a)).1 (h_row a)
    refine ⟨fun i ↦ ?_, funext fun a ↦ (h_residues a).2⟩
    exact (add_mem_cancel_right
      (mul_mem (neighbourAxis_mem i.1) (sub_mem (h_row i.2) (h_residues i.2).1))).1 (h i)
  · exact add_mem (hx i) (mul_mem (neighbourAxis_mem i.1)
      (sub_mem ((hy₀ i.2 (y i.2)).2 ⟨hx (lastSource, i.2), congrFun hy i.2⟩)
        (hx (lastSource, i.2))))

omit [Fintype X] [Fintype X'] [Fintype X''] [DecidableEq X] [DecidableEq X'] [DecidableEq X''] in
/-- The translation `n y = neighbourTranslation X X'' y` is supported at the places conjugate to
`P`: multiplication by `star (idem P)`, the idempotent `j̄` of these places, fixes it. -/
lemma star_idem_smul_neighbourTranslation [Fact N.Prime] (y : X' → P → ZMod N) :
    star (idem P : 𝔸f E) • neighbourTranslation X X'' y = neighbourTranslation X X'' y := by
  ext1 ⟨i, a⟩
  rcases i with (i | i) | (i | i) <;>
    simp [neighbourTranslation, mul_left_comm _ (normNegOne (E := E) : 𝔸f E),
      star_idem_mul_star_residueOverN (y a)]

omit [WeilData E] in
/-- The element `scalingUnitary hκ ⊗ 1`, where `scalingUnitary hκ` is the diagonal matrix of the
factors `κ`, multiplies row `i.1` of a matrix `x` by `κ i.1`. -/
lemma kroneckerOne_scalingUnitary_smul (hκ : IsScalingAtM N β δ κ)
    (x : PairIndex X X'' × X' → 𝔸f E) (i : PairIndex X X'' × X') :
    (kroneckerOne X' (PairIndex X X'') (scalingUnitary hκ) • x) i = κ i.1 * x i := by
  rw [kroneckerOne_smul]
  exact mulVec_diagonal κ _ i.1

/-- At a level prime `N` split as `P` and its conjugate, the matrix of `latticeUnitary` is
`(diagonal κ * γ) ⊗ 1`, where `γ = neighbourMatrix X X'' P π`. -/
lemma coe_latticeUnitary [Fact N.Prime] (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    (latticeUnitary X' hπ hκ : Matrix (PairIndex X X'' × X') (PairIndex X X'' × X') (𝔸f E)) =
      (diagonal κ * neighbourMatrix X X'' P π) ⊗ₖ (1 : Matrix X' X' (𝔸f E)) := by
  rw [latticeUnitary, coe_kroneckerOne, ← (commute_neighbourMatrix_diagonal hP hκ).eq]
  rfl

/-- Acting by `latticeUnitary` means scaling the rows by `κ`, then acting by `γ ⊗ 1`. -/
lemma latticeUnitary_smul (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    (x : PairIndex X X'' × X' → 𝔸f E) :
    latticeUnitary X' hπ hκ • x =
      kroneckerOne X' (PairIndex X X'') (neighbourUnitary X X'' hπ) •
        fun i : PairIndex X X'' × X' ↦ κ i.1 * x i := by
  rw [latticeUnitary, map_mul, mul_smul, funext (kroneckerOne_scalingUnitary_smul hκ x)]

instance (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    Fintype (AwayLatticeQuotient X' hπ hκ) := by
  -- The integral points have finite index in the whole lattice.
  refine AddSubgroup.fintypeOfIndexNeZero fun h_zero ↦ ?_
  exact relIndex_map_stdLattice_ne_zero (latticeUnitary X' hπ hκ)
    (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h_zero)

end Unitary

section AwayFromN

/-- Let `π` be split squarefree for `N` at `P`, and let `κ` be row factors that are `1` or a fixed
adele `δ` of norm one (`IsScalingAtM`). The unitary `latticeUnitary` is `(γ κ) ⊗ 1` for
`γ = neighbourMatrix X X'' P π`. On a matrix `x` that vanishes at `P` and its conjugate, where `γ`
acts trivially, it multiplies row `b` by `κ b`. -/
lemma latticeUnitary_smul_of_mem_vanishingAbove {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E} [DecidableEq X] [DecidableEq X'']
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    {x : PairIndex X X'' × X' → 𝔸f E} (hx : x ∈ vanishingAbove (PairIndex X X'' × X') P) :
    latticeUnitary X' hπ hκ • x = fun i : PairIndex X X'' × X' ↦ κ i.1 * x i := by
  have h_zero (i : PairIndex X X'' × X') : (idem P + star (idem P)) * x i = 0 := by
    simpa [← idem_conjClosure_eq_add_star hπ.isConjDisjoint] using
      congrFun (mem_vanishingAbove.1 hx) i
  have h_scale (i : PairIndex X X'' × X') : neighbourScale P π * x i = 0 := by
    grind [neighbourScale, h_zero i, idem_mul_self (P : Set (FinPlace E)),
      star_idem_mul_self (P : Set (FinPlace E)), idem_mul_star hπ.isConjDisjoint]
  ext1 i
  simp only [latticeUnitary_smul, kroneckerOne_smul, coe_neighbourUnitary, neighbourMatrix_mulVec]
  grind [h_scale (lastSource, i.2), h_scale (lastTarget, i.2)]

/-- Let `π` be split squarefree for `N` at `P`. Let `κ` be row factors that are `1` or a fixed adele
`δ` of norm one, with denominators bounded by `β` and `β̄` (`IsScalingAtM`). Off `P` and its
conjugate, `neighbourLattice` is the standard lattice with its rows scaled by `κ`: a matrix `x` that
vanishes at `P` and its conjugate lies in it if and only if `κ⁻¹ x = κ̄ x` has integral entries. -/
lemma mem_neighbourLattice_iff_of_mem_vanishingAbove {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E} [DecidableEq X] [DecidableEq X'']
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    {x : PairIndex X X'' × X' → 𝔸f E} (hx : x ∈ vanishingAbove (PairIndex X X'' × X') P) :
    x ∈ neighbourLattice X' hπ hκ ↔ ∀ i : PairIndex X X'' × X', star (κ i.1) * x i ∈ Ô E := by
  -- The matrix `x` is the image of `κ̄ x`.
  have h_vanish : (fun i ↦ star (κ i.1) * x i) ∈ vanishingAbove (PairIndex X X'' × X') P :=
    funext fun i ↦ (mul_left_comm _ _ _).trans (mul_eq_zero_of_right _ (congrFun hx i))
  have h_image : latticeUnitary X' hπ hκ • (fun i ↦ star (κ i.1) * x i) = x := by
    simp only [latticeUnitary_smul_of_mem_vanishingAbove hπ hκ h_vanish, ← mul_assoc,
      hκ.apply_mul_star_eq_one, one_mul]
  refine ⟨fun ⟨x₀, hx₀, h_eq⟩ i ↦ ?_, fun h ↦ ⟨_, h, h_image⟩⟩
  obtain rfl : x₀ = fun i ↦ star (κ i.1) * x i :=
    MulAction.injective (latticeUnitary X' hπ hκ) (h_eq.trans h_image.symm)
  exact hx₀ i

/-- Let `π` be split squarefree for `N` at `P`, and let `κ` be row factors of norm one with
denominator at most `β` in the first block and `β̄` in the second (`IsScalingAtM`). An element of
`awayLattice`, the part of `neighbourLattice` that vanishes at `P` and its conjugate, is `κ` times
an integral matrix. So its rows, times `β` in the first block and `β̄` in the second, are integral
at every place, in particular at those not dividing `n`, as `weightedTranslations n` asks. -/
lemma awayLattice_le_weightedTranslations {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E} [DecidableEq X] [DecidableEq X'']
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) (n : ℕ) :
    awayLattice X' hπ hκ ≤
      weightedTranslations n fun i : PairIndex X X'' × X' ↦ selfOrConj β i.1 := by
  rintro x ⟨hx, hx_zero⟩ i w -
  have h_eq : selfOrConj β i.1 * x i = selfOrConj β i.1 * κ i.1 * (star (κ i.1) * x i) := by
    linear_combination -(selfOrConj β i.1 * x i) * hκ.apply_mul_star_eq_one i.1
  rw [h_eq]
  exact mem_Ô.1 (mul_mem (hκ.selfOrConj_mul_mem i.1)
    ((mem_neighbourLattice_iff_of_mem_vanishingAbove hπ hκ hx_zero).1 hx i)) w

/-- Let `π` be split squarefree for `N` at `P` (`IsSplitSquarefree`): `N = π π̄`, `π` is a
uniformiser on `P` and a unit elsewhere, and `P` does not meet its conjugate. Let `κ` be row factors
that are `1` or a fixed adele `δ`, with denominator at most `β̄` (`IsScalingAtM`). The matrices have
rows indexed by `PairIndex X X''`, the basis indices of a sum of two definite spaces, and columns
indexed by `X'`. The group `awayLattice` consists of the matrices in `neighbourLattice` that vanish
at `P` and its conjugate. `AwayLatticeQuotient` is its quotient by the matrices all of whose entries
lie in the integral adeles `Ô E`. The order of this quotient divides the number of such matrices
with entries in `Ô E ⧸ (β)`. -/
lemma card_awayLatticeQuotient_dvd {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E} [DecidableEq X] [DecidableEq X'']
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    Fintype.card (AwayLatticeQuotient X' hπ hκ) ∣
      Nat.card (PairIndex X X'' × X' → Ô E ⧸ Ideal.span {β}) := by
  -- Reduce the conjugate of `κ̄ x` modulo `β`. If it is `0`, then `x` is `β̄ κ` times an integral
  -- matrix, hence integral.
  have h_int (x : awayLattice X' hπ hκ) (i : PairIndex X X'' × X') :
      star (κ i.1) * x.val i ∈ Ô E :=
    (mem_neighbourLattice_iff_of_mem_vanishingAbove hπ hκ x.property.2).1 x.property.1 i
  let reduction : awayLattice X' hπ hκ →+ PairIndex X X'' × X' → Ô E ⧸ Ideal.span {β} :=
    AddMonoidHom.mk' (fun x i ↦ Ideal.Quotient.mk _ (star ⟨_, h_int x i⟩)) fun x y ↦ by
      ext i
      exact congrArg (Ideal.Quotient.mk _) (Subtype.ext (by simp [mul_add]))
  have h_ker : reduction.ker ≤
      (stdLattice E (PairIndex X X'' × X')).addSubgroupOf (awayLattice X' hπ hκ) := by
    intro x hx i
    obtain ⟨z, hz⟩ : ∃ z : Ô E, star ⟨_, h_int x i⟩ = β * z :=
      (Ideal.Quotient.eq_zero_iff_dvd β _).1 (congrFun hx i)
    have hz_coe : star (star (κ i.1) * x.val i) = (β : 𝔸f E) * z := congrArg Subtype.val hz
    have hx_eq : x.val i = star (β : 𝔸f E) * κ i.1 * star (z : 𝔸f E) := by
      rw [mul_comm _ (κ i.1), mul_assoc, ← star_mul', ← hz_coe, star_star, ← mul_assoc,
        hκ.apply_mul_star_eq_one, one_mul]
    change x.val i ∈ Ô E
    rw [hx_eq]
    exact mul_mem (hκ.star_mul_mem i.1) (star_mem_Ô z.property)
  rw [← Nat.card_eq_fintype_card]
  exact (AddSubgroup.dvd_index_map _ h_ker).trans (AddSubgroup.index_dvd_card _)

end AwayFromN

/-- Let the prime `N` be split as `P` and its conjugate, let `N = π π̄` with `π` a uniformiser on
`P` and a unit elsewhere, and let `κ` be row factors that are `1` or `δ`, where `δ` is `1` above `N`
(`IsScalingAtM`). Then every translation `n y` attached to residues `y` modulo `N` at `P` lies in
`neighbourLattice`, the image of the standard lattice under `(γ κ) ⊗ 1` for
`γ = neighbourMatrix X X'' P π`. -/
lemma neighbourTranslation_mem_neighbourLattice {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E} [DecidableEq X] [DecidableEq X''] [Fact N.Prime]
    (hP : IsSplitLevel P N) (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    (y : X' → P → ZMod N) : neighbourTranslation X X'' y ∈ neighbourLattice X' hπ hκ := by
  -- Write `-n y = γ x`. Then `γ x + n y = 0` is integral, so `x` is integral at the places
  -- conjugate to `P`, and `n y` is the image of the part of `-x` at these places.
  set γ : Gf E (PairIndex X X'' × X') :=
    kroneckerOne X' (PairIndex X X'') (neighbourUnitary X X'' hπ)
  obtain ⟨x, hx⟩ : ∃ x : PairIndex X X'' × X' → 𝔸f E, γ • x = -neighbourTranslation X X'' y :=
    MulAction.surjective γ (-neighbourTranslation X X'' y)
  obtain ⟨y₀, hy₀⟩ := exists_add_neighbourTranslation_mem_iff hP hπ x
  have hx_box : x ∈ integralBox (PairIndex X X'' × X') (star ⁻¹' (P : Set (FinPlace E))) :=
    ((hy₀ y).1 (by simp [γ, hx])).1
  have h_scaled : (fun i ↦ κ i.1 * (-(star (idem P) * x i))) = -(star (idem P : 𝔸f E) • x) :=
    funext fun i ↦ by simp [mul_left_comm (κ i.1), ← mul_assoc, hκ.star_idem_mul_apply hP i.1]
  refine ⟨fun i ↦ -(star (idem P) * x i), fun i ↦ neg_mem ?_, ?_⟩
  · rw [star_idem]
    exact mem_integralBox.1 hx_box i
  · -- `γ` is linear, so it commutes with multiplication by the idempotent.
    have h_comm : γ • star (idem P : 𝔸f E) • x = star (idem P : 𝔸f E) • γ • x :=
      mulVec_smul ..
    rw [DistribSMul.toAddMonoidHom_apply, latticeUnitary_smul, h_scaled, smul_neg, h_comm, hx,
      smul_neg, neg_neg, star_idem_smul_neighbourTranslation]

/-- Let `N = π π̄` with `π` a uniformiser on `P` and a unit elsewhere, and let `P` be disjoint from
its conjugate (`IsSplitSquarefree`). An adele is integral at `P` if its product with `idem P`,
which is `1` at `P` and `0` elsewhere, is integral. The matrices have rows indexed by
`PairIndex X X''`, with last indices `e` and `e''`, and columns by `X'`; `kroneckerOne` lets the
unitary `γ` (`neighbourUnitary`, with matrix `neighbourMatrix X X'' P π`) act on each column, and
`n y = neighbourTranslation X X'' y` has row `η ȳ / N` at `e` and `-ȳ / N` at `e''`, both
supported at the places conjugate to `P`. If `z` is integral at `P`, then so is `γ z + n y`: at
`P`, `γ` is integral and `n y` is `0`. -/
lemma idem_mul_neighbour_add_translation_mem {π : (𝔸f E)ˣ} [DecidableEq X] [DecidableEq X'']
    [Fact N.Prime] (hπ : IsSplitSquarefree P (N : E) π)
    {z : PairIndex X X'' × X' → 𝔸f E} (hz : ∀ i : PairIndex X X'' × X', idem P * z i ∈ Ô E)
    (y : X' → P → ZMod N) (i : PairIndex X X'' × X') :
    idem P * (kroneckerOne X' (PairIndex X X'') (neighbourUnitary X X'' hπ) • z +
      neighbourTranslation X X'' y) i ∈ Ô E := by
  have h_translation : idem P * neighbourTranslation X X'' y i = 0 := by
    simpa [← mul_assoc, idem_mul_star hπ.isConjDisjoint] using
      congrArg (idem P * ·) (congrFun (star_idem_smul_neighbourTranslation y) i).symm
  set c : 𝔸f E := idem P * z (lastSource, i.2) +
    (normNegOne (E := E) : 𝔸f E) * (idem P * z (lastTarget, i.2)) with hc
  have h_entry : idem P * (neighbourMatrix X X'' P π *ᵥ fun l ↦ z (l, i.2)) i.1 =
      idem P * z i + ((π : 𝔸f E) - 1) * c * neighbourAxis X X'' P i.1 := by
    rw [neighbourMatrix_mulVec, neighbourScale, hc]
    grind [idem_mul_self (P : Set (FinPlace E)), idem_mul_star hπ.isConjDisjoint]
  rw [Pi.add_apply, mul_add, h_translation, add_zero, kroneckerOne_smul, coe_neighbourUnitary,
    h_entry]
  exact add_mem (hz i) (mul_mem (mul_mem (sub_mem hπ.mem_integralAdeles (one_mem _))
    (add_mem (hz _) (mul_mem normNegOne_mem (hz _)))) (neighbourAxis_mem i.1))

/-- Let the prime `N` be split as `P` and its conjugate, let `N = π π̄` with `π` a uniformiser on
`P` and a unit elsewhere, and let `κ` be row factors that are `1` above `N` (`IsScalingAtM`). Above
`N` the translations `n y` represent `neighbourLattice` modulo its integral points: for each element
`x` there is exactly one family `y` of residues modulo `N` at `P` such that `x + n y` is integral at
`P` and its conjugate, the places above `N`. -/
lemma existsUnique_add_neighbourTranslation_mem {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E} [DecidableEq X] [DecidableEq X''] [Fact N.Prime]
    (hP : IsSplitLevel P N) (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    {x : PairIndex X X'' × X' → 𝔸f E} (hx : x ∈ neighbourLattice X' hπ hκ) :
    ∃! y : X' → P → ZMod N, x + neighbourTranslation X X'' y ∈
      integralBox (PairIndex X X'' × X') (P : Set (FinPlace E)).conjClosure := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  set z : PairIndex X X'' × X' → 𝔸f E := fun i ↦ κ i.1 * x₀ i with hz
  -- Above `N` the factors `κ` are `1`, so `z = κ x₀` is integral there.
  have hz_idem (i : PairIndex X X'' × X') : idem P * z i ∈ Ô E := by
    simpa only [hz, ← mul_assoc, hκ.idem_mul_apply hP] using mul_mem (idem_mem_Ô _) (hx₀ i)
  have hz_box : z ∈ integralBox (PairIndex X X'' × X') (star ⁻¹' (P : Set (FinPlace E))) := by
    simpa only [mem_integralBox, hz, ← star_idem, ← mul_assoc, hκ.star_idem_mul_apply hP] using
      fun i ↦ mul_mem (star_mem_Ô (idem_mem_Ô _)) (hx₀ i)
  -- At the places conjugate to `P`, the sum `γ z + n y` is integral for exactly one family `y₀`.
  obtain ⟨y₀, hy₀⟩ := exists_add_neighbourTranslation_mem_iff hP hπ z
  have h_iff (y : X' → P → ZMod N) :
      latticeUnitary X' hπ hκ • x₀ + neighbourTranslation X X'' y ∈
        integralBox (PairIndex X X'' × X') (P : Set (FinPlace E)).conjClosure ↔ y₀ = y := by
    -- At `P` the sum is integral, so only the conjugate places count.
    have h_conj : kroneckerOne X' (PairIndex X X'') (neighbourUnitary X X'' hπ) • z +
        neighbourTranslation X X'' y ∈ integralBox (PairIndex X X'' × X')
          (star ⁻¹' (P : Set (FinPlace E))) ↔ y₀ = y :=
      (hy₀ y).trans (and_iff_right hz_box)
    simp only [← h_conj, latticeUnitary_smul, ← hz, mem_integralBox, add_mul, ← star_idem,
      idem_conjClosure_eq_add_star hπ.isConjDisjoint,
      add_mem_cancel_left (idem_mul_neighbour_add_translation_mem hπ hz_idem y _)]
  exact ⟨y₀, (h_iff y₀).2 rfl, fun y hy ↦ ((h_iff y).1 hy).symm⟩

omit [Fintype X] [Fintype X'] [Fintype X''] [DecidableEq X'] in
/-- Under `hπ`, the translations `n y = neighbourTranslation X X'' y` are supported above `N`:
multiplication by the idempotent `idem` of `P` and its conjugate places fixes them. -/
lemma idem_conjClosure_smul_neighbourTranslation {π : (𝔸f E)ˣ} [Fact N.Prime]
    (hπ : IsSplitSquarefree P (N : E) π) (y : X' → P → ZMod N) :
    (idem (P : Set (FinPlace E)).conjClosure : 𝔸f E) • neighbourTranslation X X'' y =
      neighbourTranslation X X'' y := by
  rw [← star_idem_smul_neighbourTranslation, smul_smul,
    idem_conjClosure_eq_add_star hπ.isConjDisjoint,
    add_mul, idem_mul_star hπ.isConjDisjoint, star_idem_mul_self, zero_add]

/-- The representative `n y + t`, where `n y = neighbourTranslation X X'' y` is attached to residues
`y` at `P` and `t` is the chosen representative of a class in `AwayLatticeQuotient`. -/
def neighbourCosetRep {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E} {κ : PairIndex X X'' → 𝔸f E}
    [DecidableEq X] [DecidableEq X'']
    {hπ : IsSplitSquarefree P (N : E) π} {hκ : IsScalingAtM N β δ κ}
    (a : (X' → P → ZMod N) × AwayLatticeQuotient X' hπ hκ) : PairIndex X X'' × X' → 𝔸f E :=
  neighbourTranslation X X'' a.1 + a.2.out.val

/-- Let `N` be prime, `IsSplitLevel P N`, `IsSplitSquarefree P (N : E) π` and
`IsScalingAtM N β δ κ`. Then `neighbourCosetRep a` lies in `neighbourLattice X' hπ hκ`, the image of
the standard lattice under `latticeUnitary`. -/
lemma neighbourCosetRep_mem_neighbourLattice {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E} [DecidableEq X] [DecidableEq X''] [Fact N.Prime]
    (hP : IsSplitLevel P N) (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    (a : (X' → P → ZMod N) × AwayLatticeQuotient X' hπ hκ) :
      neighbourCosetRep a ∈ neighbourLattice X' hπ hκ :=
  add_mem (neighbourTranslation_mem_neighbourLattice hP hπ hκ a.1) a.2.out.property.1

/-- Let the prime `N` be split as `P` and its conjugate, let `N = π π̄` with `π` a uniformiser on
`P` and a unit elsewhere, and let `κ` be row factors that are `1` above `N` (`IsScalingAtM`). Then
each `z` in `neighbourLattice` differs by a matrix with integral entries (`stdLattice`) from
`neighbourCosetRep (y, q)` for exactly one pair `(y, q)`. Here `y` is a family of residues modulo
`N` at `P`, `q` is a class of lattice elements vanishing above `N` modulo integral ones, and
`neighbourCosetRep (y, q)` is `neighbourTranslation X X'' y` plus the chosen representative of
`q`. -/
lemma existsUnique_sub_neighbourCosetRep_mem {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E} [DecidableEq X] [DecidableEq X''] [Fact N.Prime]
    (hP : IsSplitLevel P N) (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    {z : PairIndex X X'' × X' → 𝔸f E} (hz : z ∈ neighbourLattice X' hπ hκ) :
    ∃! a : (X' → P → ZMod N) × AwayLatticeQuotient X' hπ hκ,
      z - neighbourCosetRep a ∈ stdLattice E (PairIndex X X'' × X') := by
  -- The part of `z` above `N` decides `y`; the part `z'` away from `N` decides the class `q`.
  set e : 𝔸f E := idem (P : Set (FinPlace E)).conjClosure
  have h_above : e • z ∈ neighbourLattice X' hπ hκ := by
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨e • x, smul_mem_stdLattice (idem_mem_Ô _) hx, mulVec_smul ..⟩
  let z' : awayLattice X' hπ hκ :=
    ⟨z - e • z, AddSubgroup.mem_inf.2 ⟨sub_mem hz h_above, sub_idem_smul_mem_vanishingAbove z⟩⟩
  obtain ⟨y₀, hy₀, hy₀_unique⟩ :
      ∃! y : X' → P → ZMod N, e • (-z + neighbourTranslation X X'' y) ∈ stdLattice E _ :=
    existsUnique_add_neighbourTranslation_mem hP hπ hκ (neg_mem hz)
  have h_iff (y : X' → P → ZMod N) (q : AwayLatticeQuotient X' hπ hκ) :
      z - neighbourCosetRep (y, q) ∈ stdLattice E _ ↔
        e • (-z + neighbourTranslation X X'' y) ∈ stdLattice E _ ∧ q = z' := by
    have h_part : e • (z - neighbourCosetRep (y, q)) =
      -(e • (-z + neighbourTranslation X X'' y)) := by
      rw [neighbourCosetRep, smul_sub, smul_add, mem_vanishingAbove.1 q.out.property.2, smul_add,
        smul_neg]
      abel
    have h_split : z - neighbourCosetRep (y, q) =
        -(e • (-z + neighbourTranslation X X'' y)) + (-q.out.val + (z - e • z)) := by
      rw [neighbourCosetRep, smul_add, smul_neg, idem_conjClosure_smul_neighbourTranslation hπ]
      abel
    have h_class : q = z' ↔ -q.out.val + (z - e • z) ∈ stdLattice E _ := by
      conv_lhs => rw [← q.out_eq', QuotientAddGroup.eq]
      rfl
    rw [h_class]
    refine ⟨fun h ↦ ?_, fun ⟨h_int, h_away⟩ ↦ ?_⟩
    · have h_neg : -(e • (-z + neighbourTranslation X X'' y)) ∈ stdLattice E _ :=
        by simpa only [← h_part] using smul_mem_stdLattice (idem_mem_Ô _) h
      rw [h_split, add_mem_cancel_left h_neg] at h
      exact ⟨neg_mem_iff.1 h_neg, h⟩
    · rw [h_split]
      exact add_mem (neg_mem h_int) h_away
  refine ⟨(y₀, z'), (h_iff _ _).2 ⟨hy₀, rfl⟩, fun ⟨y, q⟩ h ↦ ?_⟩
  obtain ⟨hy, hq⟩ := (h_iff y q).1 h
  exact Prod.ext (hy₀_unique y hy) hq

end

end New.Seesaw
