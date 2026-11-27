import Lib.Weil.Periods.PointLattice
import New.UpperBound.Seesaw.EdgePairEvaluation

/-!
# The shift at a nonzero constant term maps lattices into lattices

`Y` and `Y'` present the spaces `V` and `V'` as a block plus a string, of lengths `s` and `s - 1`,
and `sh = Y.stringMap Y'` is the shift between the strings, of degree `-1`.

* `New.Grading.IsGraded.mulVec_mem_of_homogeneous`: a homogeneous part of a map between graded
  lattices maps the first lattice into the second.
* `New.Grading.exists_mapsTo_lattice_hasDegreeGe_sub_smul_stringMap`: let the constant term of
  `t ⊗ f` at `sh` not vanish at `(x, x')`, with `f` fixed by the Heisenberg operators of
  `b Ô ^ (ι' × ι)`; then modulo degree at least `0` the multiple `(b̄ / α) sh` maps the lattice of
  `x` into that of `x'`.
* `New.Grading.smul_map_stringMapFin_latticePlus_le`: at graded points this multiple of `sh` maps
  `Λ'⁺` of the first point into `Λ'⁻` of the second.

Notions from other files:
* `Y.gradeOf` is the grade of a basis index: `0` on the block `X` and `s - 1 - 2 i` on the string
  vector `i`; `HasDegreeGe w' w d A` says that the entry `(p, q)` of `A` is `0` if
  `w' p < w q + d`.
* `V.lattice g`, for a finite point `g`, is the lattice `g Λ` in rational coordinates;
  `Y.latticePlus g` is its projection `Λ'⁺` to `X^⊥` and `Y.latticeMinus g` is its intersection
  `Λ'⁻` with `X^⊥`.
* `Y.mapDegree Y'.gradeOf (p, q)` is the degree of the entry `(p, q)`, and `Y.constTerm` is the
  constant term along the entries of positive degree.
* `matrixToVec` and `vecToMatrix` pass between matrices and vectors indexed by `ι' × ι`.
* `Y.IsGraded L` says that the lattice `L` contains each graded part of each of its vectors.
* `Y.constTermAtStringMap Y' μ F x x'` is the constant term at `sh`, for the weights `Y'.gradeOf`,
  of the Weil translate of `F` by `(x, x')`, twisted by the characters `μ`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

open Matrix Pointwise Kronecker

noncomputable section

namespace New

open Seesaw Space WeilData

variable {E X X' ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [DecidableEq X']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  {Y : Grading V N X s} {Y' : Grading V' N X' (s - 1)}

/-- Let `D` be a Witt decomposition of the Hermitian space `V` into two dual isotropic subspaces,
with bases indexed by `p`, and an isometric image of `V'` orthogonal to both. The columns of `D.k`
are the basis of the first isotropic subspace, and `D.isotropicBasisFin` is this basis over the
finite adeles, written in lattice coordinates. Its adjoint is `D.kᴴ * V.J * V.xFin`. -/
lemma Space.Splitting.conjTranspose_isotropicBasisFin {p : Type} [Fintype p] [DecidableEq p]
    (D : V.Splitting V' p) : D.isotropicBasisFinᴴ = (D.kᴴ * V.J).map (algebraMap E (𝔸f E)) *
      V.xFin.val := by
  -- By definition `D.isotropicBasisFin` is the finite component of the product `V.x⁻¹ * D.k` over
  -- the adeles.
  have h_frame : D.isotropicBasisFin = V.xFin⁻¹.val * D.k.map (algebraMap E (𝔸f E)) :=
    Matrix.map_mul (f := RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))
  have h_dual : V.xFin⁻¹.valᴴ = V.J.map (algebraMap E (𝔸f E)) * V.xFin.val := by
    rw [← gram_inv_of_gram_eq gram_xFin, mul_one, Units.inv_mul_cancel_right]
  rw [h_frame, conjTranspose_mul, h_dual, Matrix.map_mul, Matrix.mul_assoc,
    conjTranspose_map _ fun a ↦ (star_algebraMap_finAdele a).symm]

namespace Grading

omit [Fintype X] in
/-- Let the bases of `V` and `V'` carry the integer grades `Y.gradeOf` and `Y'.gradeOf`, and let `W`
map a lattice `L` into a lattice `L'`, both graded. Then the part `T` of `W` of degree `e`, whose
entry `(p, q)` is that of `W` if the grade of `p` is that of `q` plus `e` and is `0` otherwise, also
maps `L` into `L'`. -/
lemma IsGraded.mulVec_mem_of_homogeneous {L : Submodule (Ô E) (ι → 𝔸f E)}
    {L' : Submodule (Ô E) (ι' → 𝔸f E)} (hL : Y.IsGraded L) (hL' : Y'.IsGraded L')
    {W T : Matrix ι' ι (𝔸f E)} {e : ℤ} (hW : ∀ y ∈ L, W *ᵥ y ∈ L')
    (hT : ∀ (p : ι') (q : ι), T p q = if Y'.gradeOf p = Y.gradeOf q + e then W p q else 0)
    {y : ι → 𝔸f E} (hy : y ∈ L) : T *ᵥ y ∈ L' := by
  -- `T` is the sum over the grades `d` of the part of `W` from grade `d` to grade `d + e`.
  have h_sum : T *ᵥ y = ∑ d ∈ (Finset.univ.image Y.gradeOf : Finset ℤ),
      Y'.gradeProj (d + e) (W *ᵥ Y.gradeProj d y) := by
    simp only [gradeProj, mulVecLin_apply, mulVec_mulVec, ← Matrix.sum_mulVec]
    congr 1
    ext p q : 2
    -- Only the summand of the grade of `q` contributes to the entry `(p, q)`.
    simp [Matrix.sum_apply, hT, ← Matrix.mul_assoc]
  rw [h_sum]
  exact L'.sum_mem fun d _ ↦ hL' (d + e) _ (hW _ (hL d y hy))

omit [Fintype X] in
/-- The shift `Y.stringMap Y'` from the string of basis vectors of `V` to that of `V'` is
homogeneous of degree `-1`: its entry `(p, q)` vanishes unless the grade of `p` is one less than
that of `q`. -/
lemma stringMap_eq_zero_of_gradeOf_ne {p : ι'} {q : ι} (h_grade : Y'.gradeOf p ≠ Y.gradeOf q + -1) :
    Y.stringMap Y' p q = 0 := by
  obtain ⟨b | b, rfl⟩ := Y'.indexEquiv.surjective p
  · obtain ⟨a | a, rfl⟩ := Y.indexEquiv.surjective q <;> simp [stringMap]
  obtain ⟨a | a, rfl⟩ := Y.indexEquiv.surjective q
  · simp [stringMap]
  have h_ne : b.1 ≠ a.1 := by
    simp only [gradeOf, Equiv.symm_apply_apply, Sum.elim_inr] at h_grade
    omega
  simp [stringMap, h_ne]

/-- The finite part `Y.stringMapFin Y'` of the shift between the strings kills the block `X`, so it
does not change under composition with the projection `Y.stringProj` to the span `X^⊥` of the string
of `V`. -/
lemma stringMapFin_stringProj (y : ι → 𝔸f E) :
    Y.stringMapFin Y' (Y.stringProj y) = Y.stringMapFin Y' y := by
  funext p
  have h_inl (a : X) : Y.stringMap Y' p (Y.indexEquiv (.inl a)) = 0 := by
    obtain ⟨b | b, rfl⟩ := Y'.indexEquiv.surjective p <;> simp [stringMap]
  simp [stringMapFin, mulVec, dotProduct, reindex_equiv Y.indexEquiv, stringProj_apply_inr, h_inl]

/-- The finite part `Y.stringMapFin Y'` of the shift between the strings takes its values in the
span `X'^⊥` of the string of `V'`, so they are fixed by the projection `Y'.stringProj` to it. -/
lemma stringProj_stringMapFin (y : ι → 𝔸f E) :
    Y'.stringProj (Y.stringMapFin Y' y) = Y.stringMapFin Y' y := by
  simp [stringProj_eq_self_iff, stringMapFin, stringMap, mulVec, dotProduct,
    reindex_equiv Y.indexEquiv]

/-- Let `r` be a finite point of the Bessel group of the grading `Y` of `V`, that is, `r` fixes each
string vector of grade `≥ 0` up to vectors of higher grade. Then the matrix of `r` in rational
coordinates does not lower grades. -/
lemma hasDegreeGe_zero_ratCoordMatrixFin {r : Gf E ι} (hr : r ∈ Y.besselFin) :
    HasDegreeGe Y.gradeOf Y.gradeOf 0 (V.ratCoordMatrixFin r) := fun p q h ↦ by
  -- This is the finite component of the same fact for the adelic point `(1, r)`.
  have h_mem : ((1, r) : G E ε) ∈ Y.besselGroup := hr
  simpa [ratCoordMatrix_inr] using
    congrArg Prod.snd (Y.hasDegreeGe_zero_of_mem_besselGroup h_mem p q h)

/-- The Bessel group of a grading fixes each string vector of grade `≥ 0` up to vectors of higher
grade. If `W` agrees with `c` times the finite part of the shift up to a matrix that does not lower
grades, then so does `r' W r`, read in rational coordinates. Here `r ∈ Y.besselFin` and
`r' ∈ Y'.besselFin` are finite points of the Bessel groups of `Y` and `Y'`. -/
lemma hasDegreeGe_zero_mul_mul_sub [Fintype X'] {W : Matrix ι' ι (𝔸f E)} {c : 𝔸f E}
    (hW : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (W - c • (Y.stringMap Y').map Prod.snd))
    {r : Gf E ι} (hr : r ∈ Y.besselFin) {r' : Gf E ι'} (hr' : r' ∈ Y'.besselFin) :
    HasDegreeGe Y'.gradeOf Y.gradeOf 0
      (V'.ratCoordMatrixFin r' * (W * V.ratCoordMatrixFin r) -
        c • (Y.stringMap Y').map Prod.snd) := by
  set sh : Matrix ι' ι (𝔸f E) := (Y.stringMap Y').map Prod.snd
  set A : Matrix ι ι (𝔸f E) := V.ratCoordMatrixFin r
  set A' : Matrix ι' ι' (𝔸f E) := V'.ratCoordMatrixFin r'
  have h_fixed : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (A' * (sh * A) - sh) := fun p q h ↦ by
    simpa [ratCoordMatrix_inr, mul_apply, Prod.snd_sum, sh, A, A'] using
      congrArg Prod.snd (Y.hasDegreeGe_zero_mul_stringMap_mul_sub hr hr' p q h)
  have h_split : A' * (W * A) - c • sh = A' * ((W - c • sh) * A) + c • (A' * (sh * A) - sh) := by
    simp [Matrix.sub_mul, Matrix.mul_sub, smul_sub]
  -- Degrees add under multiplication, so all three factors together have degree at least `0`.
  have h_error : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (A' * ((W - c • sh) * A)) :=
    (hasDegreeGe_zero_ratCoordMatrixFin hr').mul
      (hW.mul (hasDegreeGe_zero_ratCoordMatrixFin hr) (zero_add 0).ge) (zero_add 0).ge
  intro p q h
  rw [h_split, Matrix.add_apply, Matrix.smul_apply, h_error p q h, h_fixed p q h, smul_zero,
    add_zero]

variable [WeilData E]

omit [Fintype X] in
/-- Let `D` be a Witt decomposition of `Hom (V, V')` with isotropic basis `D.k` indexed by the
entries of positive degree and with complement `V₀`. The zero term
`D.zeroTerm : 𝒮 (Hom (V, V')) → 𝒮 V₀` averages theta functions along `D.k`, and `zeroTermFin D F` is
the zero term of `v ⊗ F` for a fixed translate `v` of the Fock vacuum. Assume that the constant term
is the theta value on `V₀` of the zero term. Let `t` be a vector of the real Fock space of
`Hom (V, V')`, `f` a vector of the Weil representation `𝒮 (V.hom V')` and
`t ⊗ f = (V.hom V').integrated t f`. Translate `t ⊗ f` by adelic points `(x, x')` of `U(V) × U(V')`
in the Weil representation twisted by the characters `μ ι`, `μ ι'` of `[U(1)]`. If the constant term
of this translate at `sh`, `Y.constTermAtStringMap Y' μ (t ⊗ f) x x'`, is nonzero, then
`zeroTermFin D` does not kill the translate of `f` by the finite part of `(x, x')` and then by the
finite Heisenberg operator of `sh`. -/
lemma zeroTermFin_finHeisenbergOp_stringMap_ne_zero {μ : (n : Type) → [Fintype n] → AutChar E}
    {t : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns ε ε')))}
    {f : 𝒮 (V.hom V')} {x : G E ε} {x' : G E ε'}
    {m : ℕ} {s₀ : Fin m → ℤˣ} {V₀ : Space E (Fin m) s₀}
    {D : (V.hom V').Splitting V₀ {r : ι' × ι // 0 < Y.mapDegree Y'.gradeOf r}}
    (h_theta : ∀ (F : 𝒮 (V.hom V')) (w : Matrix ι' ι (𝔸 E)),
      Y.constTerm Y'.gradeOf F w = V₀.θ (D.zeroTerm (homHeisenbergOp w F)))
    (h_ne : Y.constTermAtStringMap Y' μ ((V.hom V').integrated t f) x x' ≠ 0) :
    zeroTermFin D ((V.hom V').finHeisenbergOp (finCoord (V.homAtPoint V' (Y.stringMap Y')))
      ((V.hom V').ω (1, (G.onHom (x, x')).2) f)) ≠ 0 := by
  let v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns ε ε'))) :=
    Fock.realWeil (Fock.blockU (G.onHom (x, x')).1) t
  let y : ι' × ι → 𝔸 E := V.homAtPoint V' (Y.stringMap Y')
  -- Each operation acts separately on the real and on the finite factor of a pure tensor.
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E s₀)),
      ∀ F : 𝒮 (V.hom V'), D.zeroTerm ((V.hom V').ϱ y ((V.hom V').integrated v F)) =
        V₀.integrated t₀ (zeroTermFin D ((V.hom V').finHeisenbergOp (finCoord y) F)) :=
    exists_zeroTerm_rho_integrated_eq D y v
  have h_omega : (V.hom V').ω (G.onHom (x, x')) ((V.hom V').integrated t f) =
      (V.hom V').integrated v ((V.hom V').ω (1, (G.onHom (x, x')).2) f) := by
    simp [omega_integrated, v]
  intro h_zero
  have h_zeroTerm :
      D.zeroTerm ((V.hom V').ϱ y ((V.hom V').ω (G.onHom (x, x')) ((V.hom V').integrated t f))) =
        0 := by
    rw [h_omega, ht₀, h_zero, map_zero]
  -- The characters only contribute a scalar factor, and the theta value of `0` is `0`.
  apply h_ne
  simp [h_theta, pairWeil_apply, h_zeroTerm, y]

/-- Let `M` be an adelic matrix and `l` a finite vector. Subtract `c g l`, where `g` is the finite
part of `(x, x')` acting on `Hom (V, V')`, from the finite coordinates of the point of
`Hom (V, V')` given by `M`. In rational coordinates the difference is the finite part of `M`
divided by the idele `α` of the Weil data, less `c` times the product of `V'.xFin x'.2`, the matrix
of `l` and the inverse of `V.xFin x.2`. -/
lemma xFin_mulVec_finCoord_homAtPoint_sub {x : G E ε} {x' : G E ε'} (M : Matrix ι' ι (𝔸 E))
    (l : ι' × ι → 𝔸f E) (c : 𝔸f E) :
    (V.hom V').xFin.val *ᵥ (finCoord (V.homAtPoint V' M) -
        (c • ((G.onHom (x, x')).2 : Matrix (ι' × ι) (ι' × ι) (𝔸f E))) *ᵥ l) =
      matrixToVec ((α : (𝔸f E)ˣ)⁻¹.val • M.map Prod.snd -
        c • ((V'.xFin * x'.2.val).val * vecToMatrix l * (V.xFin * x.2.val)⁻¹.val)) := by
  have h_xFin : (V.hom V').xFin.val = V'.xFin.val ⊗ₖ V.xFin⁻¹.valᵀ := rfl
  have h_cancel (A : Matrix ι' ι (𝔸f E)) : V'.xFin.val * (V'.xFin⁻¹.val * A) = A := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [h_xFin, finCoord_homAtPoint, G.onHom_snd, smul_mulVec, mulVec_sub, mulVec_smul]
  simp only [kronecker_mulVec_eq_matrixToVec, vecToMatrix_matrixToVec]
  funext pq
  -- `coe_units_inv` would turn the inverse units into matrix inverses and hide the cancellations.
  simp [matrixToVec, Matrix.mul_assoc, -coe_units_inv, h_cancel]

/-- Let `t` be a vector of the real Fock space of `Hom (V, V')`, let `f ∈ 𝒮 (V.hom V')` and
`t ⊗ f = (V.hom V').integrated t f`. Translate `t ⊗ f` by adelic points `(x, x')` of `U(V) × U(V')`
in the Weil representation twisted by the characters `μ ι`, `μ ι'` of `[U(1)]`. Let the constant
term of this translate at `sh` be nonzero, and let `f` be fixed by the finite Heisenberg operators
of `b Ô ^ (ι' × ι)`. Then some matrix `W` maps the lattice `V.lattice x.2` into `V'.lattice x'.2`
and agrees with `b̄ / α` times the finite part of `sh` up to a matrix that does not lower grades.
Here `α` is the finite idele of `WeilData E` that makes `Ô` self-dual. -/
lemma exists_mapsTo_lattice_hasDegreeGe_sub_smul_stringMap [Fintype X']
    {μ : (n : Type) → [Fintype n] → AutChar E}
    {t : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns ε ε')))}
    {f : 𝒮 (V.hom V')} {x : G E ε} {x' : G E ε'}
    (h_ne : Y.constTermAtStringMap Y' μ ((V.hom V').integrated t f) x x' ≠ 0) (b : (𝔸f E)ˣ)
    (hf : ∀ y ∈ stdLattice E (ι' × ι), finHeisenbergOp (V.hom V') (b.val • y) f = f) :
    ∃ W : Matrix ι' ι (𝔸f E), (∀ y ∈ V.lattice x.2, W *ᵥ y ∈ V'.lattice x'.2) ∧
      HasDegreeGe Y'.gradeOf Y.gradeOf 0
        (W - (star b / α).val • (Y.stringMap Y').map Prod.snd) := by
  -- Take a splitting `D` along the maps of positive degree. The constant term is a theta value of
  -- the zero term, so the finite zero term does not vanish at `sh`, and `sh` lies in its support.
  obtain ⟨m, s₀, V₀, D, -, h_proj, h_theta⟩ :
      ∃ (m : ℕ) (s₀ : Fin m → ℤˣ) (V₀ : Space E (Fin m) s₀)
        (D : (V.hom V').Splitting V₀ {r : ι' × ι // 0 < Y.mapDegree Y'.gradeOf r}),
        D.k = inclMatrix E Subtype.val ∧
        (V.hom V').J⁻¹ * (D.k * (D.kᴴ * (V.hom V').J)) =
          diagonal (fun r : ι' × ι ↦ if Y.mapDegree Y'.gradeOf r < 0 then 1 else 0) ∧
        ∀ (F : 𝒮 (V.hom V')) (w : Matrix ι' ι (𝔸 E)),
          Y.constTerm Y'.gradeOf F w = V₀.θ (D.zeroTerm (homHeisenbergOp w F)) :=
    Y.exists_splitting_constTerm Y'.gradeOf_stringReversal
  let g : Gf E (ι' × ι) := (G.onHom (x, x')).2
  have h_period (y : ι' × ι → 𝔸f E) (hy : y ∈ stdLattice E (ι' × ι)) :
      (V.hom V').finHeisenbergOp ((b.val • g.val.val) *ᵥ y) ((V.hom V').ω (1, g) f) =
        (V.hom V').ω (1, g) f := by
    simpa [omega_finHeisenbergOp, smul_mulVec, mulVec_smul] using
      congrArg ((V.hom V').ω (1, g)) (hf y hy)
  have h_unitary : (b.val • g.val.val) * (star b⁻¹.val • g.val.val)ᴴ = 1 := by
    simp [← U.inv_val_eq_conjTranspose, smul_smul]
  -- The finite coordinates `z` of `sh` are, up to the orthogonal of `D.k`, a vector `b̄⁻¹ g l` of
  -- the dual lattice. In rational coordinates `l` becomes the matrix `W`.
  let z : ι' × ι → 𝔸f E := finCoord (V.homAtPoint V' (Y.stringMap Y'))
  have h_zeroTerm : zeroTermFin D ((V.hom V').finHeisenbergOp z ((V.hom V').ω (1, g) f)) ≠ 0 :=
    zeroTermFin_finHeisenbergOp_stringMap_ne_zero h_theta h_ne
  obtain ⟨l, hl, h_supp⟩ :
      ∃ l ∈ stdLattice E (ι' × ι), D.isotropicBasisFinᴴ *ᵥ (z - (star b⁻¹.val • g.val.val) *ᵥ l) =
        0 :=
    exists_sub_orthogonal_of_zeroTermFin_ne_zero D _ _ h_zeroTerm h_unitary h_period
  set sh : Matrix ι' ι (𝔸f E) := (Y.stringMap Y').map Prod.snd
  let W : Matrix ι' ι (𝔸f E) := (V'.xFin * x'.2.val).val * vecToMatrix l * (V.xFin * x.2.val)⁻¹.val
  have h_rat : (V.hom V').xFin.val *ᵥ (z - (star b⁻¹.val • g.val.val) *ᵥ l) =
      matrixToVec ((α : (𝔸f E)ˣ)⁻¹.val • sh - star b⁻¹.val • W) :=
    xFin_mulVec_finCoord_homAtPoint_sub (Y.stringMap Y') l (star b⁻¹.val)
  -- Applying `J⁻¹ * D.k` to `h_supp` keeps the entries of negative degree.
  have h_neg :
      (diagonal fun r : ι' × ι ↦ if Y.mapDegree Y'.gradeOf r < 0 then (1 : E) else 0).map
        (algebraMap E (𝔸f E)) *ᵥ matrixToVec ((α : (𝔸f E)ˣ)⁻¹.val • sh - star b⁻¹.val • W) = 0 := by
    rw [D.conjTranspose_isotropicBasisFin, ← mulVec_mulVec, h_rat] at h_supp
    rw [← h_proj, Matrix.map_mul, Matrix.map_mul, ← mulVec_mulVec, ← mulVec_mulVec, h_supp,
      mulVec_zero, mulVec_zero]
  refine ⟨W, fun y hy ↦ ?_, fun p q h_deg ↦ ?_⟩
  · rw [mem_lattice, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec, Units.inv_mul, one_mulVec]
    exact IsIntMatrix.mulVec (fun p q ↦ hl (p, q)) hy
  · have h_entry : (α : (𝔸f E)ˣ)⁻¹.val * sh p q = star b⁻¹.val * W p q := by
      have h_lt : Y'.gradeOf p < Y.gradeOf q := by lia
      simpa [mulVec_diagonal, mapDegree, h_lt, matrixToVec, sub_eq_zero] using congrFun h_neg (p, q)
    calc (W - (star b / α).val • sh) p q
      _ = W p q - (star b).val * ((α : (𝔸f E)ˣ)⁻¹.val * sh p q) := by
        simp [div_eq_mul_inv, mul_assoc]
      _ = 0 := by simp [h_entry, ← mul_assoc, ← star_mul]

/-- The gradings `Y`, `Y'` split the bases of the Hermitian spaces `V`, `V'` (of signs `ε`, `ε'` at
the infinite places) into blocks `X`, `X'` of grade `0` and strings of `s` and `s - 1` vectors,
which span `X^⊥` and `X'^⊥`. The shift `sh = Y.stringMap Y'`, with finite part `Y.stringMapFin Y'`,
is the rational map `V → V'` that kills `X` and sends each string vector to a multiple of the one
with the same number; it lowers grades by one. The constant term at `sh` of a vector of the Weil
representation `𝒮 (V.hom V')` is the mean of its theta function, translated by `sh`, over the adelic
maps `V → V'` that raise grades, modulo rational ones.

Let `t` be a vector of the real Fock space of `Hom (V, V')`, whose signs are the products of those
of `ε` and `ε'`, let `f ∈ 𝒮 (V.hom V')` and `t ⊗ f = (V.hom V').integrated t f`. Translate `t ⊗ f`
by adelic points `(x, x')` of `U(V) × U(V')` in the Weil representation twisted by the characters
`μ ι`, `μ ι'` of `[U(1)]`. Let the constant term of this translate at `sh` be nonzero, and let `f`
be fixed by the finite Heisenberg operators of `b Ô ^ (ι' × ι)`. Let `r`, `r'` be finite points of
the Bessel groups (which fix each string vector of grade `≥ 0` up to vectors of higher grade) such
that the lattices of `r x.2` and `r' x'.2` are graded, that is, contain the part in each grade of
each of their vectors. Then `b̄ / α` times the finite part of `sh` maps the projection to `X^⊥` of
the lattice of `r x.2` into the intersection with `X'^⊥` of the lattice of `r' x'.2`. Here `α` is
the finite idele of `WeilData E` that makes `Ô` self-dual. -/
lemma smul_map_stringMapFin_latticePlus_le [Fintype X'] {μ : (n : Type) → [Fintype n] → AutChar E}
    {t : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns ε ε')))}
    {f : 𝒮 (V.hom V')} {x : G E ε} {x' : G E ε'}
    (h_ne : Y.constTermAtStringMap Y' μ ((V.hom V').integrated t f) x x' ≠ 0) (b : (𝔸f E)ˣ)
    (hf : ∀ y ∈ stdLattice E (ι' × ι), finHeisenbergOp (V.hom V') (b.val • y) f = f)
    {r : Gf E ι} (hr : r ∈ Y.besselFin) (h_graded : Y.IsGraded (V.lattice (r * x.2)))
    {r' : Gf E ι'} (hr' : r' ∈ Y'.besselFin) (h_graded' : Y'.IsGraded (V'.lattice (r' * x'.2))) :
    (star b / α).val • (Y.latticePlus (r * x.2)).map ((Y.stringMapFin Y').restrictScalars (Ô E)) ≤
      Y'.latticeMinus (r' * x'.2) := by
  set c : 𝔸f E := (star b / α).val
  obtain ⟨W, hW_mem, hW_deg⟩ : ∃ W : Matrix ι' ι (𝔸f E),
      (∀ y ∈ V.lattice x.2, W *ᵥ y ∈ V'.lattice x'.2) ∧
      HasDegreeGe Y'.gradeOf Y.gradeOf 0 (W - c • (Y.stringMap Y').map Prod.snd) :=
    exists_mapsTo_lattice_hasDegreeGe_sub_smul_stringMap h_ne b hf
  -- Move `W` to the graded points; `c sh` is its part of degree `-1`.
  let W₀ : Matrix ι' ι (𝔸f E) := V'.ratCoordMatrixFin r' * (W * V.ratCoordMatrixFin r⁻¹)
  have hW₀_mem : ∀ y ∈ V.lattice (r * x.2), W₀ *ᵥ y ∈ V'.lattice (r' * x'.2) := fun y hy ↦ by
    rw [← mulVec_mem_lattice_mul (g := r⁻¹), inv_mul_cancel_left] at hy
    rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_mem_lattice_mul]
    exact hW_mem _ hy
  have hW₀_deg : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (W₀ - c • (Y.stringMap Y').map Prod.snd) :=
    hasDegreeGe_zero_mul_mul_sub hW_deg (inv_mem hr) hr'
  have h_part (p : ι') (q : ι) : (c • (Y.stringMap Y').map Prod.snd) p q =
      if Y'.gradeOf p = Y.gradeOf q + -1 then W₀ p q else 0 := by
    split_ifs with h
    · exact (sub_eq_zero.1 (hW₀_deg p q (by lia))).symm
    · simp [stringMap_eq_zero_of_gradeOf_ne h]
  -- An element of the left side is `c sh y'` with `y'` the projection of a lattice vector `y`.
  rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  change c • Y.stringMapFin Y' (Y.stringProj y) ∈ Y'.latticeMinus (r' * x'.2)
  have h_mem : (c • (Y.stringMap Y').map Prod.snd) *ᵥ y ∈ V'.lattice (r' * x'.2) :=
    h_graded.mulVec_mem_of_homogeneous h_graded' hW₀_mem h_part hy
  rw [stringMapFin_stringProj, mem_latticeMinus, map_smul, stringProj_stringMapFin]
  exact ⟨by simpa [stringMapFin, smul_mulVec] using h_mem, rfl⟩

end Grading

end New

end
