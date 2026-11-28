import Lib.ClassField.Places.DecompositionCompletion
import Lib.General.LinearAlgebra.Eigenvalues
import Lib.General.LinearAlgebra.MatrixNormBounds
import Lib.General.NumberTheory.CoefficientRings
import Lib.PadicComparison.Descent.TestCategory

/-!
# Semisimple representations: conjugacy, continuity, cancellation and stable lattices

This file studies representations `r : G →* GL n k` over an algebraically closed field `k` of
characteristic zero, with semisimplicity expressed by `New.IsTraceNondeg r`. It proves the
Wedderburn–Artin decomposition for maps with semiprime span and Clifford's theorem for
restriction to a normal subgroup. It then shows that equal traces give conjugate
representations, and that continuity follows from the trace. It treats twists by characters
and the cancellation of characters. For continuous ℓ-adic representations of compact groups it
constructs stable lattices over rings of integers `O`.

## Main definitions and results

* `New.IsTraceNondeg.exists_conj_of_trace_eq`: equal traces give conjugate representations.
* `New.IsTraceNondeg.continuous_of_trace`: continuity from the trace.
* `New.IsTraceNondeg.exists_cancel_chars`: if two representations have the same trace after
  subtracting two families of characters with no common member, this common function is the trace
  of a representation.
* `New.eventually_exists_isLatticeIn`: a continuous representation r of a compact group has a
  lattice over every large enough O.

Notions from other files:
* `New.IsTraceNondeg`: Non-degeneracy of the trace form on the span of r(G): any x in that span with
  tr(x r(g)) = 0 for all g is zero.
* `New.CoeffRing`: Rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, where the
  class `ThePrime ℓ` records that ℓ is the fixed prime.

## Relation to the literature

Known; see `Lib.GaloisRep.Pseudocharacter.Pseudorepresentations` for sources.
-/

noncomputable section

/-!
## Wedderburn–Artin, Clifford's theorem and conjugacy from traces

For a map `ρ : G →* B` into a finite-dimensional algebra, semisimplicity is used in the form
`New.HasSemiprimeSpan k ρ`. The Wedderburn–Artin theorem writes the restriction of `ρ` to a normal
subgroup as an algebra map out of a product `New.PiMatrix` of matrix algebras. Maps out of such a
product are compared through the matrix units `New.piMatrixUnit`.

* `New.exists_rep_of_trace`: a tracial form with natural values at the matrix units is a character.
* `New.IsTraceNondeg.comp`: restriction to a normal subgroup stays semisimple (Clifford).
-/

section SemisimpleReps

open Matrix Submodule Fintype ConjAct IsArtinianRing Set Algebra Pi Units LinearMap

namespace New

variable {k G H n N B : Type} [Field k] [Group G] [Fintype n] [DecidableEq n] [Fintype N]
  [DecidableEq N] {m : ℕ} {d : Fin m → ℕ}
  {r : G →* GL n k} [∀ i, NeZero (d i)]

/-! ### Products of matrix algebras and idempotents -/

/-- The product over i of the matrix algebras M_{d_i}(k). -/
abbrev PiMatrix (k : Type*) (d : Fin m → ℕ) : Type _ := ∀ i : Fin m,
  Matrix (Fin (d i)) (Fin (d i)) k

/-- The R-algebra homomorphism from ∏_i M_{m_i}(R) to matrices indexed by the disjoint union of
the m_i, sending a family of square matrices to the block diagonal matrix. -/
@[simps!]
def blockDiagonalAlgHom {R o : Type*} {m : o → Type} [CommRing R] [DecidableEq o] [Fintype o]
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] :
    (∀ i : o, Matrix (m i) (m i) R) →ₐ[R] Matrix (Σ i : o, m i) (Σ i : o, m i) R :=
  AlgHom.mk'
    { toFun := blockDiagonal'
      map_one' := by simp
      map_mul' := by simp [Pi.mul_def]
      map_zero' := by simp
      map_add' := by simp }
    (by simp)

/-- The element of the product of matrix algebras M_{d_i}(k) that is the matrix unit E_ab in
factor i and zero elsewhere; a, b default to 0. -/
abbrev piMatrixUnit (i : Fin m) (a b : Fin (d i) := 0) : PiMatrix k d :=
  Pi.single i (Matrix.single a b 1)

lemma sum_piMatrixUnit : ∑ i : Fin m, ∑ a : Fin (d i), (piMatrixUnit i a a : PiMatrix k d) = 1 := by
  -- in the block `i` only the terms of index `i` are left, and they add up to the identity matrix
  funext i
  simp_all [sum_eq_single i, sum_single_one]

/-- If `A'` has rank at most that of `A`, then `A' = U' * A * U` for some matrices `U`, `U'`. -/
lemma exists_mul_mul_eq_of_rank_le {A : Matrix N N k} {A' : Matrix n n k} (h : A'.rank ≤ A.rank) :
    ∃ (U : Matrix N n k) (U' : Matrix n N k), U' * A * U = A' := by
  -- The range of `A'` embeds by some `J` in the range of `A`. A lift of `J` through `A` gives `U`,
  -- and a left inverse of `J` gives `U'`.
  let R : Submodule k (N → k) := range A.mulVecLin
  let R' : Submodule k (n → k) := range A'.mulVecLin
  obtain ⟨J, J_inj⟩ : ∃ J : R' →ₗ[k] R, Function.Injective J := finrank_le_iff_exists_linearMap.1 h
  obtain ⟨lift, h_lift⟩ : ∃ lift : R' →ₗ[k] N → k, A.mulVecLin.rangeRestrict ∘ₗ lift = J :=
    Module.projective_lifting_property _ J A.mulVecLin.surjective_rangeRestrict
  obtain ⟨L, hL⟩ : ∃ L : (N → k) →ₗ[k] R', L ∘ₗ R.subtype ∘ₗ J = .id :=
    (R.subtype ∘ₗ J).exists_leftInverse_of_injective
      (ker_eq_bot.2 (R.injective_subtype.comp J_inj))
  have left_inv (y : R') : L (A *ᵥ lift y) = y := by
    rw [show A *ᵥ lift y = J y from congrArg Subtype.val (LinearMap.congr_fun h_lift y)]
    exact LinearMap.congr_fun hL y
  refine ⟨(lift ∘ₗ A'.mulVecLin.rangeRestrict).toMatrix', (R'.subtype ∘ₗ L).toMatrix',
    ext_iff_mulVec.2 fun x ↦ ?_⟩
  simp [← mulVec_mulVec, left_inv]

variable {p : Matrix n n k} (f : PiMatrix k d →ₐ[k] Matrix N N k)
  (f' : PiMatrix k d →ₐ[k] Matrix n n k) [Ring B] [Group H] [Algebra k B] [Module.Finite k B]
  (ρ : G →* B)

lemma eq_zero_iff_trace_eq_zero_of_isIdempotentElem [CharZero k] [IsAlgClosed k]
    (hp : IsIdempotentElem p) :
    p = 0 ↔ p.trace = 0 := by
  have h_rank : p.rank = 0 ↔ p = 0 := by
    rw [Matrix.rank, finrank_eq_zero, range_eq_bot, ← toLin'_apply', toLin'.map_eq_zero_iff]
  rw [trace_eq_rank_of_isIdempotentElem hp, Nat.cast_eq_zero, h_rank]

/-- The trace of an idempotent matrix is its rank. In characteristic zero, the matrix is zero
exactly when its trace is zero. -/
lemma trace_of_idempotent [CharZero k] [IsAlgClosed k] (hp : IsIdempotentElem p) :
    p.trace = p.rank ∧ (p = 0 ↔ p.trace = 0) :=
  ⟨trace_eq_rank_of_isIdempotentElem hp, eq_zero_iff_trace_eq_zero_of_isIdempotentElem hp⟩

attribute [local ext] ext_linearMap

omit [Module.Finite k B] in
lemma isIdempotentElem_map_piMatrixUnit (f : PiMatrix k d →ₐ[k] B) (i : Fin m) :
    IsIdempotentElem (f (piMatrixUnit i)) :=
  IsIdempotentElem.map (by simp [IsIdempotentElem, ← Pi.single_mul]) f

omit [∀ i, NeZero (d i)] in
/-- Let `k` be algebraically closed of characteristic zero. If `r = f' ∘ s`, where the image of
`s` spans a finite product of matrix algebras and `f'` is an algebra map to `M_n(k)`, then the
trace form on the span of `r(G)` is non-degenerate. -/
lemma IsTraceNondeg.of_span_piMatrix [CharZero k] [IsAlgClosed k]
    {s : G → PiMatrix k d} (s_span : span k (Set.range s) = ⊤) (hr : ∀ g : G, f' (s g) = r g) :
    IsTraceNondeg r := by
  -- Write `x = f' a`. The left ideal spanned by `a` is spanned by an idempotent `c * a`. Its image
  -- has trace zero, so it is zero (characteristic zero), and `a` is a multiple of `c * a`.
  intro x hx h_trace
  obtain ⟨a, rfl⟩ : ∃ a : PiMatrix k d, f' a = x :=
    mem_span.1 hx f'.range.toSubmodule (range_subset_iff.2 fun g ↦ ⟨s g, hr g⟩)
  obtain ⟨c, idem, b, hb⟩ :
      ∃ c : PiMatrix k d, IsIdempotentElem (c * a) ∧ ∃ b : PiMatrix k d, b * (c * a) = a := by
    simpa [le_antisymm_iff, mem_span_singleton] using
      IsSemisimpleRing.ideal_eq_span_idempotent (PiMatrix k d ∙ a)
  -- The trace of `f' (y * a)` is linear in `y` and vanishes on the spanning family `s`.
  have trace_zero (y : PiMatrix k d) : (f' (y * a)).trace = 0 := by
    have h_lin : traceLinearMap n k k ∘ₗ f'.toLinearMap ∘ₗ .mulRight k a = 0 :=
      LinearMap.ext_on_range s_span fun g ↦ by simp [hr, Matrix.trace_mul_comm _ (f' a), h_trace]
    simpa using LinearMap.congr_fun h_lin y
  have idem_zero : f' (c * a) = 0 :=
    (eq_zero_iff_trace_eq_zero_of_isIdempotentElem (idem.map f')).2 (trace_zero c)
  rw [← hb, map_mul, idem_zero, mul_zero]

/-- Let `k` be an algebraically closed field of characteristic zero, and let `s : G →* PiMatrix k d`
be a homomorphism into the product ∏_i M_{d_i}(k) of matrix algebras whose image spans the product.
Let `τ` be a `k`-linear form on the product with `τ (x * y) = τ (y * x)`, taking a natural number
value on `piMatrixUnit i` (the matrix unit E_00 in factor `i`, zero elsewhere) for each `i`, and
with `τ 1 = card n`. Then there is a representation `r : G →* GL n k` with trace `τ ∘ s` whose trace
form is non-degenerate on the span of the `r g`, meaning any `x` in that span with
`tr (x * r g) = 0` for all `g` is zero. -/
lemma exists_rep_of_trace [CharZero k] [IsAlgClosed k]
    {s : G →* PiMatrix k d} (h_span : span k (Set.range s) = ⊤)
    (τ : PiMatrix k d →ₗ[k] k) (h_comm : ∀ x y : PiMatrix k d, τ (x * y) = τ (y * x))
    (h_nat : ∀ i : Fin m, ∃ c : ℕ, τ (piMatrixUnit i) = c) (h_one : τ 1 = Fintype.card n) :
    ∃ r : G →* GL n k, IsTraceNondeg r ∧ ∀ g : G, (r g).val.trace = τ (s g) := by
  choose c hc using h_nat
  -- A tracial form is a combination of the traces of the blocks, with coefficients `c i`.
  have τ_unit (i : Fin m) (a b : Fin (d i)) :
      τ (piMatrixUnit i a b) = if a = b then (c i : k) else 0 := by
    have h_swap : τ (piMatrixUnit i a * piMatrixUnit i 0 b) =
        τ (piMatrixUnit i 0 b * piMatrixUnit i a) := h_comm _ _
    split_ifs with hab
    · simpa [hab, hc, ← single_mul_left] using h_swap
    · simpa [Ne.symm hab, ← single_mul_left] using h_swap
  have τ_eq (z : PiMatrix k d) : τ z = ∑ i : Fin m, c i * (z i).trace := by
    have τ_lsum : τ = lsum k _ k fun i : Fin m ↦ c i • traceLinearMap (Fin (d i)) k k := by
      ext i a b
      have trace_unit : (Matrix.single a b (1 : k)).trace = if a = b then 1 else 0 := by
        split_ifs with hab <;> simp [hab]
      simpa [-lsum_apply, lsum_piSingle, trace_unit] using τ_unit i a b
    simp [τ_lsum]
  -- Repeat the block `i` along the diagonal `c i` times; the total size is `τ 1 = card n`.
  let ι : Type := Σ p : Σ i : Fin m, Fin (c i), Fin (d p.1)
  let blocks : PiMatrix k d →ₐ[k] Matrix ι ι k :=
    blockDiagonalAlgHom.comp (.pi fun p ↦ evalAlgHom k _ p.1)
  have trace_blocks (z : PiMatrix k d) : (blocks z).trace = τ z := by
    simp +instances [blocks, ι, trace_blockDiagonal', τ_eq, sum_sigma]
  have h_card : card ι = card n := by
    refine Nat.cast_injective (R := k) ?_
    rw [← h_one, ← trace_blocks, map_one, Matrix.trace_one]
  let φ : PiMatrix k d →ₐ[k] Matrix n n k :=
    (reindexAlgEquiv k k (equivOfCardEq h_card)).toAlgHom.comp blocks
  refine ⟨.toHomUnits (.comp φ s), .of_span_piMatrix φ h_span (by simp), fun g ↦ ?_⟩
  simp [φ, -coe_reindexAlgEquiv, trace_blocks]

/-! ### Intertwiners between algebra maps -/

/-- Given algebra maps f, f' from the product of the M_{d_i}(k) to matrix algebras and matrices U_i,
this is the matrix Σ_i Σ_a f(E^i_{a0}) U_i f'(E^i_{0a}). -/
def intertwiner (U : Fin m → Matrix N n k) : Matrix N n k :=
  ∑ i : Fin m, ∑ a : Fin (d i), f (piMatrixUnit i a) * U i * f' (piMatrixUnit i 0 a)

/-- Multiplying `intertwiner f f' U` on the right by the image under `f'` of the matrix unit
E^i_{ab} gives f(E^i_{a0}) U_i f'(E^i_{0b}). -/
lemma intertwiner_mul_map_piMatrixUnit (U : Fin m → Matrix N n k) (i : Fin m) (a b : Fin (d i)) :
    intertwiner f f' U * f' (piMatrixUnit i a b) =
      f (piMatrixUnit i a) * U i * f' (piMatrixUnit i 0 b) := by
  -- Products of matrix units vanish unless block and index match, so one term of the sum is left.
  simp +contextual [intertwiner, ← map_mul, eq_comm, sum_eq_single i,
    sum_eq_single a, Matrix.mul_assoc, Matrix.sum_mul, ← single_mul_left]

/-- Multiplying `intertwiner f f' U` on the left by the image under `f` of the matrix unit
E^i_{ab} gives the same matrix f(E^i_{a0}) U_i f'(E^i_{0b}). -/
lemma map_piMatrixUnit_mul_intertwiner (U : Fin m → Matrix N n k) (i : Fin m) (a b : Fin (d i)) :
    f (piMatrixUnit i a b) * intertwiner f f' U =
      f (piMatrixUnit i a) * U i * f' (piMatrixUnit i 0 b) := by
  -- Products of matrix units vanish unless block and index match, so one term of the sum is left.
  simp +contextual [intertwiner, ← map_mul, ← (f _).mul_assoc (f _), eq_comm, sum_eq_single i,
    sum_eq_single b, Matrix.mul_assoc, ← single_mul_left, Matrix.mul_sum]

/-- Multiplying `intertwiner f f' U` by the image of the matrix unit E^i_{ab}, on the right under
`f'` or on the left under `f`, gives the same matrix f(E^i_{a0}) U_i f'(E^i_{0b}). -/
lemma intertwiner_mul_piMatrixUnit (U : Fin m → Matrix N n k) (i : Fin m) (a b : Fin (d i)) :
    intertwiner f f' U * f' (piMatrixUnit i a b) =
      f (piMatrixUnit i a) * U i * f' (piMatrixUnit i 0 b) ∧
    f (piMatrixUnit i a b) * intertwiner f f' U =
      f (piMatrixUnit i a) * U i * f' (piMatrixUnit i 0 b) :=
  ⟨intertwiner_mul_map_piMatrixUnit f f' U i a b, map_piMatrixUnit_mul_intertwiner f f' U i a b⟩

/-- `intertwiner f f' U` intertwines the two actions of the product of matrix algebras. -/
lemma mul_intertwiner (U : Fin m → Matrix N n k) (z : PiMatrix k d) :
    f z * intertwiner f f' U = intertwiner f f' U * f' z := by
  -- Both sides are linear in `z`: expand `z` in the matrix units.
  rw [← (Pi.basis fun i ↦ stdBasis k (Fin (d i)) (Fin (d i))).sum_repr z]
  simp [sum_prod_type, stdBasis_eq_single, intertwiner_mul_map_piMatrixUnit,
    map_piMatrixUnit_mul_intertwiner, sum_sigma, Matrix.sum_mul, Matrix.mul_sum]

/-- Let `f` and `f'` be matrix representations of a product of matrix algebras. The rank of
`f (piMatrixUnit i)` is the multiplicity of the block `i` in `f`. If each block occurs in `f'` at
most as often as in `f`, then there is an intertwiner `P` from `f'` to `f` with a left inverse. -/
lemma exists_piMatrix_retract
    (h_rank : ∀ i : Fin m, (f' (piMatrixUnit i)).rank ≤ (f (piMatrixUnit i)).rank) :
    ∃ (P : Matrix N n k) (Q : Matrix n N k), Q * P = 1 ∧ ∀ z : PiMatrix k d,
      f z * P = P * f' z := by
  -- The inequality of ranks gives matrices `U i`, `U' i` that cut `f' (piMatrixUnit i)` out of
  -- `f (piMatrixUnit i)`. The sums `intertwiner` made of them are `P` and `Q`.
  have exists_retract (i : Fin m) : ∃ (U : Matrix N n k) (U' : Matrix n N k),
      U' * f (piMatrixUnit i) * U = f' (piMatrixUnit i) := exists_mul_mul_eq_of_rank_le (h_rank i)
  choose U U' retract using exists_retract
  have unit_mul (i : Fin m) (a : Fin (d i)) : (piMatrixUnit i a * piMatrixUnit i *
      piMatrixUnit i 0 a : PiMatrix k d) = piMatrixUnit i a a := by simp [← single_mul_left]
  refine ⟨intertwiner f f' U, intertwiner f' f U', ?_, mul_intertwiner f f' U⟩
  calc intertwiner f' f U' * intertwiner f f' U
    _ = ∑ i : Fin m, ∑ a : Fin (d i),
        f' (piMatrixUnit i a) * (U' i * f (piMatrixUnit i) * U i) * f' (piMatrixUnit i 0 a) := by
      simp [intertwiner.eq_1 f', map_piMatrixUnit_mul_intertwiner, Matrix.mul_assoc, Matrix.sum_mul]
    _ = ∑ i : Fin m, ∑ a : Fin (d i), f' (piMatrixUnit i a a) := by
      simp only [retract, ← map_mul, unit_mul]
    _ = 1 := by simp only [← map_sum, sum_piMatrixUnit, map_one]

variable [IsAlgClosed k]

variable (k) in
/-- The span of ρ(G) in B is semiprime: any x in it with x ρ(g) x = 0 for all g is zero. -/
def HasSemiprimeSpan : Prop := ∀ x ∈ span k (Set.range ρ), (∀ g : G, x * ρ g * x = 0) → x = 0

/-! ### The Wedderburn decomposition and its consequences -/

/-- The Wedderburn–Artin theorem for the span of `ρ ∘ f`. Let `ρ : G →* B` have semiprime span and
let `f : H →* G` have normal range. Then `ρ ∘ f = F ∘ s`, where the image of `s` spans a product of
matrix algebras and the algebra map `F` kills no block of that product. -/
lemma exists_wedderburn [CharZero k] (f : H →* G) (h_semiprime : HasSemiprimeSpan k ρ)
    (h_normal : f.range.Normal) :
    ∃ (b : ℕ) (d : Fin b → ℕ) (_ : ∀ i : Fin b, NeZero (d i))
      (s : H →* PiMatrix k d) (F : PiMatrix k d →ₐ[k] B),
      (∀ i : Fin b, F (piMatrixUnit i) ≠ 0) ∧
      span k (Set.range s) = ⊤ ∧
      ∀ g : H, F (s g) = ρ (f g) := by
  -- The span `A` of `ρ (f H)` is an algebra stable under conjugation by `ρ G`. Its radical is zero,
  -- so by the Wedderburn–Artin theorem it is a product of matrix algebras.
  let A : Subalgebra k B := adjoin k (range (ρ.comp f))
  have A_span : A.toSubmodule = span k (range (ρ.comp f)) := by
    rw [adjoin_eq_span, MonoidHom.mclosure_range, MonoidHom.coe_mrange]
  have A_artinian : IsArtinianRing A := of_finite k A
  let conj (g : G) : B →ₐ[k] B := MulSemiringAction.toAlgHom k B (toConjAct (ρ.toHomUnits g))
  have conj_apply (g y : G) : conj g (ρ y) = ρ (g * y * g⁻¹) := by
    simp [conj, units_smul_def, ← map_inv]
  have conj_mem (g : G) : A ≤ A.comap (conj g) := by
    refine adjoin_le ?_
    rintro - ⟨y, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : H, f z = g * f y * g⁻¹ := h_normal.conj_mem (f y) ⟨y, rfl⟩ g
    exact subset_adjoin ⟨z, by simp [conj_apply, hz]⟩
  let conjA (g : G) : A →+* A := .restrict (conj g) A A (conj_mem g)
  have conjA_surj (g : G) : RingHomSurjective (conjA g⁻¹) :=
    ⟨fun y ↦ ⟨conjA g y, Subtype.ext (show conj g⁻¹ (conj g y.val) = y.val by simp [conj])⟩⟩
  have radical_zero : Ring.jacobson A = ⊥ := by
    -- Otherwise the radical contains a minimal left ideal `I`, which it kills (Nakayama).
    refine (eq_bot_or_exists_atom_le (Ring.jacobson A)).resolve_right fun ⟨I, atom, I_le⟩ ↦ ?_
    have kills : Ring.jacobson A • I = ⊥ :=
      atom.lt_iff.1 (FG.of_finite.jacobson_smul_lt atom.ne_bot)
    refine atom.ne_bot (eq_bot_iff.2 fun x hx ↦ Subtype.ext ?_)
    have x_mem : x.val ∈ span k (range ρ) :=
      span_mono (range_comp_subset_range f ρ) (A_span.le x.property)
    refine h_semiprime x x_mem fun g ↦ ?_
    -- The conjugate `(ρ g)⁻¹ * x * ρ g` lies in the radical, so it kills `x`: `x * ρ g * x = 0`.
    have conj_rad : conjA g⁻¹ x ∈ Ring.jacobson A := Ring.le_comap_jacobson (conjA g⁻¹) (I_le hx)
    have conj_mul : conjA g⁻¹ x * x = 0 := kills.le (smul_mem_smul conj_rad hx)
    simpa [conjA, conj, units_smul_def, mul_assoc, Subtype.ext_iff] using conj_mul
  have A_semisimple : IsSemisimpleRing A := isSemisimpleRing_iff_jacobson.2 radical_zero
  obtain ⟨b, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k A
  -- the same isomorphism, for the instances of `PiMatrix k d`
  replace e : A ≃ₐ[k] PiMatrix k d := by convert! e
  let ρA : H →* A := (ρ.comp f).codRestrict A fun y ↦ subset_adjoin ⟨y, rfl⟩
  have ρA_span : span k (range ρA) = ⊤ :=
    (span_range_subtype_eq_top_iff A.toSubmodule _).2 A_span.symm
  refine ⟨b, d, hd, .comp e ρA, A.val.comp e.symm, ?_, ?_, by simp [ρA]⟩
  · simp [← ext_iff, Matrix.single]
  · have e_surj : Function.Surjective e.toLinearMap := e.surjective
    simpa [Set.range_comp, ← span_image, range_eq_top.2 e_surj] using
      congrArg (Submodule.map e.toLinearMap) ρA_span

/-- If the trace form of `r : G →* GL n k` is non-degenerate on the span of `r(G)`, then this span
is semiprime: any `x` in it with `x * r g * x = 0` for all `g` is zero. This is the hypothesis of
`New.exists_wedderburn`. -/
lemma IsTraceNondeg.hasSemiprimeSpan (h : IsTraceNondeg r) :
    HasSemiprimeSpan k ((coeHom (Matrix n n k)).comp r) := by
  -- If `x * r g * x = 0`, then `x * r g` has square zero, so its trace is zero.
  refine fun x hx h_zero ↦ h x hx fun g ↦ ?_
  have h_sandwich : x * (r g).val * x = 0 := h_zero g
  have h_nilpotent : IsNilpotent (x * (r g).val) :=
    ⟨2, by rw [sq, ← mul_assoc, h_sandwich, zero_mul]⟩
  exact (Matrix.isNilpotent_trace_of_isNilpotent h_nilpotent).eq_zero

/-- Clifford's theorem for the trace form. Let `k` be algebraically closed of characteristic zero.
If the trace form of `r : G →* GL n k` is non-degenerate and `f : H →* G` has normal range, then
the trace form of `r ∘ f` is non-degenerate. -/
lemma IsTraceNondeg.comp [CharZero k]
    (h : IsTraceNondeg r) (f : H →* G) (h_normal : f.range.Normal) :
    IsTraceNondeg (r.comp f) := by
  -- the span of `r (f H)` is the image of a product of matrix algebras
  obtain ⟨b, d, hd, s, F, -, s_span, hF⟩ := exists_wedderburn _ f h.hasSemiprimeSpan h_normal
  exact of_span_piMatrix F s_span hF

/-- Brauer–Nesbitt in the form used here: over an algebraically closed field `k` of characteristic
`0`, let `r` have non-degenerate trace form, `ρ : G →* B` into a finite-dimensional algebra have
semiprime span, and `φ : B →ₐ[k] Matrix n n k`. If `r` and `φ ∘ ρ` have equal traces, then
`r g * P = P * φ (ρ g)` for one invertible `P`. -/
lemma IsTraceNondeg.exists_conj_of_trace_eq [CharZero k]
    (hr : IsTraceNondeg r) (φ : B →ₐ[k] Matrix n n k)
    (hρ : HasSemiprimeSpan k ρ) (h_trace : ∀ g : G, (r g).val.trace = (φ (ρ g)).trace) :
    ∃ P : GL n k, ∀ g : G, (r g).val * P = P * φ (ρ g) := by
  -- Apply `exists_wedderburn` to the pair `(r, ρ)`. It writes `r = F₁ ∘ s` and `φ ∘ ρ = F₂ ∘ s` for
  -- algebra maps `F₁`, `F₂` of equal trace, and `exists_piMatrix_retract` intertwines these.
  let pair : G →* Matrix n n k × B := ((coeHom (Matrix n n k)).comp r).prod ρ
  have pair_semiprime : HasSemiprimeSpan k pair := by
    rintro ⟨x, y⟩ h_mem h_zero
    obtain ⟨x_mem, y_mem⟩ :
        x ∈ span k (range ((coeHom (Matrix n n k)).comp r)) ∧ y ∈ span k (range ρ) :=
      span_prod_le _ _ (span_mono (range_pair_subset ..) h_mem)
    exact Prod.ext (hr.hasSemiprimeSpan x x_mem fun g ↦ congrArg Prod.fst (h_zero g))
      (hρ y y_mem fun g ↦ congrArg Prod.snd (h_zero g))
  obtain ⟨b, d, _, s, F, -, s_span, hF⟩ :=
    exists_wedderburn pair (.id G) pair_semiprime ⟨by simp⟩
  let F₁ : PiMatrix k d →ₐ[k] Matrix n n k := (AlgHom.fst k (Matrix n n k) B).comp F
  let F₂ : PiMatrix k d →ₐ[k] Matrix n n k := φ.comp ((AlgHom.snd k (Matrix n n k) B).comp F)
  have F₁_s (g : G) : F₁ (s g) = r g := congrArg Prod.fst (hF g)
  have F₂_s (g : G) : F₂ (s g) = φ (ρ g) := congrArg (fun z ↦ φ z.2) (hF g)
  -- The traces agree on the spanning family `s`, hence everywhere; an idempotent has its rank as
  -- trace.
  have trace_eq (y : PiMatrix k d) : (F₁ y).trace = (F₂ y).trace := by
    have h_lin :
        traceLinearMap n k k ∘ₗ F₁.toLinearMap = traceLinearMap n k k ∘ₗ F₂.toLinearMap :=
      LinearMap.ext_on_range s_span fun g ↦ by simp [F₁_s, F₂_s, h_trace]
    simpa using LinearMap.congr_fun h_lin y
  have rank_eq (i : Fin b) : (F₂ (piMatrixUnit i)).rank = (F₁ (piMatrixUnit i)).rank := by
    refine Nat.cast_injective (R := k) ?_
    rw [← trace_eq_rank_of_isIdempotentElem (isIdempotentElem_map_piMatrixUnit F₁ i),
      ← trace_eq_rank_of_isIdempotentElem (isIdempotentElem_map_piMatrixUnit F₂ i), trace_eq]
  obtain ⟨P, Q, QP, hP⟩ := exists_piMatrix_retract F₁ F₂ fun i ↦ (rank_eq i).le
  exact ⟨⟨P, Q, mul_eq_one_comm.1 QP, QP⟩, fun g ↦ by rw [← F₁_s, ← F₂_s, hP]⟩

/-! ### Continuity -/

omit [IsAlgClosed k] in
/-- Let k be a field with a ring topology. Let r be a representation of a topological group into
GL_n(k) whose trace form is non-degenerate on the span of its image. If the trace of r is
continuous, then r is continuous. -/
lemma IsTraceNondeg.continuous_of_trace [TopologicalSpace k] [IsTopologicalRing k]
    [TopologicalSpace G] [IsTopologicalGroup G] (h : IsTraceNondeg r)
    (h_trace : Continuous fun g : G ↦ (r g).val.trace) :
    Continuous r := by
  -- On the span `S` of `r G` the trace form is non-degenerate, so each matrix entry is a linear
  -- combination of the functionals `L g : x ↦ trace (x * r g)`. These are continuous along `r`.
  refine .of_coeHom_comp (continuous_matrix fun i j ↦ ?_)
  let S : Submodule k (Matrix n n k) := span k (range fun g : G ↦ (r g).val)
  let L (g : G) : S →ₗ[k] k := (traceLinearMap n k k ∘ₗ .mulRight k (r g).val).domRestrict S
  have ker_le : ⨅ g : G, ker (L g) ≤ ker ((entryLinearMap k k i j).domRestrict S) := by
    intro x hx
    simp [show x.val = 0 from h x x.property (by simpa [L] using hx)]
  have entry_mem : (entryLinearMap k k i j).domRestrict S ∈ span k (range L) :=
    FiniteDimensional.mem_span_of_iInf_ker_le_ker ker_le
  -- The functionals `φ` for which `g ↦ φ (r g)` is continuous form a subspace.
  let along : (S →ₗ[k] k) →ₗ[k] G → k := .pi fun g ↦ .applyₗ ⟨r g, subset_span ⟨g, rfl⟩⟩
  have L_cont (g : G) : Continuous (along (L g)) := by
    -- along `r`, the functional `L g` is `x ↦ trace (r (x * g))`
    refine (h_trace.comp (continuous_mul_const g)).congr fun x ↦ ?_
    simp [along, L]
  exact mem_span.1 entry_mem ((continuousSubmodule ..).comap along) (range_subset_iff.2 L_cont)

end New

end SemisimpleReps

/-!
## Twists by characters and cancellation of characters

* `New.twistByChar`, `New.IsTraceNondeg.twist`: the twist by a character, which keeps nondegeneracy.

The proof of `New.IsTraceNondeg.exists_cancel_chars` decomposes both sides at once through a product
of matrix algebras (`New.exists_wedderburn`). It then shows that the common virtual character has
multiplicities in `ℕ`.
-/

section CharacterCancellation

open Matrix Submodule Pi Fintype Function

variable {k G m n t : Type} [Field k] [Group G] [Fintype m] [DecidableEq m] [Fintype n] [Fintype t]
  (μ : G →* kˣ) (R : G →* GL m k)

/-- For a character μ of G and a matrix representation R over k, the representation g ↦
μ(g)R(g). -/
noncomputable abbrev New.twistByChar : G →* GL m k :=
  MonoidHom.mk' (fun g ↦ μ g • R g) (by aesop (add simp smul_mul_smul))

/-- Twisting by a character `μ` keeps the trace form non-degenerate on the span of the image. -/
lemma New.IsTraceNondeg.twist {R : G →* GL m k} (h : IsTraceNondeg R) (μ : G →* kˣ) :
    IsTraceNondeg (twistByChar μ R) := by
  -- Scaling each `R g` by the unit `μ g` changes neither the span nor which traces vanish.
  intro x hx h_trace
  have twist_apply (g : G) : (twistByChar μ R g).val = (μ g).val • (R g).val := rfl
  have span_le_span : span k (Set.range fun g : G ↦ (twistByChar μ R g).val) ≤
      span k (Set.range fun g : G ↦ (R g).val) :=
    span_le.2 (Set.range_subset_iff.2 fun g ↦ smul_mem _ (μ g).val (subset_span ⟨g, rfl⟩))
  refine h x (span_le_span hx) fun g ↦ ?_
  simpa [twist_apply, smul_eq_zero_iff_eq] using h_trace g

/-- Cancellation of characters over an algebraically closed field of characteristic `0`. Let `r 0`,
`r 1` of dimension `card n + card t` have nondegenerate trace form, and let no character `ψ 0 i`
equal a `ψ 1 j`. If `tr (r i) - ∑ j, ψ i j` is the same function `T` for `i = 0, 1`, then `T` is
the trace of some `s` of dimension `card n` with nondegenerate trace form. -/
lemma New.IsTraceNondeg.exists_cancel_chars [DecidableEq n] [CharZero k] [IsAlgClosed k]
    (h_card : card m = card n + card t) {r : Fin 2 → G →* GL m k}
    (h_nondeg : ∀ i : Fin 2, IsTraceNondeg (r i))
    {ψ : Fin 2 → t → G →* kˣ} (h_ne : ∀ i j : t, ψ 0 i ≠ ψ 1 j) {T : G → k}
    (h_trace : ∀ (i : Fin 2) (g : G), (r i g).val.trace = T g + ∑ j : t, (ψ i j g).val) :
    ∃ s : G →* GL n k, IsTraceNondeg s ∧ ∀ g : G, T g = (s g).val.trace := by
  -- Decompose `ρ = (r i, ψ i)_i` through a product of matrix algebras. The virtual character
  -- `τ = tr (r i) - ∑ ψ i j` is `T` for both `i`; it is the trace of a representation as soon as it
  -- takes natural values on the primitive idempotents `piMatrixUnit c`.
  let ρ : G →* Fin 2 → Matrix m m k × (t → k) :=
    { toFun := fun g i ↦ ((r i g : Matrix m m k), fun j ↦ (ψ i j g : k))
      map_one' := by aesop
      map_mul' := by aesop }
  -- The span of `ρ` has no `x ≠ 0` with all `x * ρ g * x = 0`: test each component.
  have hsemi : HasSemiprimeSpan k ρ := by
    intro x hx h_zero
    funext i
    -- the matrix component of `x i` lies in the span of `r i G`
    have hspan : (x i).fst ∈ span k (Set.range ((Units.coeHom (Matrix m m k)).comp (r i))) := by
      refine span_mono ?_ (apply_mem_span_image_of_mem_span (LinearMap.fst k _ _ ∘ₗ .proj i) hx)
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    have h_mat : (x i).fst = 0 := (h_nondeg i).hasSemiprimeSpan (x i).fst hspan fun g ↦ by
      simpa [ρ] using congrArg (fun y ↦ (y i).fst) (h_zero g)
    -- at `g = 1` the character components give `(x i).snd j ^ 2 = 0`
    have h_chars : (x i).snd = 0 :=
      funext fun j ↦ by simpa [ρ] using congrArg (fun y ↦ (y i).snd j) (h_zero 1)
    exact Prod.ext h_mat h_chars
  -- Wedderburn: `ρ = F ∘ s`, where `s G` spans a product `PiMatrix k d` of matrix algebras and `F`
  -- is an algebra map on it.
  obtain ⟨b, d, hd, s, F, -, hs, hF⟩ : ∃ (b : ℕ) (d : Fin b → ℕ) (_ : ∀ i : Fin b, NeZero (d i))
      (s : G →* PiMatrix k d) (F : PiMatrix k d →ₐ[k] Fin 2 → Matrix m m k × (t → k)),
      (∀ i : Fin b, F (piMatrixUnit i) ≠ 0) ∧ span k (Set.range s) = ⊤ ∧
      ∀ g : G, F (s g) = ρ g :=
    exists_wedderburn ρ (.id G) hsemi ⟨by simp⟩
  replace hF (g : G) (i : Fin 2) :
      F (s g) i = ((r i g : Matrix m m k), fun j ↦ (ψ i j g : k)) := congrFun (hF g) i
  let τ (i : Fin 2) : PiMatrix k d →ₗ[k] k :=
    (traceLinearMap m k k).coprod (-∑ j, .proj j) ∘ₗ .proj i ∘ₗ F.toLinearMap
  have hτ (i : Fin 2) (x : PiMatrix k d) : τ i x = (F x i).fst.trace - ∑ j, (F x i).snd j := by
    simp [τ, sub_eq_add_neg]
  have hτ_eq (i : Fin 2) : τ 0 = τ i :=
    LinearMap.ext_on_range hs fun g ↦ by simp [hτ, hF, h_trace]
  have hcomm (x y : PiMatrix k d) : τ 0 (x * y) = τ 0 (y * x) := by
    simp [hτ, trace_mul_comm (F x 0).fst, mul_comm ((F x 0).snd _)]
  have hnat (c : Fin b) : ∃ N : ℕ, τ 0 (piMatrixUnit c) = N := by
    by_contra hc
    -- If the characters `ψ i` did not see `piMatrixUnit c`, then `τ i (piMatrixUnit c)` would be
    -- the trace of an idempotent, a natural number.
    have hsee (i : Fin 2) : ∃ j : t, (F (piMatrixUnit c) i).snd j ≠ 0 := by
      refine ne_iff.mp fun hzero : (F (piMatrixUnit c) i).snd = 0 ↦ hc ?_
      have h_idem : IsIdempotentElem (F (piMatrixUnit c) i).fst :=
        ((isIdempotentElem_map_piMatrixUnit F c).map (evalAlgHom k _ i)).map (AlgHom.fst k _ _)
      simp [hτ_eq i, hτ, hzero, trace_of_idempotent h_idem]
    choose j hj using hsee
    -- Since `piMatrixUnit c * s g * piMatrixUnit c = s g c 0 0 • piMatrixUnit c`, both `ψ i (j i)`
    -- equal `g ↦ s g c 0 0`.
    have hcorner (g : G) : piMatrixUnit c * (s g - s g c 0 0 • 1) * piMatrixUnit c = 0 := by
      simp [← single_mul_left]
    have hψ (g : G) (i : Fin 2) : (ψ i (j i) g : k) = s g c 0 0 := by
      simpa [hF, hj i, sub_eq_zero] using congrArg (fun y ↦ (F y i).snd (j i)) (hcorner g)
    exact h_ne (j 0) (j 1) (MonoidHom.ext fun g ↦ Units.ext (by simp [hψ]))
  -- A trace form with natural values on the `piMatrixUnit c` is the character of a representation.
  have h_one : τ 0 1 = card n := by simp [hτ, h_card]
  obtain ⟨σ, hσ, htr⟩ := exists_rep_of_trace hs (τ 0) hcomm hnat h_one
  exact ⟨σ, hσ, fun g ↦ by simp [htr, hτ, hF, h_trace]⟩

end CharacterCancellation

/-!
## Stable lattices for ℓ-adic representations of compact groups

* `New.Selmer.IsLatticeIn`: a representation u with values in matrices over O is conjugate to a
  given ℓ-adic representation r.

Auerbach's lemma (`New.exists_auerbach`) gives a basis in which all entries have norm at most 1.
Baire's theorem and compactness put them in one finite extension.
-/

namespace New

open Matrix Filter Set Prod IntermediateField InfiniteGalois Units CoeffRing

variable {ℓ : ℕ} [ThePrime ℓ]
  {n : Type} [Fintype n] [DecidableEq n] {G : Type} [Group G] {O : CoeffRing ℓ}

/-- The `O`-valued representation `u` is a lattice in `r`: there is one `P` in `GL n ℚ̄_ℓ` with
`P⁻¹ * r g * P = u g` for all `g` in `G`, where `u g` is read in `ℚ̄_ℓ` through the inclusion
`O.val.val` of `O` into `ℚ̄_ℓ`. -/
def Selmer.IsLatticeIn (r : G →* GL n (PadicAlgCl ℓ)) (u : G →* Matrix n n O) : Prop :=
  ∃ P : GL n (PadicAlgCl ℓ), ∀ g : G, ↑(P⁻¹ * r g * P) = (u g).map O.val.val

variable {r : G →* GL n (PadicAlgCl ℓ)} {u : G →* Matrix n n O}

/-- If `u` is a lattice in `r`, then for every `g` the characteristic polynomial of `r g` is the
image of that of `u g` under the inclusion `O.val.val` of `O` into `ℚ̄_ℓ`. -/
lemma Selmer.IsLatticeIn.charpoly_eq_map (h_lattice : IsLatticeIn r u) (g : G) :
    (r g).val.charpoly = (u g).charpoly.map O.val.val := by
  obtain ⟨P, hP⟩ : ∃ P : GL n (PadicAlgCl ℓ), ∀ g : G, ↑(P⁻¹ * r g * P) = (u g).map O.val.val :=
    h_lattice
  -- Conjugation by `P` does not change the characteristic polynomial.
  have h_conj : (↑(P⁻¹ * r g * P) : Matrix n n (PadicAlgCl ℓ)).charpoly = (r g).val.charpoly := by
    rw [Units.val_mul, Units.val_mul, coe_units_inv, charpoly_units_conj']
  rw [← h_conj, hP g]
  simpa using charpoly_map (u g) (O.val.val : O.val →+* PadicAlgCl ℓ)

/-- A continuous representation `r : G →* GL n ℚ̄_ℓ` of a compact group `G` has a lattice over
every large enough coefficient ring: for all `O` in `CoeffRing ℓ` that contain some fixed one,
there is a representation `u` with entries in `O` that is a lattice in `r`
(`Selmer.IsLatticeIn r u`, that is, `u` is conjugate to `r` in `GL n ℚ̄_ℓ`). -/
lemma eventually_exists_isLatticeIn [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (hr : Continuous r) :
    ∀ᶠ O : CoeffRing ℓ in atTop, ∃ u : G →* Matrix n n O, Selmer.IsLatticeIn r u := by
  -- Auerbach's lemma conjugates `r` to `s` with entries of norm at most 1. By Baire's theorem the
  -- entries lie in fixed rings `O _` on a nonempty open set; finitely many translates cover `G`.
  -- The family of linear forms `v ↦ (r g v) i`, for `⟨i, g⟩` in the compact space `Σ _ : n, G`.
  let forms (x : Σ _ : n, G) : Module.Dual (PadicAlgCl ℓ) (n → PadicAlgCl ℓ) :=
    .proj x.fst ∘ₗ (r x.snd).val.toLin'
  have h_sep (v : n → PadicAlgCl ℓ) (hv : ∀ x : Σ _ : n, G, forms x v = 0) : v = 0 :=
    funext fun i ↦ by simpa [forms] using hv ⟨i, 1⟩
  have h_forms_cont (v : n → PadicAlgCl ℓ) :
      Continuous fun x : Σ _ : n, G ↦ RingHom.id (PadicAlgCl ℓ) (forms x v) := by
    refine continuous_sigma fun i ↦ ?_
    change Continuous fun g : G ↦ ∑ j : n, (r g).val i j * v j
    fun_prop
  obtain ⟨c, z, hz, h_norm⟩ : ∃ (c : n → Σ _ : n, G)
      (z : Module.Basis n (PadicAlgCl ℓ) (n → PadicAlgCl ℓ)),
      (∀ k : n, z.coord k = forms (c k)) ∧
      ∀ (x : Σ _ : n, G) (k : n), ‖RingHom.id (PadicAlgCl ℓ) (forms x (z k))‖ ≤ 1 :=
    exists_auerbach (Pi.basisFun (PadicAlgCl ℓ) n) forms h_sep (.id _) h_forms_cont
  -- The rows of `P` are the forms chosen by `c`, the columns of `P⁻¹` are the vectors `z k`. An
  -- entry of `s g = P * r g * P⁻¹` is the value of a form of the family at some `z k`.
  have h_mul_eq_one : (of fun k ↦ (r (c k).snd).val (c k).fst) * (of z)ᵀ = 1 :=
    -- the entry `(k, j)` is the form `forms (c k)` at `z j`, the `k`-th coordinate of `z j`
    (ext fun k j ↦ (LinearMap.congr_fun (hz k) (z j)).symm).trans z.toMatrix_self
  let P : GL n (PadicAlgCl ℓ) := mkOfMulEqOne _ _ h_mul_eq_one
  let s : G →* GL n (PadicAlgCl ℓ) := (MulAut.conj P).toMonoidHom.comp r
  have hs_norm (g : G) (p : n × n) : ‖s g p.fst p.snd‖ ≤ 1 := by
    -- the entry is the value of the form `forms ⟨(c p.fst).fst, (c p.fst).snd * g⟩` at `z p.snd`
    simpa [forms] using! h_norm ⟨(c p.fst).fst, (c p.fst).snd * g⟩ p.snd
  have hs_cont (p : n × n) : Continuous fun g : G ↦ s g p.fst p.snd := by
    suffices Continuous fun g : G ↦ (P.val * (r g).val * (P⁻¹).val) p.fst p.snd by
      simpa [s] using this
    fun_prop
  -- The values of an entry lie in the closure of a countable set `D p`, hence in the field that
  -- `D p` generates, as what fixes `D p` fixes its closure; finitely many generators suffice.
  choose D hD_count hD_dense using fun p : n × n ↦ (isCompact_range (hs_cont p)).isSeparable
  have h_gen (g : G) (p : n × n) : ∃ S : Finset (PadicAlgCl ℓ),
      ↑S ⊆ D p ∧ s g p.fst p.snd ∈ adjoin ℚ_[ℓ] (S : Set (PadicAlgCl ℓ)) := by
    refine exists_finset_of_mem_adjoin ((fixedField_fixingSubgroup _).le fun σ ↦ ?_)
    -- `σ` fixes `D p`, hence its closure, which contains `s g p.fst p.snd`
    exact EqOn.closure (fun x hx ↦ σ.prop ⟨x, subset_adjoin ℚ_[ℓ] _ hx⟩) (by fun_prop) continuous_id
      (hD_dense p ⟨g, rfl⟩)
  have h_coeff (S : Finset (PadicAlgCl ℓ)) : ∃ O : CoeffRing ℓ,
      ∀ x ∈ adjoin ℚ_[ℓ] (S : Set (PadicAlgCl ℓ)), ‖x‖ ≤ 1 → x ∈ O.val :=
    CoeffRing.exists_mem_of_mem_adjoin S
  choose O hO using h_coeff
  -- Baire: `G` is the union of countably many closed sets `Z m`, one for each choice `m` of finite
  -- subsets of the `D p`.
  let I (p : n × n) : Set (Finset (PadicAlgCl ℓ)) := {S : Finset (PadicAlgCl ℓ) | ↑S ⊆ D p}
  have h_count (p : n × n) : Countable (I p) := by
    simpa using (countable_ofPred_finite_subset (hD_count p)).preimage Finset.coe_injective
  let Z (m : ∀ p, I p) : Set G := ⋂ p : n × n, {g | s g p.fst p.snd ∈ (O (m p)).val}
  have hZ_closed (m : ∀ p, I p) : IsClosed (Z m) := isClosed_iInter fun p ↦
    -- `O (m p)` is compact, hence closed; `Z m` is an intersection of preimages of it
    .preimage (hs_cont p) <| by
      simpa using (isCompact_range (X := O (m p)) continuous_subtype_val).isClosed
  have hZ_cover : ⋃ m, Z m = univ := by
    refine eq_univ_of_forall fun g ↦ ?_
    choose m hm hg using h_gen g
    exact mem_iUnion.mpr ⟨fun p ↦ ⟨m p, hm p⟩, mem_iInter.mpr fun p ↦ hO _ _ (hg p) (hs_norm g p)⟩
  obtain ⟨m, hm⟩ := nonempty_interior_of_iUnion_of_closed hZ_closed hZ_cover
  obtain ⟨t, ht⟩ : ∃ t : Finset G, ∀ x, ∃ g ∈ t, g * x ∈ Z m := by
    simpa [subset_def] using compact_covered_by_mul_left_translates isCompact_univ hm
  -- Take `O'` above the `O (m p)` and containing the entries of `s g⁻¹`, `g ∈ t`;
  -- then `s x = s g⁻¹ * s (g * x)` has its entries in `O'`.
  filter_upwards [eventually_all.mpr fun p ↦ mem_atTop (O (m p)),
    t.eventually_all.mpr fun g _ ↦
      eventually_all.mpr fun p ↦ CoeffRing.eventually_mem (hs_norm g⁻¹ p)] with O' h_le h_inv
  have h_mem (x : G) (i j : n) : s x i j ∈ O'.val := by
    obtain ⟨g, hg, hgx⟩ := ht x
    simpa using O'.val.matrix.mul_mem (fun i j ↦ h_inv g hg (i, j))
      (fun i j ↦ h_le _ (mem_iInter.mp hgx (i, j))) i j
  -- The entries of `s` as a representation with values in matrices over `O'`.
  let u : G →* Matrix n n O' :=
    { toFun := fun x ↦ of fun i j ↦ ⟨s x i j, h_mem x i j⟩
      map_one' := by simp [← ext_iff, Subtype.ext_iff, one_apply, apply_ite]
      map_mul' x y := by simp [← ext_iff, Subtype.ext_iff, mul_apply] }
  -- `(P⁻¹)⁻¹ * r g * P⁻¹ = s g`, whose entries are those of `u g`
  exact ⟨u, P⁻¹, fun g ↦ by ext i j; simp [u, s]⟩

end New

end
