import New.UpperBound.Divisibility.MarkedPrimes
import New.UpperBound.ElementaryDivisors.ElementaryDivisorTheorem

/-!
# Elementary divisor bound for the scaled Hecke operator via edges

Let `l` be a place of a marked set `Λ` above a prime `p`. This file carries the theorem on
elementary divisors, `New.FrobeniusCycle.elementary_divisors`, for the edge Hecke operator over
to the normalised Hecke operator `New.Data.IsMarked.scaledHeckeOperator` at `l`. It assumes a
Frobenius cycle that matches the places above `l`. The proof identifies the two operators in
four steps:
* The edges: the cosets of the Hecke operator at `l` are indexed by edges. An edge is determined
  by its origin and its basis change there, because the rational points act freely on the cosets
  of the level (`New.Columns.HeckeEdges.eq_of_origin_eq_of_mem_parahoric`).
* The variables: at an a-place that induces `l` or its conjugate, an edge acts by letter matrices
  and powers of `p` (`New.Columns.kroneckerPi_symPowMatrix_eq_letterRep`).
* The weight space splits into monomials at these a-places and a factor on which the edges act
  integrally (`New.Columns.exists_weylIndex_equiv`, `New.Columns.exists_schur_eq_map`).
* The module: integral source forms are families of integral vectors indexed by the classes
  (`New.Columns.range_sourceFormOfValues`).

## Main definitions and results

* `New.Columns.isOntoUpToColength_scaledHeckeOperator_of_frobeniusCycle`: given a Frobenius cycle
  that matches the places above `l`, the operator is an edge Hecke operator, so the bound of the
  theorem holds for it.
* `New.Columns.HeckeEdges.heckeSplit_apply_rep`: The Hecke operator as a sum over edges.

Notions from other files:
* `New.IsOntoUpToColength`: The endomorphism `y` keeps `M`, and for some natural number `i ≤ c` the
  sum `y (M) + p ^ j₀ • M` has index dividing `p ^ i` in `M` (in the sense of `New.ColengthDvd`):
  `y` is onto on `M` modulo `p ^ j₀` up to an index `p ^ i`.
* `New.Data.IsMarked`: a marked set `Λ` of primes of `E` is disjoint from its complex conjugate,
  each of its primes is induced by an a-place (an element of `D.aPlaces`), `p` is exceptional
  (`New.Data.IsExceptional`), and `p` is below `D.x₁` and not split in the imaginary quadratic
  field.
* `New.Data.integralSourceForms`: the module of the elements of `D.SourceForm` of gauge at most `1`.
* `New.FrobeniusCycle`: ring maps `ι s : W → R` for `s` in `ℤ/N`, alternately even and odd, with
  `ι (s + 1) ≡ ι s ^ P` modulo `p`, where `P = p ^ frobExp` and the residue field of `W` has
  `P ^ N` elements.

## Relation to the literature

See `New.UpperBound.Divisibility.MarkOperator` for related work.
-/

noncomputable section TwistedHeckeType

namespace New.Columns

open Matrix Finset FrobeniusCycle Gf Data ComplexConjugate WithZero NumberField

/-! ### Lattices at a finite place -/

section Lattices

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {k : ℕ}

/-- The valuation ring in `E` of the finite place `v`. -/
abbrev valuationRingAt (v : FinPlace E) : ValuationSubring E := (v.valuation E).valuationSubring

/-- An invertible matrix over `E`, read over the completion of `E` at `v`. -/
def localGL (v : FinPlace E) : GL n E →* GL n (LocField v) :=
  GeneralLinearGroup.map (algebraMap E (LocField v))

/-- A rational matrix lies in the maximal compact subgroup at `v` exactly if it is invertible over
the valuation ring of `v`. -/
lemma localGL_mem_localIntGL_iff {v : FinPlace E} {x : GL n E} :
    localGL v x ∈ localIntGL n v ↔ x ∈ intGL n (valuationRingAt v).toSubring := by
  have h_entry (y : E) :
      algebraMap E (LocField v) y ∈ (LocInt v).toSubring ↔ y ∈ (valuationRingAt v).toSubring := by
    change Valued.v (algebraMap E (LocField v) y) ≤ 1 ↔ v.valuation E y ≤ 1
    rw [v_algebraMap_eq_valuation]
  simp only [mem_intGL, ← map_inv, ← h_entry]
  rfl

/-- The component at `v` of the finite adelic point of a rational point `γ` of the unitary group is
`γ`, read over the completion at `v`. -/
lemma atPlace_embFin (v : FinPlace E) (γ : U (stdSpace E n).J) :
    ((stdSpace E n).embFin γ).atPlace v = localGL v γ :=
  congrArg (GeneralLinearGroup.map (evalAt v)) (stdSpace_embFin γ)

/-- The group `GL_k(W)` over the valuation ring `W` of `v`, embedded in `GL_n(E)` by numbering the
coordinates with `q`. -/
def latticeGL (q : n ≃ Fin k) (v : FinPlace E) : GL (Fin k) (valuationRingAt v) →* GL n E :=
  (GeneralLinearGroup.map (valuationRingAt v).subtype).comp (reindexGL q.symm).toMonoidHom

lemma latticeGL_apply (q : n ≃ Fin k) (v : FinPlace E) (g : GL (Fin k) (valuationRingAt v))
    (i j : n) : latticeGL q v g i j = g (q i) (q j) := rfl

/-- A rational matrix lies in the maximal compact subgroup at `v` exactly if it comes from `GL_k`
over the valuation ring of `v`, in the numbering `q` of the coordinates. -/
lemma localGL_mem_localIntGL_iff_mem_range (q : n ≃ Fin k) {v : FinPlace E} {x : GL n E} :
    localGL v x ∈ localIntGL n v ↔ x ∈ (latticeGL q v).range := by
  have h_onto : (reindexGL (R := valuationRingAt v) q.symm).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.2 (reindexGL q.symm).surjective
  rw [localGL_mem_localIntGL_iff, latticeGL, MonoidHom.range_comp, h_onto, ← MonoidHom.range_eq_map]
  rfl

/-- The image of `GL_k` over the valuation ring of `v` lies in the maximal compact subgroup at
`v`. -/
lemma localGL_latticeGL_mem_localIntGL (q : n ≃ Fin k) (v : FinPlace E)
    (g : GL (Fin k) (valuationRingAt v)) : localGL v (latticeGL q v g) ∈ localIntGL n v :=
  (localGL_mem_localIntGL_iff_mem_range q).2 ⟨g, rfl⟩

variable (E) in
/-- The matrix `diag(p, …, p, 1, …, 1)` with `p` at the first `r` coordinates in the numbering
`q`. -/
def blockScaling (q : n ≃ Fin k) (p r : ℕ) [Fact p.Prime] : GL n E :=
  diagGL fun i : n ↦ if q i < r then Units.mk0 (p : E) NeZero.out else 1

variable {p r : ℕ} [Fact p.Prime] {l : FinPlace E}

lemma coe_blockScaling (q : n ≃ Fin k) :
    (blockScaling E q p r).val = diagonal fun i : n ↦ if q i < r then (p : E) else 1 := by
  simp [blockScaling, apply_ite Units.val]

lemma coe_blockScaling_inv (q : n ≃ Fin k) :
    (blockScaling E q p r)⁻¹.val = diagonal fun i : n ↦ if q i < r then (p : E)⁻¹ else 1 := by
  simp [blockScaling, ← map_inv, apply_ite Units.val, apply_ite Inv.inv]

/-- Let `p` be a uniformizer at `l`, let `q` number the `k` coordinates, and let `r < k`. The matrix
`blockScaling E q p r = diag(p, …, p, 1, …, 1)`, with `p` at the first `r` coordinates, lies over
the completion at `l` in the double coset `basicDoubleCoset n l r` of the Hecke operator of index
`r`. -/
lemma blockScaling_mem_basicDoubleCoset (q : n ≃ Fin k) (hp : l.valuation E p = exp (-1))
    (hr : r < k) : localGL l (blockScaling E q p r) ∈ basicDoubleCoset n l r := by
  let ϖ : (LocField l)ˣ := (Units.mk0 (p : E) NeZero.out).map (algebraMap E (LocField l))
  let s : Finset n := (Iio (⟨r, hr⟩ : Fin k)).map q.symm.toEmbedding
  have h_diag : localGL l (blockScaling E q p r) = diagGL fun i : n ↦ if i ∈ s then ϖ else 1 := by
    ext i j
    simp [localGL, coe_blockScaling, s, ϖ, Fin.lt_def, diagonal_apply, apply_ite Units.val,
      apply_ite (algebraMap E (LocField l))]
  simpa [h_diag, s] using
    (diagGL_mem_basicDoubleCoset (ϖ := ϖ) ((v_algebraMap_eq_valuation (p : E)).trans hp) s).1

/-- Over a local ring `W`, a matrix is parahoric for the blocks of sizes `r` and `k - r` exactly if
its entries at `(i, j)` with `i < r ≤ j` lie in the maximal ideal. -/
lemma mem_parahoric_twoBlock_iff {W : Type} [CommRing W] [IsLocalRing W] {β : GL (Fin k) W} :
    β ∈ parahoric W (twoBlock k r) ↔
      ∀ i j : Fin k, i < r → r ≤ j → β i j ∈ IsLocalRing.maximalIdeal W := by
  refine forall₂_congr fun i j ↦ ?_
  have h_blocks : twoBlock k r i < twoBlock k r j ↔ i < r ∧ r ≤ j := by grind [twoBlock]
  change (twoBlock k r i < twoBlock k r j → IsLocalRing.residue W (β i j) = 0) ↔ _
  rw [h_blocks, and_imp, IsLocalRing.residue_eq_zero_iff]

/-- Let `p` be a uniformizer at `l`, with valuation ring `W`, and let `d = diag(p, …, p, 1, …, 1)`
have `r` entries `p`. For `β` in `GL_k(W)`, the conjugate `d⁻¹ β d` is integral at `l`, together
with its inverse, exactly if `β` is parahoric for the blocks of sizes `r` and `k - r`, that is, if
its entries at `(i, j)` with `i < r ≤ j` lie in the maximal ideal of `W`. -/
lemma conj_blockScaling_mem_localIntGL_iff (q : n ≃ Fin k) (hp : l.valuation E p = exp (-1))
    {β : GL (Fin k) (valuationRingAt l)} :
    localGL l ((blockScaling E q p r)⁻¹ * latticeGL q l β * blockScaling E q p r) ∈ localIntGL n l ↔
      β ∈ parahoric (valuationRingAt l) (twoBlock k r) := by
  set d : GL n E := blockScaling E q p r
  have h_entries (x : GL (Fin k) (valuationRingAt l)) :
      (∀ i j : n, (d⁻¹ * latticeGL q l x * d) i j ∈ (valuationRingAt l).toSubring) ↔
        x ∈ parahoric (valuationRingAt l) (twoBlock k r) := by
    -- Conjugation divides one off-diagonal block by `p`, multiplies the other by `p` and fixes
    -- the diagonal blocks.
    rw [mem_parahoric_twoBlock_iff]
    refine q.forall₂_congr q fun {i j} ↦ ?_
    have h_entry : l.valuation E ((d⁻¹ * latticeGL q l x * d) i j) =
        (if q i < r then exp 1 else 1) * l.valuation E (x (q i) (q j)) *
          if q j < r then exp (-1) else 1 := by
      -- `-coe_units_inv`: the inverse stays that of a unit, so that `coe_blockScaling_inv` applies
      simp [d, -coe_units_inv, coe_blockScaling, coe_blockScaling_inv, latticeGL_apply, hp,
        apply_ite (l.valuation E)]
    change l.valuation E _ ≤ 1 ↔ _
    rw [h_entry, Valuation.mem_maximalIdeal_iff]
    have h_int : l.valuation E (x (q i) (q j)) ≤ 1 := (x (q i) (q j)).2
    split_ifs with hi hj hj
    · simpa [mul_right_comm, ← exp_add, hj.not_ge] using h_int
    · -- the block that is divided by `p`
      rw [mul_one, ← le_inv_mul_iff₀ exp_pos, ← WithZero.exp_neg, ← lt_mul_exp_iff_le (by simp)]
      simp [hi, not_lt.1 hj, ← exp_add]
    · simpa [hi] using mul_le_one' h_int (exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0))
    · simpa [hi] using h_int
  have h_inv : (d⁻¹ * latticeGL q l β * d)⁻¹ = d⁻¹ * latticeGL q l β⁻¹ * d := by simp [mul_assoc]
  rw [localGL_mem_localIntGL_iff, mem_intGL, h_inv, h_entries, h_entries, inv_mem_iff, and_self]

/-- Let `p` be a uniformizer at `l` and let `d = diag(p, …, p, 1, …, 1)` have `r` entries `p`. If
`gᵀ g'ᵀ⁻¹` is parahoric for the blocks of sizes `r` and `k - r`, then `d g⁻¹ g' d⁻¹` is integral
at `l`: the inverse transpose keeps integrality and exchanges `d` with `d⁻¹`. -/
lemma conj_mem_localIntGL_of_transposeGL_mem_parahoric (q : n ≃ Fin k)
    (hp : l.valuation E p = exp (-1)) {g g' : GL (Fin k) (valuationRingAt l)}
    (h_parahoric :
      transposeGL g * (transposeGL g')⁻¹ ∈ parahoric (valuationRingAt l) (twoBlock k r)) :
    localGL l (blockScaling E q p r * latticeGL q l (g⁻¹ * g') * (blockScaling E q p r)⁻¹) ∈
      localIntGL n l := by
  set d : GL n E := blockScaling E q p r
  have hd : invTransposeGL d = d⁻¹ := GeneralLinearGroup.ext fun i j ↦ by
    change (d⁻¹.val)ᵀ i j = d⁻¹.val i j
    rw [coe_blockScaling_inv, diagonal_transpose]
  have h_lattice (x : GL (Fin k) (valuationRingAt l)) :
      invTransposeGL (latticeGL q l (transposeGL x)) = latticeGL q l x⁻¹ := rfl
  have h_eq : d * latticeGL q l (g⁻¹ * g') * d⁻¹ =
      invTransposeGL (d⁻¹ * latticeGL q l (transposeGL g * (transposeGL g')⁻¹) * d) := by
    simp only [map_mul, map_inv, hd, h_lattice, inv_inv]
  rwa [h_eq, localGL_mem_localIntGL_iff, invTransposeGL_mem_intGL, ← localGL_mem_localIntGL_iff,
    conj_blockScaling_mem_localIntGL_iff q hp]

end Lattices

/-! ### The cosets of the Hecke operator as origins of edges -/

section Edges

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {k : ℕ}

/-- The element `g_l⁻¹ β d` of `GL_n` over the completion at `l`, where `g_l` is the `l`-component
of `g` and `d = diag(p, …, p, 1, …, 1)`. Multiplying `g_l` by it on the right gives `β d`. -/
def edgeStep (q : n ≃ Fin k) (p r : ℕ) [Fact p.Prime] {l : FinPlace E} (g : Gf E n)
    (β : GL (Fin k) (valuationRingAt l)) : GL n (LocField l) :=
  (g.atPlace l)⁻¹ * localGL l (latticeGL q l β * blockScaling E q p r)

variable {p r : ℕ} [Fact p.Prime] {l : FinPlace E}

omit [Fact p.Prime] in
lemma natCast_mem_of_valuation_eq (hp : l.valuation E p = exp (-1)) : (p : 𝓞 E) ∈ l.asIdeal :=
  (l.valuation_lt_one_iff_mem (K := E) p).1 (hp.trans_lt (exp_lt_exp.2 (by norm_num)))

/-- Let `p` be a uniformizer at `l`, let `q` number the `k` coordinates, and let `r < k`. Let the
component `g_l` of `g` at `l` be invertible over the local integers, let `β` lie in `GL_k` over the
valuation ring of `l`, and let `d = diag(p, …, p, 1, …, 1)` have `p` at the first `r` coordinates.
Then `edgeStep q p r g β = g_l⁻¹ β d` lies in the double coset `basicDoubleCoset n l r` of the Hecke
operator of index `r` at `l`. -/
lemma edgeStep_mem_basicDoubleCoset (q : n ≃ Fin k) (hp : l.valuation E p = exp (-1)) (hr : r < k)
    {g : Gf E n} (hg : g.atPlace l ∈ localIntGL n l) (β : GL (Fin k) (valuationRingAt l)) :
    edgeStep q p r g β ∈ basicDoubleCoset n l r := by
  have h_left : (g.atPlace l)⁻¹ * localGL l (latticeGL q l β) ∈ localIntGL n l :=
    mul_mem (inv_mem hg) (localGL_latticeGL_mem_localIntGL q l β)
  rw [basicDoubleCoset_eq (blockScaling_mem_basicDoubleCoset q hp hr), edgeStep, map_mul,
    ← mul_assoc]
  exact DoubleCoset.mem_doubleCoset.2 ⟨_, h_left, 1, one_mem _, (mul_one _).symm⟩

/-- Let `p` be a uniformizer at `l`, and recall that `edgeStep q p r g β = g_l⁻¹ β d`. These
elements for `β` and `β'` lie in the same coset of the maximal compact subgroup at `l` exactly if
`β⁻¹ β'` is parahoric for the blocks of sizes `r` and `k - r`. -/
lemma edgeStep_inv_mul_mem_localIntGL_iff (q : n ≃ Fin k) (hp : l.valuation E p = exp (-1))
    (g : Gf E n) (β β' : GL (Fin k) (valuationRingAt l)) :
    (edgeStep q p r g β)⁻¹ * edgeStep q p r g β' ∈ localIntGL n l ↔
      β⁻¹ * β' ∈ parahoric (valuationRingAt l) (twoBlock k r) := by
  rw [← conj_blockScaling_mem_localIntGL_iff q hp]
  simp [edgeStep, mul_assoc]

/-- Let `p` be a uniformizer at the split place `l` and let `g` be integral above `p`. Every coset
in the double coset of the Hecke operator of index `r < k` at `l` is the coset of
`edgeStep q p r g β = g_l⁻¹ β d` for some `β` over the valuation ring of `l`, where `g_l` is the
component of `g` at `l` and `d = diag(p, …, p, 1, …, 1)` has `p` at the first `r` coordinates. -/
lemma exists_edgeStep_eq (q : n ≃ Fin k) (hl : l.IsSplit) (hp : l.valuation E p = exp (-1))
    (hr : r < k) {g : Gf E n} (hg : g ∈ integralAbove n p) {z : GL n (LocField l)}
    (hz : z ∈ basicDoubleCoset n l r) :
    ∃ β : GL (Fin k) (valuationRingAt l),
      (edgeStep q p r g β : GL n (LocField l) ⧸ localIntGL n l) = z := by
  set d : GL n (LocField l) := localGL l (blockScaling E q p r)
  have hpl : (p : 𝓞 E) ∈ l.asIdeal := natCast_mem_of_valuation_eq hp
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ : ∃ u₁ ∈ localIntGL n l, ∃ u₂ ∈ localIntGL n l,
    z = u₁ * d * u₂ := by
    rwa [basicDoubleCoset_eq (blockScaling_mem_basicDoubleCoset q hp hr),
      DoubleCoset.mem_doubleCoset] at hz
  -- By weak approximation above `p`, a rational `η` makes `η g u₁` and its conjugate by `d`
  -- integral. Then `η` is integral at `l`, so it comes from some `β`, and `β⁻¹` is as required.
  obtain ⟨η, hη, hη_conj⟩ := exists_mul_mem_integralAbove p (g * ofSplitPlace hl u₁)
    (ofSplitPlace hl d⁻¹)
  have hη_l : localGL l η * (g.atPlace l * u₁) ∈ localIntGL n l := by
    simpa [atPlace_embFin] using hη l hpl
  have hη_conj_l : d⁻¹ * (localGL l η * (g.atPlace l * u₁)) * d ∈ localIntGL n l := by
    simpa [atPlace_embFin] using hη_conj l hpl
  obtain ⟨β, hβ⟩ : η.val ∈ (latticeGL q l).range :=
    (localGL_mem_localIntGL_iff_mem_range q).1
      ((mul_mem_cancel_right (mul_mem (hg l hpl) hu₁)).1 hη_l)
  have h_eq : (edgeStep q p r g β⁻¹)⁻¹ * (u₁ * d * u₂) =
      d⁻¹ * (localGL l η * (g.atPlace l * u₁)) * d * u₂ := by
    simp [edgeStep, hβ, d, mul_assoc]
  exact ⟨β⁻¹, QuotientGroup.eq.2 (by simpa only [h_eq] using mul_mem hη_conj_l hu₂)⟩

/-- The edges at `l` and level `K`: pairs of a class at level `K`, the terminus of the edge, and a
coset in `GL_k(W)` of the parahoric subgroup with blocks of sizes `r` and `k - r`, where `W` is the
valuation ring of `l`. -/
abbrev ClassEdges (K : Subgroup (Gf E n)) (l : FinPlace E) (k r : ℕ) : Type :=
  StdClasses K × ParahoricCosets (valuationRingAt l) k r

variable (p k r) in
/-- Coordinates for the cosets of the Hecke operator of index `r` at a split place `l`, at
level `K`. Write `W` for the valuation ring of `l` and `d = diag(p, …, p, 1, …, 1)`. The origin
of the edge `(x, b)` is the point obtained from the representative of `x` by replacing its
`l`-component with `β d` (and the component at the conjugate place accordingly), where `β = b.out`
represents the coset `b`. -/
structure HeckeEdges (K : Subgroup (Gf E n)) (hl : l.IsSplit) where
  /-- The numbering of the coordinates. -/
  numbering : n ≃ Fin k
  /-- The representative of a class. -/
  rep : StdClasses K → Gf E n
  /-- The point `rep x` lies in the class `x`. -/
  mk_rep : ∀ x : StdClasses K, DoubleCoset.mk stdRatPoints K (rep x) = x
  /-- The representatives are integral above `p`. -/
  rep_mem_integralAbove : ∀ x : StdClasses K, rep x ∈ integralAbove n p
  /-- The class of the origin of an edge. -/
  origin : ClassEdges K l k r → StdClasses K
  /-- The rational part: a rational point that takes the representative of the class `origin e` to
  the origin of `e`, up to right multiplication by `K`. -/
  rationalPart : ClassEdges K l k r → U (stdSpace E n).J
  /-- The remaining factor in `K`. -/
  levelPart : ClassEdges K l k r → K
  /-- The change of basis at the origin. -/
  originBasisChange : ClassEdges K l k r → GL (Fin k) (valuationRingAt l)
  /-- The origin is the rational part times the representative of its class times `levelPart`. -/
  rep_mul_edgeStep_eq : ∀ (x : StdClasses K) (b : ParahoricCosets (valuationRingAt l) k r),
    rep x * ofSplitPlace hl (edgeStep numbering p r (rep x) b.out) =
      (stdSpace E n).embFin (rationalPart (x, b)) * rep (origin (x, b)) * levelPart (x, b)
  /-- The inverse of the rational part is `g d⁻¹ β⁻¹`, with `g` the change of basis at the
  origin. -/
  rationalPart_inv : ∀ (x : StdClasses K) (b : ParahoricCosets (valuationRingAt l) k r),
    (rationalPart (x, b)).val⁻¹ = latticeGL numbering l (originBasisChange (x, b)) *
      (blockScaling E numbering p r)⁻¹ * latticeGL numbering l b.out⁻¹

variable {K : Subgroup (Gf E n)} [IsLevel K] {hl : l.IsSplit}

/-- The component at any place of an element of a level is integral. -/
lemma atPlace_mem_localIntGL_of_isLevel (u : K) (v : FinPlace E) :
    u.val.atPlace v ∈ localIntGL n v :=
  mem_stdLevel_iff.1 (IsLevel.le u.2) v

variable (r K hl) in
/-- Let `l` be a split finite place above `p`, let `K` be a level and let `q` number the
coordinates. A class is a double coset of the rational points and `K`. An edge is a pair `(x, b)` of
a class `x`, its terminus, and a coset `b` of the parahoric subgroup with blocks of sizes `r` and
`k - r`. Then there is a choice of the data `New.Columns.HeckeEdges`: for each class a
representative that is integral above `p`, and for each edge a factorisation of its origin (the
representative of `x` moved at `l` to `β d`, with `β = b.out` and `d = diag(p, …, p, 1, …, 1)`) as a
rational matrix (the rational part) times the representative of the class of the origin times an
element of `K`, and a matrix in `GL_k` over the valuation ring of `l` by which the rational part
differs from `β d`. -/
lemma nonempty_heckeEdges (q : n ≃ Fin k) (hpl : (p : 𝓞 E) ∈ l.asIdeal) :
    Nonempty (HeckeEdges k p r K hl) := by
  obtain ⟨ρ, hρ, hρ_int⟩ := exists_reps_integralAbove (K := K) p
  have h_origin (e : ClassEdges K l k r) :
      ∃ (y : StdClasses K) (γ : U (stdSpace E n).J) (u : K),
        ρ e.1 * ofSplitPlace hl (edgeStep q p r (ρ e.1) e.2.out) = (stdSpace E n).embFin γ * ρ y *
          u :=
    exists_eq_map_mul_rep_mul _ K hρ _
  choose origin γ u h_eq using h_origin
  -- At `l` the origin is `β d`, so `γ⁻¹ β d` is integral at `l`.
  have h_basisChange (e : ClassEdges K l k r) :
      (γ e).val⁻¹ * (latticeGL q l e.2.out * blockScaling E q p r) ∈ (latticeGL q l).range := by
    have h_at : localGL l (latticeGL q l e.2.out) * localGL l (blockScaling E q p r) =
        localGL l (γ e) * ((ρ (origin e)).atPlace l * (u e).val.atPlace l) := by
      simpa [edgeStep, atPlace_embFin, mul_assoc] using congrArg (atPlace l) (h_eq e)
    rw [← localGL_mem_localIntGL_iff_mem_range, map_mul, map_mul, h_at, map_inv,
      inv_mul_cancel_left]
    exact mul_mem (hρ_int _ l hpl) (atPlace_mem_localIntGL_of_isLevel (u e) l)
  choose g hg using h_basisChange
  exact ⟨{
    numbering := q, rep := ρ, mk_rep := hρ, rep_mem_integralAbove := hρ_int
    origin := origin, rationalPart := γ, levelPart := u, originBasisChange := g
    rep_mul_edgeStep_eq x b := h_eq (x, b)
    rationalPart_inv x b := by simp [hg, mul_assoc] }⟩

namespace HeckeEdges

variable (C : HeckeEdges k p r K hl)

omit [IsLevel K] in
/-- The rational part of the edge `(x, b)` as a finite adelic point: the origin of the edge, times
the inverse of its factor in `K`, times the inverse of the representative of the class of the
origin. -/
lemma embFin_rationalPart (x : StdClasses K) (b : ParahoricCosets (valuationRingAt l) k r) :
    (stdSpace E n).embFin (C.rationalPart (x, b)) =
      C.rep x * ofSplitPlace hl (edgeStep C.numbering p r (C.rep x) b.out) *
        (C.levelPart (x, b)).val⁻¹ * (C.rep (C.origin (x, b)))⁻¹ := by
  simp [C.rep_mul_edgeStep_eq]

omit [IsLevel K] in
/-- The rational part of the edge `(x, b)` is `β d g⁻¹`, with `β = b.out`,
`d = diag(p, …, p, 1, …, 1)` and `g` the change of basis at the origin. -/
lemma rationalPart_eq (x : StdClasses K) (b : ParahoricCosets (valuationRingAt l) k r) :
    (C.rationalPart (x, b)).val = latticeGL C.numbering l b.out * blockScaling E C.numbering p r *
      latticeGL C.numbering l (C.originBasisChange (x, b))⁻¹ := by
  simp [inv_eq_iff_eq_inv.1 (C.rationalPart_inv x b), mul_assoc]

/-- For coordinates `C` of the edges at `l`, the rational part `C.rationalPart e` is integral at
every place `v` above `p` other than `l` and its conjugate `star l`. -/
lemma localGL_rationalPart_mem_localIntGL (e : ClassEdges K l k r) {v : FinPlace E}
    (hpv : (p : 𝓞 E) ∈ v.asIdeal) (hv : v ≠ l) (hv_star : star v ≠ l) :
    localGL v (C.rationalPart e) ∈ localIntGL n v := by
  obtain ⟨x, b⟩ := e
  have h_atPlace : localGL v (C.rationalPart (x, b)) = (C.rep x).atPlace v *
      ((C.levelPart (x, b)).val.atPlace v)⁻¹ * ((C.rep (C.origin (x, b))).atPlace v)⁻¹ := by
    simp [← atPlace_embFin, C.embFin_rationalPart, atPlace_ofSplitPlace_of_ne hl _ hv hv_star]
  rw [h_atPlace]
  exact mul_mem (mul_mem (C.rep_mem_integralAbove x v hpv)
    (inv_mem (atPlace_mem_localIntGL_of_isLevel _ v))) (inv_mem (C.rep_mem_integralAbove _ v hpv))

/-- Let `p` be a uniformizer at the split place `l`, let the level `K` be maximal at `l`, and let
the rational points act freely on the cosets of `K`. An edge is a pair `(x, b)` of a class `x` at
level `K`, its terminus, and a coset `b` of the parahoric subgroup. Its origin is the representative
of `x` moved at `l` to `β d`, with `β = b.out` and `d = diag(p, …, p, 1, …, 1)`. The data
`C : HeckeEdges k p r K hl` give the class `C.origin e` of the origin and the matrix
`g = C.originBasisChange e` in `GL_k` over the valuation ring of `l` for which the rational point
moving the representative of that class to the origin is `β d g⁻¹`. Then an edge `e` is determined
by `C.origin e` and by the parahoric coset of the transpose of `g`. -/
lemma eq_of_origin_eq_of_mem_parahoric (hp : l.valuation E p = exp (-1)) (hK : maxCompactAt n l ≤ K)
    (h_free : ∀ g : Gf E n, classAut stdRatPoints K g = ⊥) (e e' : ClassEdges K l k r)
    (h_origin : C.origin e = C.origin e')
    (h_basisChange :
      transposeGL (C.originBasisChange e) * (transposeGL (C.originBasisChange e'))⁻¹ ∈
        parahoric (valuationRingAt l) (twoBlock k r)) : e = e' := by
  -- The quotient `η` of the two rational parts takes the representative of one terminus to that of
  -- the other modulo `K`. So the termini agree and `η = 1` by freeness; then the cosets agree.
  obtain ⟨⟨x, b⟩, ⟨x', b'⟩⟩ := e, e'
  let q : n ≃ Fin k := C.numbering
  let d : GL n E := blockScaling E q p r
  let g : GL n E := latticeGL q l ((C.originBasisChange (x, b))⁻¹ * C.originBasisChange (x', b'))
  let η : U (stdSpace E n).J := C.rationalPart (x, b) * (C.rationalPart (x', b'))⁻¹
  let u : K := (C.levelPart (x', b'))⁻¹ * C.levelPart (x, b)
  have hη : η.val = latticeGL q l b.out * (d * g * d⁻¹) * latticeGL q l b'.out⁻¹ := by
    simp [η, d, g, q, C.rationalPart_eq, mul_assoc]
  have hη_l : localGL l η ∈ localIntGL n l := by
    rw [hη, map_mul, map_mul]
    exact mul_mem (mul_mem (localGL_latticeGL_mem_localIntGL q l _)
      (conj_mem_localIntGL_of_transposeGL_mem_parahoric q hp h_basisChange))
        (localGL_latticeGL_mem_localIntGL q l _)
  -- The element `y u` is trivial away from `l` and `star l`, because the representatives of the
  -- origins cancel, and it is integral at `l`.
  let y : Gf E n := (C.rep x)⁻¹ * (stdSpace E n).embFin η * C.rep x'
  have h_support : y * u ∈ supportedOn n {l} := by
    have h_eq : y * u = ofSplitPlace hl (edgeStep q p r (C.rep x) b.out) *
        (u.val⁻¹ * (ofSplitPlace hl (edgeStep q p r (C.rep x') b'.out))⁻¹ * u) := by
      simp [y, η, u, q, C.embFin_rationalPart, h_origin, mul_assoc]
    simp +contextual [h_eq, atPlace_ofSplitPlace_of_ne]
  have h_int : (y * u).atPlace l ∈ localIntGL n l := by
    have h_rep (z : StdClasses K) := C.rep_mem_integralAbove z l (natCast_mem_of_valuation_eq hp)
    simpa [y, atPlace_embFin] using mul_mem (mul_mem (mul_mem (inv_mem (h_rep x)) hη_l) (h_rep x'))
      (atPlace_mem_localIntGL_of_isLevel u l)
  have h_level : y ∈ K := (mul_mem_cancel_right u.2).1
    (hK ⟨(mem_stdLevel_iff_of_supportedOn h_support).2 (by simpa using h_int), h_support⟩)
  have h_stabilizer (γ : U (stdSpace E n).J)
      (hγ : (C.rep x')⁻¹ * (stdSpace E n).embFin γ * C.rep x' ∈ K) : γ = 1 :=
    (map_eq_one_iff _ Fact.out).1 ((h_free (C.rep x')).le ⟨⟨γ, rfl⟩, hγ⟩)
  obtain ⟨rfl, hη_one⟩ : x = x' ∧ η = 1 :=
    eq_and_eq_one_of_doubleCoset_rep C.mk_rep h_stabilizer η h_level
  have h_coset : b.out⁻¹ * b'.out ∈ parahoric (valuationRingAt l) (twoBlock k r) := by
    have h_one : latticeGL q l b.out * (d * g * d⁻¹) = latticeGL q l b'.out := by
      rw [← mul_inv_eq_one, ← map_inv, ← hη, hη_one, OneMemClass.coe_one]
    have h_conj : d⁻¹ * latticeGL q l (b.out⁻¹ * b'.out) * d = g := by simp [← h_one, mul_assoc]
    rw [← conj_blockScaling_mem_localIntGL_iff q hp, h_conj]
    exact localGL_latticeGL_mem_localIntGL q l _
  rw [← QuotientGroup.out_eq' b, ← QuotientGroup.out_eq' b', QuotientGroup.eq.2 h_coset]

omit [IsLevel K] in
/-- Let `p` be a uniformizer at the split place `l`, let the level `K` be maximal at `l`, let `φ` be
an algebraic form of level `K`, and let `T_r` be the Hecke operator of index `r < k` at `l`. The
classes (`StdClasses K`) are the double cosets of the rational points and `K`, and `C.rep x` is the
representative of the class `x` chosen in the data `C : HeckeEdges k p r K hl`. An edge into `x` is
a pair `(x, b)` with `b` a coset of the parahoric subgroup with blocks of sizes `r` and `k - r`.
Then the value of `T_r φ` at `C.rep x` is the sum over `b` of `C.rationalPart (x, b)`, acting in the
weight representation, applied to `φ (C.rep (C.origin (x, b)))`. -/
lemma heckeSplit_apply_rep [Fintype (ParahoricCosets (valuationRingAt l) k r)]
    (hp : l.valuation E p = exp (-1)) (hr : r < k) (hK : maxCompactAt n l ≤ K)
    {κ : InfinitePlace E → ℕ → ℕ} {c : InfinitePlace E → ℤ} {φ : AlgForm n κ c}
    (hφ : φ ∈ levelSpace (algFormRep κ c) K) (x : StdClasses K) :
    (heckeSplit (algFormRep κ c) hl r φ).val (C.rep x) =
      ∑ b : ParahoricCosets (valuationRingAt l) k r,
        (stdSpace E n).weightRep κ c (C.rationalPart (x, b)) (φ.val (C.rep (C.origin (x, b)))) := by
  -- The cosets in the double coset of `T_r` are those of the `δ b.out`.
  let δ (β : GL (Fin k) (valuationRingAt l)) := edgeStep C.numbering p r (C.rep x) β
  let f : GL n (LocField l) → ℂ := (basicDoubleCoset n l r).indicator 1
  have hf (β : GL (Fin k) (valuationRingAt l)) : f (δ β) = 1 :=
    Set.indicator_of_mem (edgeStep_mem_basicDoubleCoset _ hp hr
      (C.rep_mem_integralAbove x l (natCast_mem_of_valuation_eq hp)) β) 1
  have h_cover (z : GL n (LocField l)) (hz : f z ≠ 0) :
      ∃ β : GL (Fin k) (valuationRingAt l), (δ β : GL n (LocField l) ⧸ localIntGL n l) = z :=
    exists_edgeStep_eq _ hl hp hr (C.rep_mem_integralAbove x) (Set.mem_of_indicator_ne_zero hz)
  have h_sum : heckeSplit (algFormRep κ c) hl r φ =
      ∑ b : ParahoricCosets (valuationRingAt l) k r,
        algFormRep κ c (ofSplitPlace hl (δ b.out)) φ := by
    -- By definition, `heckeSplit` is the operator of the indicator `f` of the double coset.
    change heckeFun ((algFormRep κ c).comp (ofSplitPlace hl)) (localIntGL n l) f φ = _
    have hφ_l : φ ∈ sphericalAt (algFormRep κ c) l := levelSpace_anti hK hφ
    have h_inv := edgeStep_inv_mul_mem_localIntGL_iff (r := r) C.numbering hp (C.rep x)
    obtain ⟨-, h_eq⟩ := heckeFun_eq_sum_pullback (f := f) (by simp [f])
      ((mem_sphericalAt_iff hl).1 hφ_l) univ δ h_cover h_inv (by simp)
    simpa only [hf, one_smul, MonoidHom.comp_apply] using h_eq
  simp only [h_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  refine sum_congr rfl fun b _ ↦ ?_
  change φ.val (C.rep x * ofSplitPlace hl (δ b.out)) = _
  rw [C.rep_mul_edgeStep_eq, levelSpace_smoothFormRep_apply hφ, MonoidHom.one_apply, one_smul]

end HeckeEdges

end Edges

/-! ### The variables -/

section Variables

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {k N p r : ℕ}
  [Fact p.Prime] {l : FinPlace E} {O : ValuationSubring ℂ}

/-- The action on the variables of one letter `s`. Let `T` be a Frobenius cycle for `p` on the
valuation ring `W` of `l`: it assigns to each letter a ring map `T.embedding s` from `W` to `O` and
a parity. Let `T.embedding s` be the embedding `φ` if `s` is even and `φ ∘ conj` if `s` is odd. Let
`γ` be unitary with `γ⁻¹ = g d⁻¹ β`, where `g` and `β` lie in `GL_k(W)` and
`d = diag(p, …, p, 1, …, 1)` has `p` at the coordinates that `q` numbers below `r`. Here
`latticeGL q l` reads a matrix over `W` in the basis numbered by `q`, and the letter matrix of `g`
is `g` under `T.embedding s`, inverted and transposed for odd `s`. The variable `(i, s)` is deep if
`r ≤ i` for even `s` and if `i < r` for odd `s`; `T.deepIndicator r (i, s)` is `1` for deep
variables and `0` for the others. Apply `φ ∘ conj` to the entries of `γ`, transpose, and multiply by
`p` if `s` is even. The result is the letter matrix of `g`, times the diagonal matrix with `p` at
the deep variables and `1` elsewhere, times the letter matrix of `β`. -/
lemma smul_transpose_map_eq_letterMatrix (T : FrobeniusCycle N (valuationRingAt l) O)
    (hTp : T.p = p) (q : n ≃ Fin k) (s : ZMod N) (φ : E →+* ℂ)
    (hι : ∀ x : valuationRingAt l, T.embedding s x = (if T.isEven s then φ else φ.comp conj) x)
    {γ : U (stdSpace E n).J} {g β : GL (Fin k) (valuationRingAt l)}
    (hγ : (γ : GL n E)⁻¹ = latticeGL q l g * (blockScaling E q p r)⁻¹ * latticeGL q l β) :
    (if T.isEven s then (p : ℂ) else 1) •
        ((γ : GL n E).val.map (φ.comp conj))ᵀ.submatrix q.symm q.symm =
      (T.letterMatrix s g * diagonal (fun i : Fin k ↦ (T.p : O) ^ T.deepIndicator r (i, s)) *
        T.letterMatrix s β).map O.subtype := by
  -- `F` applies the embedding of the letter to the entries of a matrix and numbers the coordinates.
  let ψ : E →+* ℂ := if T.isEven s then φ else φ.comp conj
  let F : Matrix n n E →+* Matrix (Fin k) (Fin k) ℂ :=
    (reindexRingEquiv ℂ q).toRingHom.comp ψ.mapMatrix
  have hF (x : GL (Fin k) (valuationRingAt l)) :
      F (latticeGL q l x).val = (x.val.map (T.embedding s)).map O.subtype :=
    Matrix.ext fun i j ↦ by simp [F, ψ, latticeGL_apply, hι]
  have hF_diagonal (v : n → E) : F (diagonal v) = diagonal fun i : Fin k ↦ ψ (v (q.symm i)) :=
    Matrix.ext fun i j ↦ by simp [F, diagonal_apply]
  rw [Matrix.map_mul, Matrix.map_mul]
  cases hs : T.isEven s
  · -- Odd letter: transpose `γ = β⁻¹ d g⁻¹`.
    have hγ_eq : γ.val = latticeGL q l β⁻¹ * blockScaling E q p r * latticeGL q l g⁻¹ := by
      simp [inv_eq_iff_eq_inv.1 hγ, mul_assoc]
    have hd : (F (blockScaling E q p r).val)ᵀ =
        (diagonal fun i : Fin k ↦ (T.p : O) ^ T.deepIndicator r (i, s)).map O.subtype := by
      rw [coe_blockScaling, hF_diagonal, diagonal_transpose, diagonal_map (map_zero _)]
      congr with i
      by_cases hi : i < r <;> simp [deepIndicator, hs, hTp, hi]
    have h_letter (x : GL (Fin k) (valuationRingAt l)) :
        (F (latticeGL q l x⁻¹).val)ᵀ = (T.letterMatrix s x).map O.subtype := by
      simp [hF, letterMatrix, hs, transpose_map, -map_inv]
    calc _ = (F γ.val.val)ᵀ := Matrix.ext fun i j ↦ by simp [F, ψ, hs]
      _ = _ := by
          simp only [hγ_eq, Units.val_mul, map_mul, transpose_mul, hd, h_letter, Matrix.mul_assoc]
  · -- Even letter: `γ` is unitary, so its conjugate transpose is `γ⁻¹ = g d⁻¹ β`.
    have h_unitary : γ.val⁻¹.val = γ.val.valᴴ := U.inv_val_eq_conjTranspose γ
    have hd : (p : ℂ) • F (blockScaling E q p r)⁻¹.val =
        (diagonal fun i : Fin k ↦ (T.p : O) ^ T.deepIndicator r (i, s)).map O.subtype := by
      rw [coe_blockScaling_inv, hF_diagonal, ← diagonal_smul, diagonal_map (map_zero _)]
      congr with i
      by_cases hi : i < r <;> simp [deepIndicator, hs, hTp, hi, ← not_lt, NeZero.ne p]
    have h_letter (x : GL (Fin k) (valuationRingAt l)) : F (latticeGL q l x).val =
        (T.letterMatrix s x).map O.subtype := by simp [hF, letterMatrix, hs]
    calc _ = (p : ℂ) • F γ.val⁻¹.val := by
          simp only [h_unitary, F, ψ, hs, ite_true]
          rfl
      _ = _ := by
          simp only [hγ, Units.val_mul, map_mul, ← hd, h_letter, Matrix.mul_smul, Matrix.smul_mul]

/-- Let `γ` be unitary with `γ⁻¹ = g d⁻¹ β` (`g`, `β` in `GL_k` over the valuation ring of `l`,
`d = diag(p, …, p, 1, …, 1)` with `r` entries `p`), and let the Frobenius cycle `T` embed that ring
by `φ s` at even letters `s` and by `φ s ∘ conj` at odd ones. Apply `φ s ∘ conj` to `γ`, transpose,
multiply by `p` for even `s`, and take the tensor product over `s` of the `a`-th symmetric powers.
The result is `T.letterRep a g * T.depthPower k a r * T.letterRep a β`. Here `T.letterRep a` is the
representation on the monomials, and `T.depthPower k a r` is the diagonal matrix whose entry at a
monomial is `p` to its total degree in the deep variables. -/
lemma kroneckerPi_symPowMatrix_eq_letterRep [NeZero N] (T : FrobeniusCycle N (valuationRingAt l) O)
    (hTp : T.p = p) (q : n ≃ Fin k) (a : ℕ) (φ : ZMod N → E →+* ℂ)
    (hι : ∀ (s : ZMod N) (x : valuationRingAt l),
      T.embedding s x = (if T.isEven s then φ s else (φ s).comp conj) x)
    {γ : U (stdSpace E n).J} {g β : GL (Fin k) (valuationRingAt l)}
    (hγ : (γ : GL n E)⁻¹ = latticeGL q l g * (blockScaling E q p r)⁻¹ * latticeGL q l β) :
    (kroneckerPi fun s : ZMod N ↦ symPowMatrix a ((if T.isEven s then (p : ℂ) else 1) •
        ((γ : GL n E).val.map ((φ s).comp conj))ᵀ.submatrix q.symm q.symm)) =
      (T.letterRep a g * T.depthPower k a r * T.letterRep a β).map O.subtype := by
  -- Symmetric powers and tensor products are multiplicative.
  simp only [smul_transpose_map_eq_letterMatrix T hTp q _ _ (hι _) hγ, symPowMatrix_map,
    kroneckerPi_map, letterRep_apply, depthPower, diagonal_pow_depth, ← kroneckerPi_mul, ← map_mul]

end Variables

/-! ### The weight space and the module of integral source forms -/

/-- On the `k` coordinates `D.X 0`, numbered by `q`, the weight `D.columnCount τ` has one row, of
length `b = a` if the infinite place `τ` is an a-place (in `D.aPlaces`) and `b = 0` otherwise. So
there is a matching `ψ` of the basis with the monomials of degree `b` such that, for all `c` and
`z`, `c ^ b` times the Schur matrix of `z` is the transpose of the `b`-th symmetric power of `c zᵀ`,
with coordinates renumbered by `q`. -/
lemma exists_schur_eq_symPowMatrix {P : Parameters} {D : Data P} (q : D.X 0 ≃ Fin D.k)
    {τ : D.Φ} {b : ℕ} (hb : (if τ ∈ D.aPlaces then D.a else 0) = b) :
    ∃ ψ : WeylIndex (D.X 0) (fun _ : Unit ↦ D.columnCount τ) ≃ Monomials (Fin D.k) b,
      ∀ (c : ℂ) (z : Matrix (D.X 0) (D.X 0) ℂ)
        (i j : WeylIndex (D.X 0) fun _ : Unit ↦ D.columnCount τ),
        c ^ b * schur (fun _ : Unit ↦ D.columnCount τ) (fun _ : Unit ↦ z) i j =
          symPowMatrix b (c • zᵀ.submatrix q.symm q.symm) (ψ j) (ψ i) := by
  have h_card : Fintype.card (D.X 0) = D.k := by simpa using Fintype.card_congr q
  have h_row : ∀ i > 0, i < Fintype.card (D.X 0) → D.columnCount τ i = if i = 1 then b else 0 := by
    -- by the definition of the weight `D.columnCount`, given the value `hb` of `b`
    grind only [columnCount]
  exact exists_equiv_schur_one_row_eq_symPowMatrix q.symm
    (D.nat_le_of_hasLogBound.trans_eq h_card.symm) h_row

/-- Let `q` number the `D.k` coordinates `D.X 0`, and let `t` number a set `Q` of a-places among the
infinite places `D.Φ` of `D.E`. At an a-place the weight `D.columnCount` is one row of length
`a = D.a`. So a basis index of the weight space splits, by `J`, into monomials of degree `a` at the
places `t s` and an index for the places outside `Q`. Let `z` be a family of matrices, one for each
place, which acts on the weight space by its Schur matrix (`schur`), and let `c s` be scalars. Then
`(∏ s, c s) ^ a` times this matrix is the tensor product of the transposed `a`-th symmetric powers
of the `c s • (z (t s))ᵀ`, in the numbering `q`, and the Schur matrix of `z` outside `Q`. -/
lemma exists_weylIndex_equiv {P : Parameters} {D : Data P} {N : ℕ} [NeZero N] {Q : D.Φ → Prop}
    [DecidablePred Q] (q : D.X 0 ≃ Fin D.k) (t : ZMod N ≃ Subtype Q)
    (h_aPlace : ∀ s : ZMod N, (t s).val ∈ D.aPlaces) :
    ∃ J : WeylIndex (D.X 0) D.columnCount ≃
        Exponents N D.k D.a × WeylIndex (D.X 0) fun τ : {τ : D.Φ // ¬Q τ} ↦ D.columnCount τ,
      ∀ (c : ZMod N → ℂ) (z : D.Φ → Matrix (D.X 0) (D.X 0) ℂ)
        (i j : WeylIndex (D.X 0) D.columnCount),
        (∏ s : ZMod N, c s) ^ D.a * schur D.columnCount z i j =
          schur (fun τ : {τ : D.Φ // ¬Q τ} ↦ D.columnCount τ) (fun τ : {τ : D.Φ // ¬Q τ} ↦ z τ)
              (J i).2 (J j).2 *
            kroneckerPi
              (fun s : ZMod N ↦ symPowMatrix D.a (c s • (z (t s))ᵀ.submatrix q.symm q.symm))
              (J j).1 (J i).1 := by
  have h_place (s : ZMod N) :
      ∃ ψ : WeylIndex (D.X 0) (fun _ : Unit ↦ D.columnCount (t s).val) ≃ Monomials (Fin D.k) D.a,
        ∀ (c : ℂ) (z : Matrix (D.X 0) (D.X 0) ℂ)
          (i j : WeylIndex (D.X 0) fun _ : Unit ↦ D.columnCount (t s).val),
          c ^ D.a * schur (fun _ : Unit ↦ D.columnCount (t s).val) (fun _ : Unit ↦ z) i j =
            symPowMatrix D.a (c • zᵀ.submatrix q.symm q.symm) (ψ j) (ψ i) :=
    exists_schur_eq_symPowMatrix q (ite_eq_left (h_aPlace s))
  choose ψ hψ using h_place
  let J : WeylIndex (D.X 0) D.columnCount ≃
      Exponents N D.k D.a × WeylIndex (D.X 0) fun τ : {τ : D.Φ // ¬Q τ} ↦ D.columnCount τ :=
    (Equiv.piEquivPiSubtypeProd Q _).trans
      ((t.piCongr fun s ↦ (ψ s).symm.trans (Equiv.piUnique _)).symm.prodCongr (Equiv.refl _))
  have hJ_fst (i : WeylIndex (D.X 0) D.columnCount) (s : ZMod N) : (J i).1 s = ψ s fun _ ↦
    i (t s) := rfl
  have hJ_snd (i : WeylIndex (D.X 0) D.columnCount) (τ : {τ : D.Φ // ¬Q τ}) : (J i).2 τ = i τ := rfl
  refine ⟨J, fun c z i j ↦ ?_⟩
  -- Both Schur matrices are products over places; split the places into `Q` and the others.
  rw [schur_apply_eq_prod .refl, schur_apply_eq_prod .refl,
    ← Fintype.prod_subtype_mul_prod_subtype Q, ← t.prod_comp, ← mul_assoc, ← prod_pow,
    ← prod_mul_distrib, mul_comm]
  simp only [hψ, kroneckerPi, of_apply, hJ_fst, hJ_snd]

/-- Let `S` be a set of infinite places of `E = D.E`. A place `τ` has a chosen complex embedding
`Φ τ`, and with `ιₚ : ℂ → ℂ_p` it induces a prime `inducedPlace τ` above `p`. Let `γ` be an
invertible matrix over `E` that lies in `GL(O_v)` for the conjugate `v` of each prime induced by an
a-place (`D.aPlaces`) in `S`. Embed `γ` by `Φ τ ∘ conj` at `τ`. Then its Schur matrix (`schur`), the
action on the factor at `S` of the weight space of weight `D.columnCount`, is an invertible matrix
over `embValRing`, the ring of complex numbers that are integral under `ιₚ`. -/
lemma exists_schur_eq_map {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {S : D.Φ → Prop} [DecidablePred S] {γ : GL (D.X 0) D.E}
    (hγ : ∀ τ ∈ D.aPlaces, S τ →
      localGL (star (inducedPlace τ)) γ ∈ localIntGL (D.X 0) (star (inducedPlace τ))) :
    ∃ m : GL (WeylIndex (D.X 0) fun τ : Subtype S ↦ D.columnCount τ) embValRing,
      schur (fun τ : Subtype S ↦ D.columnCount τ)
          (fun τ : Subtype S ↦ γ.val.map ((Φ τ.val).comp conj)) =
        m.val.map embValRing.subtype := by
  have h_place (τ : Subtype S) : ∃ m : GL (D.X 0) embValRing,
      schur (fun _ : Unit ↦ D.columnCount τ) (fun _ ↦ γ.val.map ((Φ τ.val).comp conj)) =
        schur (fun _ : Unit ↦ D.columnCount τ) fun _ ↦ m.val.map embValRing.subtype := by
    by_cases hτ : τ.val ∈ D.aPlaces
    · -- The embedding `Φ τ ∘ conj` maps the valuation ring of its prime `v` into `embValRing`.
      let v : FinPlace D.E := placeOfEmb (weightEmbedding ιₚ τ.val)
      have h_star : star (inducedPlace τ.val) = v := (placeOfEmb_comp_star _).symm
      obtain ⟨m, hm⟩ : γ ∈ intGL (D.X 0) (valuationRingAt v).toSubring := by
        rw [← localGL_mem_localIntGL_iff, ← h_star]
        exact hγ τ hτ τ.2
      let ι : valuationRingAt v →+* embValRing :=
        ((Φ τ.val).comp conj).restrict _ _ fun _ ↦ (isEquiv_placeOfEmb _).le_one_iff_le_one.2
      refine ⟨GeneralLinearGroup.map ι m, ?_⟩
      rw [← hm]
      rfl
    · -- In degree `0` the Schur matrix does not depend on its argument: take the scalar `0`.
      have q : D.X 0 ≃ Fin D.k := Fintype.equivFinOfCardEq (by simp [D.card_X 0, Data.n])
      obtain ⟨ψ, hψ⟩ := exists_schur_eq_symPowMatrix q (ite_eq_right hτ)
      have h_const (z : Matrix (D.X 0) (D.X 0) ℂ)
        (i j : WeylIndex (D.X 0) fun _ : Unit ↦ D.columnCount τ) :
          schur (fun _ : Unit ↦ D.columnCount τ) (fun _ ↦ z) i j = symPowMatrix 0 0 (ψ j)
            (ψ i) := by
        simpa using hψ 0 z i j
      exact ⟨1, Matrix.ext fun i j ↦ (h_const _ i j).trans (h_const _ i j).symm⟩
  choose m hm using h_place
  obtain ⟨M, hM⟩ : IsUnit (schur (fun τ : Subtype S ↦ D.columnCount τ) fun τ ↦ (m τ).val) := by
    simpa [weylRep] using (Group.isUnit m).map (weylRep (fun τ : Subtype S ↦ D.columnCount τ) 0)
  refine ⟨M, Matrix.ext fun i j ↦ ?_⟩
  rw [hM, ← schur_map .refl, schur_apply_eq_prod .refl, schur_apply_eq_prod .refl]
  simp only [hm]

section Columns

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]

omit [Fact p.Prime] [PadicPlace p] in
/-- On the definite space `D.X 0` the weight `(D.columnCount, D.lastEntry 0)` has no determinant
twist, so `weightRep` sends `γ` to the Schur matrix `schur D.columnCount` of the matrices `γ` with
entries mapped by `Φ τ ∘ conj`, applied to `v`. -/
lemma weightRep_column_apply (γ : U (stdSpace D.E (D.X 0)).J)
    (v : WeylIndex (D.X 0) D.columnCount → ℂ) :
    (stdSpace D.E (D.X 0)).weightRep D.columnCount (D.lastEntry 0) γ v =
      schur D.columnCount (fun τ : D.Φ ↦ (γ : GL (D.X 0) D.E).val.map ((Φ τ).comp conj)) *ᵥ v := by
  simp [stdSpace_weightRep_apply, weylRep, lastEntry]

/-- The source form with given values in `embValRing`, the `p`-integral complex numbers, at the
representatives `ρ x` of the classes. -/
def sourceFormOfValues {ρ : StdClasses (D.levelX 0) → Gf D.E (D.X 0)}
    (hρ : ∀ x : StdClasses (D.levelX 0),
      DoubleCoset.mk stdRatPoints (D.levelX 0) (ρ x) = x) :
    (StdClasses (D.levelX 0) → WeylIndex (D.X 0) D.columnCount → embValRing) →ₗ[embValRing]
      D.SourceForm :=
  (freeLevelEquiv _ _ 1 D.classAut_levelX_zero_eq_bot hρ).symm.toLinearMap.restrictScalars _ ∘ₗ
    ((Algebra.linearMap embValRing ℂ).compLeft _).compLeft _

/-- The source form with values `F` takes the value `F x` at the representative of the class `x`. -/
lemma sourceFormOfValues_apply_rep {ρ : StdClasses (D.levelX 0) → Gf D.E (D.X 0)}
    (hρ : ∀ x : StdClasses (D.levelX 0),
      DoubleCoset.mk stdRatPoints (D.levelX 0) (ρ x) = x)
    (F : StdClasses (D.levelX 0) → WeylIndex (D.X 0) D.columnCount → embValRing)
    (x : StdClasses (D.levelX 0)) :
    (sourceFormOfValues hρ F).val.val (ρ x) = fun i : WeylIndex (D.X 0) D.columnCount ↦
      (F x i : ℂ) :=
  congrFun ((freeLevelEquiv _ _ 1 D.classAut_levelX_zero_eq_bot hρ).apply_symm_apply _) x

/-- Let `ρ` pick a matrix `ρ x` in each class `x`, a double coset for the rational points and the
level. The map `sourceFormOfValues hρ` sends a family of vectors over `embValRing` to the source
form with these values at the `ρ x`. If every `ρ x` is integral at the primes above `p`, then its
range is the module of integral source forms. -/
lemma range_sourceFormOfValues {ρ : StdClasses (D.levelX 0) → Gf D.E (D.X 0)}
    (hρ : ∀ x : StdClasses (D.levelX 0),
      DoubleCoset.mk stdRatPoints (D.levelX 0) (ρ x) = x)
    (hρ_int : ∀ x : StdClasses (D.levelX 0), ρ x ∈ integralAbove (D.X 0) p) :
    (sourceFormOfValues hρ).range = D.integralSourceForms := by
  have h_mem (φ : D.SourceForm) : φ ∈ D.integralSourceForms ↔
      ∀ g : Gf D.E (D.X 0), weylGauge D.columnCount (D.lastEntry 0) g (φ.val.val g) ≤ 1 := by
    change φ.val ∈ D.SourceForm ∧ GaugeLe 1 1 φ.val ↔ _
    simp [GaugeLe]
  refine le_antisymm ?_ fun φ hφ ↦ ?_
  · -- The gauge of a source form at `η * ρ x * u` equals its gauge at `ρ x`.
    rintro _ ⟨F, rfl⟩
    refine (h_mem _).2 fun g ↦ ?_
    obtain ⟨x, η, u, rfl⟩ := exists_eq_map_mul_rep_mul _ _ hρ g
    rw [levelSpace_smoothFormRep_apply (sourceFormOfValues hρ F).2, MonoidHom.one_apply, one_smul,
      weylGauge_mul_of_mem_integralAbove _ (stdLevel_le_localLevel (IsLevel.le u.2)),
        weylGauge_embFin,
      weylGauge_le_one_iff _ (hρ_int x), sourceFormOfValues_apply_rep]
    exact fun i ↦ (F x i).2
  · let F (x : StdClasses (D.levelX 0)) (i : WeylIndex (D.X 0) D.columnCount) : embValRing :=
      ⟨φ.val.val (ρ x) i, (weylGauge_le_one_iff _ (hρ_int x)).1 ((h_mem φ).1 hφ (ρ x)) i⟩
    exact ⟨F, levelSpace_ext_doubleCosets hρ (sourceFormOfValues_apply_rep hρ F)⟩

end Columns

/-! ### The bound for the scaled Hecke operator -/

/-- Let `Λ` be a marked set of primes above `p` and `l ∈ Λ`. Let `T` be a Frobenius cycle on the
valuation ring `W` of `l`: ring maps `T.embedding i` to `embValRing` for `i` modulo `N`, alternately
even and odd, each congruent modulo `p` to the `P`-th power of the one before, with
`P = p ^ T.frobExp` and `P ^ N` the size of the residue field. Assume that `T.p = p` is not a unit,
that `t` numbers the a-places that induce `l` or `star l`, that `T.embedding i` is the embedding
`Φ (t i)`, composed with conjugation unless `i` is even, and that `heckeScalingExponent l` is `a`
times the number of even letters. With `k = D.k`, `a = D.a` and `r` the least natural number with
`D.m ≤ p ^ r` (`D.ceilLogLifts p`), assume the size conditions `IsLargeDegree`: `0 < r`, `2 r ≤ k`,
`0 < θ ≤ 1`, `a ^ 4 ≤ q` and `(N k log q / θ) ^ 5 P ^ (3 r) ≤ a`, where `q = P ^ N`. Let `Y` be the
scaled Hecke operator at `l`. Then `Y` preserves the module `M` of integral source forms, and for
every natural `j₀` the index of `Y M + p ^ j₀ M` in `M` divides `p ^ e` for a natural
`e ≤ (3 c + θ j₀) * dim`. Here `c = T.divisorConstant k a r = N a (P ^ (-2 r) + r ^ 2 / (k P))`, and
`dim` is the complex dimension of `D.SourceForm`. -/
lemma isOntoUpToColength_scaledHeckeOperator_of_frobeniusCycle {P : Parameters} {p : ℕ} {D : Data P}
    [Fact p.Prime] [PadicPlace p]
    {Λ : Finset (FinPlace D.E)} {l : FinPlace D.E} {N : ℕ} {W : ValuationSubring D.E} {θ : ℝ}
    {Q : D.Φ → Prop} [NeZero N] (hΛ : D.IsMarked Λ) (hlΛ : l ∈ Λ)
    (hW : W = (l.valuation D.E).valuationSubring) (T : FrobeniusCycle N W embValRing)
    (hp_nonunit : ¬IsUnit (T.p : embValRing)) (hTp : T.p = p) (t : ZMod N ≃ Subtype Q)
    (hQ : ∀ σ : D.Φ, Q σ ↔ σ ∈ D.aPlaces ∧ (inducedPlace σ = l ∨ inducedPlace σ = star l))
    (hι : ∀ (i : ZMod N) (x : W),
      T.embedding i x = (if T.isEven i then Φ (t i).val else (Φ (t i)).comp conj) x)
    (h_exponent : heckeScalingExponent l = D.a * #{i : ZMod N | T.isEven i})
    (h_size : T.IsLargeDegree D.k D.a (D.ceilLogLifts p) θ) (j₀ : ℕ) :
    IsOntoUpToColength (T.p : embValRing) D.integralSourceForms j₀ (hΛ.scaledHeckeOperator ⟨l, hlΛ⟩)
      ((3 * T.divisorConstant D.k D.a (D.ceilLogLifts p) + θ * j₀) * Module.finrank ℂ
        D.SourceForm) := by
  -- Evaluation at representatives of the classes turns integral source forms into families of
  -- integral vectors, and the scaled Hecke operator into the edge Hecke operator of the edges at
  -- `l`.
  classical
  subst hW
  set r : ℕ := D.ceilLogLifts p
  have hr : r < D.k := by linarith [h_size.block_pos, h_size.two_mul_block_le]
  have hl : l.IsSplit := hΛ.isSplit hlΛ
  have hp_val : l.valuation D.E p = exp (-1) := hΛ.valuation_natCast_eq_exp_neg_one hlΛ
  have hK : maxCompactAt (D.X 0) l ≤ D.levelX 0 := hΛ.maxCompactAt_le_levelX hlΛ
  have := T.finite_residueField
  have : Fintype (ParahoricCosets (valuationRingAt l) D.k r) := .ofFinite _
  -- The edges, the splitting `J` of the weight space, and the integral matrices `m e` by which the
  -- rational parts of the edges act outside `Q`.
  have q : D.X 0 ≃ Fin D.k := Fintype.equivFinOfCardEq (by simp [D.card_X 0, Data.n])
  obtain ⟨C⟩ : Nonempty (HeckeEdges D.k p r (D.levelX 0) hl) :=
    nonempty_heckeEdges r (D.levelX 0) hl q (hΛ.natCast_mem_asIdeal hlΛ)
  have h_aPlace (i : ZMod N) : (t i).val ∈ D.aPlaces := ((hQ (t i)).1 (t i).2).1
  let H : Type := WeylIndex (D.X 0) fun τ : {τ : D.Φ // ¬Q τ} ↦ D.columnCount τ
  obtain ⟨J, hJ⟩ : ∃ J : WeylIndex (D.X 0) D.columnCount ≃ Exponents N D.k D.a × H,
      ∀ (c : ZMod N → ℂ) (z : D.Φ → Matrix (D.X 0) (D.X 0) ℂ)
        (i j : WeylIndex (D.X 0) D.columnCount),
        (∏ s : ZMod N, c s) ^ D.a * schur D.columnCount z i j =
          schur (fun τ : {τ : D.Φ // ¬Q τ} ↦ D.columnCount τ) (fun τ ↦ z τ) (J i).2 (J j).2 *
            kroneckerPi (fun s : ZMod N ↦
              symPowMatrix D.a (c s • (z (t s))ᵀ.submatrix C.numbering.symm C.numbering.symm))
              (J j).1 (J i).1 :=
    exists_weylIndex_equiv C.numbering t h_aPlace
  have h_off (e : ClassEdges (D.levelX 0) l D.k r) :
      ∃ m : GL H embValRing,
        schur (fun τ : {τ : D.Φ // ¬Q τ} ↦ D.columnCount τ)
          (fun τ ↦ (C.rationalPart e).val.val.map ((Φ τ.val).comp conj)) =
            m.val.map embValRing.subtype := by
    refine exists_schur_eq_map fun τ hτ hτQ ↦ ?_
    obtain ⟨h_ne, h_ne_star⟩ : inducedPlace τ ≠ l ∧ inducedPlace τ ≠ star l := by
      simpa [hQ, hτ] using hτQ
    exact C.localGL_rationalPart_mem_localIntGL e (by simpa using D.p_mem_inducedPlace τ)
      (star_involutive.eq_iff.not.2 h_ne_star) (by rwa [star_star])
  choose m hm using h_off
  let 𝓔 : EdgeCoordinates (valuationRingAt l) embValRing D.k r (StdClasses (D.levelX 0)) H :=
    { origin := C.origin
      originBasisChange := C.originBasisChange
      terminusBasisChange b := b.out⁻¹
      transition := m
      mk_terminusBasisChange_inv b := by rw [inv_inv, QuotientGroup.out_eq']
      eq_of_origin_eq := C.eq_of_origin_eq_of_mem_parahoric hp_val hK
        D.classAut_levelX_zero_eq_bot }
  let f : (StdClasses (D.levelX 0) → WeylIndex (D.X 0) D.columnCount → embValRing)
      →ₗ[embValRing] D.SourceForm := sourceFormOfValues C.mk_rep
  -- The matrix of a rational part on the weight space, times `p ^ heckeScalingExponent l`, is the
  -- term of its edge in the edge Hecke operator.
  have h_edge (x : StdClasses (D.levelX 0)) (b : ParahoricCosets (valuationRingAt l) D.k r)
      (i j : WeylIndex (D.X 0) D.columnCount) :
      (p : ℂ) ^ heckeScalingExponent l *
          schur D.columnCount (fun τ ↦ (C.rationalPart (x, b)).val.val.map ((Φ τ).comp conj)) i j =
        𝓔.transition (x, b) (J i).2 (J j).2 *
          (T.letterRep D.a (𝓔.originBasisChange (x, b)) * T.depthPower D.k D.a r *
            T.letterRep D.a (𝓔.terminusBasisChange b)) (J j).1 (J i).1 := by
    rw [h_exponent, pow_mul', ← prod_const, prod_filter, hJ, hm,
      kroneckerPi_symPowMatrix_eq_letterRep T hTp C.numbering D.a (fun i : ZMod N ↦ Φ (t i).val) hι
        (C.rationalPart_inv x b)]
    -- it remains to unfold the fields of `𝓔`
    rfl
  -- At the representative of `x` both operators are sums over the edges into `x`.
  have h_lift : hΛ.scaledHeckeOperator ⟨l, hlΛ⟩ ∘ₗ f = f ∘ₗ T.edgeHeckeOperator D.a J 𝓔 := by
    refine LinearMap.ext fun F ↦ levelSpace_ext_doubleCosets C.mk_rep fun x ↦ ?_
    change (p : ℂ) ^ heckeScalingExponent l •
        (heckeSplit (algFormRep D.columnCount (D.lastEntry 0)) hl r (f F).val).val (C.rep x) =
      (f (T.edgeHeckeOperator D.a J 𝓔 F)).val.val (C.rep x)
    have h_origin : C.origin = 𝓔.origin := rfl
    rw [C.heckeSplit_apply_rep hp_val hr hK (f F).2, sourceFormOfValues_apply_rep,
      edgeHeckeOperator_apply]
    -- In each coordinate, `h_edge` identifies the two matrix coefficients of every edge.
    ext i
    push_cast
    simp only [f, sourceFormOfValues_apply_rep, weightRep_column_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, mulVec, dotProduct, mul_sum, ← mul_assoc, h_edge, h_origin]
  have h_dim : (Module.finrank ℂ D.SourceForm : ℝ) =
      Nat.card (StdClasses (D.levelX 0)) * Nat.card (WeylIndex (D.X 0) D.columnCount) := by
    simp [finrank_levelSpace_smoothFormRep D.classAut_levelX_zero_eq_bot]
  rw [h_dim, ← range_sourceFormOfValues C.mk_rep C.rep_mem_integralAbove]
  exact T.elementary_divisors hp_nonunit h_size J 𝓔 f h_lift j₀

end New.Columns

end TwistedHeckeType
