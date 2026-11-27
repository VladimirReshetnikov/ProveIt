import Lib.General.Algebra.FittingIdealsAndLengths

/-!
# A matrix of relations with small block determinant valuation

Linear algebra over a discrete valuation ring O (written `DVR O`) with normalized valuation
v = `addVal O` and fraction field K. The valuation of a determinant of relations is bounded by the
length of a module of solutions, taken modulo an element p or in K/O.

* `New.Selmer.exists_rows_addVal_det_le`: let ψ : A → M_d(O) be onto, N an A-submodule of A^ι, p ≠ 0
  and b < v(p). If the vectors modulo p killed by ψ(N) lie in a module of length at most b, then
  some square matrix B with rows in N has v(det ψ(B)) ≤ b, with ψ(B) read as a block matrix.
* `New.Selmer.divQuot`: the map x ↦ x/p from O/p to K/O (`New.Selmer.DivisibleQuot`). For p ≠ 0 it
  is injective with image the p-torsion.
* `New.Selmer.exists_rows_addVal_det_le_of_divisible`: the same bound when the vectors with entries
  in K/O killed by ψ(N) lie in a module of length at most b. It follows from the form modulo p and
  is the form that Ribet's lemma uses.

The idea: as ψ is onto, any d linear forms in the span of the rows of the ψ(t), t ∈ N, are the rows
of one ψ(t). So a basis of this span, divided into groups of d forms, gives B. The length of the
solutions bounds the determinant of such a basis by the duality lemma
`New.exists_matrix_addVal_det_le_length` for lattices in O^n.

## Relation to the literature

General linear algebra over a discrete valuation ring (elementary divisors).
-/

open IsDiscreteValuationRing Matrix Module Submodule Fintype Ideal LinearMap

/-- Let O be a discrete valuation ring (`DVR O`) with normalized valuation v = `addVal O`, let
ψ : A → M_d(O) be onto, N an A-submodule of A^ι, p ≠ 0 and b < v(p). Write `QuotSpan p` for O/p,
on whose vectors indexed by d the matrices act by multiplication. If all w in ((O/p)^d)^ι with
∑ j, ψ(t j) • w_j = 0 for every t ∈ N lie in a submodule Z of length at most b, then some square
matrix B with rows in N has v(det ψ(B)) ≤ b, where ψ(B) is read as a block matrix. -/
lemma New.Selmer.exists_rows_addVal_det_le {O ι A d : Type} [CommRing O] [DVR O] [Fintype ι]
    [DecidableEq ι] [Ring A] [Algebra O A] [Fintype d] [DecidableEq d] (ψ : A →ₐ[O] Matrix d d O)
    (hψ : Function.Surjective ψ) (N : Submodule A (ι → A)) {p : O} (hp : p ≠ 0) {b : ℕ∞}
    (hb : b < addVal O p) {Z : Submodule O (ι → d → QuotSpan p)} (hZ : length O Z ≤ b)
    (hZ_mem : ∀ w : ι → d → QuotSpan p, (∀ t ∈ N, ∑ j : ι, ψ (t j) • w j = 0) → w ∈ Z) :
    ∃ B : Matrix ι ι A,
      (∀ i : ι, B i ∈ N) ∧ addVal O (Matrix.comp ι ι d d O (B.map ψ)).det ≤ b := by
  -- Let σ(t) ∈ O^(ι × d) be the sum of the rows of the d × (ι × d) matrix ψ(t). As ψ is onto, σ(N)
  -- is the span of all rows of the ψ(t), t ∈ N. Apply duality to the lattice
  -- L = p·O^(ι × d) + σ(N): there are a matrix M with rows in L and an S with annihilator L and
  -- v(det M) ≤ length S. This S embeds in Z, so v(det M) ≤ b. Modulo p the rows of M, in groups of
  -- d, are the rows of some ψ(B), and b < v(p), so det ψ(B) has the valuation of det M.
  obtain ⟨E, hE : ∀ X : Matrix d d O, ψ (E X) = X⟩ := hψ.hasRightInverse
  let σ : (ι → A) →ₗ[O] (ι × d → O) :=
    .pi fun x : ι × d ↦ ∑ c : d, entryLinearMap O O c x.2 ∘ₗ ψ.toLinearMap ∘ₗ proj x.1
  have σ_apply (s : ι → A) (j : ι) (l : d) : σ s (j, l) = ∑ c : d, ψ (s j) c l := by simp [σ]
  let L : Submodule O (ι × d → O) := range (p • .id) ⊔ (N.restrictScalars O).map σ
  -- The rows of M lie in L, and L is the annihilator of S in O^(ι × d).
  obtain ⟨M, S, M_mem, mem_L, det_le⟩ :=
    exists_matrix_addVal_det_le_length L hp fun v ↦ mem_sup_left ⟨v, rfl⟩
  have S_le : S ≤ Z.map (LinearEquiv.curry O (QuotSpan p) ι d).symm.toLinearMap := by
    refine fun w hw ↦ ⟨fun j l ↦ w (j, l), hZ_mem _ fun s hs ↦ funext fun i ↦ ?_, rfl⟩
    -- Row i of ψ(s) is σ(e • s), with e a preimage of the matrix unit at (i, i).
    let e : A := E (.single i i 1)
    have h_orth : ∑ x : ι × d, σ (e • s) x • w x = 0 :=
      (mem_L _).1 (mem_sup_right (mem_map_of_mem (N.smul_mem e hs))) w hw
    have σ_row (j : ι) (l : d) : σ (e • s) (j, l) = ψ (s j) i l := by
      simp [e, σ_apply, hE, mul_apply, Matrix.single_apply, ite_and]
    simpa [σ_row, sum_prod_type] using h_orth
  have det_M : addVal O M.det ≤ b := by grw [det_le, length_le_of_le_map _ Z S_le, hZ]
  have M_row (k : ι) (c : d) : ∃ u : ι × d → O, ∃ s ∈ N, p • u + σ s = M (k, c) := by
    simpa [L, mem_sup] using M_mem (k, c)
  choose u t t_mem M_eq using M_row
  -- The matrix with ones in row c puts σ(t k c) into row c, so row (k, c) of ψ(B) is σ(t k c).
  let B : Matrix ι ι A := of fun k : ι ↦ ∑ c : d, E (updateRow 0 c 1) • t k c
  refine ⟨B, fun k ↦ N.sum_mem fun c _ ↦ N.smul_mem _ (t_mem k c), ?_⟩
  set ψB : Matrix (ι × d) (ι × d) O := comp ι ι d d O (B.map ψ)
  have B_apply (k j : ι) (c l : d) : ψB (k, c) (j, l) = σ (t k c) (j, l) := by
    simp [ψB, B, σ_apply, hE, mul_apply, Matrix.sum_apply, updateRow_apply]
  have congr_p : p ∣ ψB.det - M.det := by
    rw [← Quotient.eq_zero_iff_dvd, map_sub, sub_eq_zero, RingHom.map_det, RingHom.map_det]
    congr 1
    ext ⟨k, c⟩ ⟨j, l⟩
    simp [B_apply, ← M_eq]
  have h_lt : addVal O M.det < addVal O (ψB.det - M.det) :=
    det_M.trans_lt (hb.trans_le (addVal_le_iff_dvd.2 congr_p))
  rwa [AddValuation.map_eq_of_lt_sub _ h_lt]

namespace New.Selmer

variable {O : Type} [CommRing O] [DVR O]

variable (O) in
/-- The divisible module K/O, where K = Frac(O). -/
abbrev DivisibleQuot : Type := FractionRing O ⧸ (1 : Submodule O (FractionRing O))

/-- Division by `a`, from O/a to K/O: the class of t goes to the class of t/a. -/
noncomputable def divQuot (a : O) : QuotSpan a →ₗ[O] DivisibleQuot O :=
  (Ideal.span {a}).liftQ ((1 : Submodule O (FractionRing O)).mkQ ∘ₗ
      LinearMap.toSpanSingleton O (FractionRing O) (algebraMap O (FractionRing O) a)⁻¹)
    (by
      rw [Ideal.span_singleton_le_iff_mem, mem_ker, LinearMap.comp_apply]
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      · exact (Submodule.Quotient.mk_eq_zero _).2 (mem_one.2 ⟨1, by simp [Algebra.smul_def, ha]⟩))

lemma divQuot_mk (a t : O) : divQuot a (Ideal.Quotient.mk _ t) =
    Submodule.Quotient.mk (t • (algebraMap O (FractionRing O) a)⁻¹) := rfl

lemma divQuot_injective {a : O} (ha : a ≠ 0) : Function.Injective (divQuot a) := by
  rw [injective_iff_map_eq_zero, Ideal.Quotient.mk_surjective.forall]
  intro t ht
  rw [divQuot_mk, Submodule.Quotient.mk_eq_zero, mem_one] at ht
  obtain ⟨s, hs⟩ := ht -- s = t/a in K
  refine (Ideal.Quotient.eq_zero_iff_dvd ..).2 ⟨s, IsFractionRing.injective O (FractionRing O) ?_⟩
  simp [map_mul, hs, ha, Algebra.smul_def, mul_left_comm (algebraMap O (FractionRing O) a)]

/-- An element of K/O killed by `a ≠ 0` is the image of some x in O/a under division by `a`. -/
lemma exists_divQuot_eq {a : O} (ha : a ≠ 0) {y : DivisibleQuot O} (hy : a • y = 0) :
    ∃ x : QuotSpan a, divQuot a x = y := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_one] at hy
  obtain ⟨s, hs⟩ := hy
  exact ⟨Ideal.Quotient.mk _ s, by simp [divQuot_mk, Algebra.smul_def, hs, ha, mul_comm _ r]⟩

lemma exists_smul_eq_zero_divisibleQuot (y : DivisibleQuot O) : ∃ d : O, d ≠ 0 ∧ d • y = 0 := by
  induction y using Submodule.Quotient.induction_on with | _ r =>
  obtain ⟨d, s, hs⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors O) r
  exact ⟨d, nonZeroDivisors.coe_ne_zero d, (Submodule.Quotient.mk_eq_zero _).2 (mem_one.2 ⟨s, hs⟩)⟩

/-- Let `X` be a torsion module over a discrete valuation ring `O` with additive valuation `v`. If
the `a`-torsion of `X` is not all of `X`, then it contains a copy of `O / a`, so its length is at
least `v(a)`. -/
lemma addVal_le_length_torsionBy {X : Type} [AddCommGroup X] [Module O X] {a : O}
    (hX : ∀ z : X, ∃ a' : O, a' ≠ 0 ∧ a' • z = 0) (h_ne : torsionBy O X a ≠ ⊤) :
    addVal O a ≤ length O (torsionBy O X a) := by
  obtain ⟨z, hz⟩ : ∃ z : X, a • z ≠ 0 := by simpa [eq_top_iff'] using h_ne
  -- The annihilator of `z` is generated by some `b`, which does not divide `a`; so `b = a c`.
  obtain ⟨b, hb⟩ : ∃ b : O, ∀ t : O, t • z = 0 ↔ b ∣ t :=
    (IsPrincipalIdealRing.principal (torsionOf O X z)).principal.imp fun b h_ann t ↦ by
      rw [← mem_torsionOf_iff, h_ann, Ideal.mem_span_singleton]
  obtain ⟨c, rfl⟩ : a ∣ b := (ValuationRing.dvd_total a b).resolve_right fun h ↦ hz ((hb a).2 h)
  have hc : c ≠ 0 := by
    rintro rfl
    simpa [hb] using hX z
  -- The element `w = c z` is killed exactly by the multiples of `a`, so `t ↦ t w` embeds `O / a`.
  let w : torsionBy O X a := ⟨c • z, by simp [smul_smul, hb]⟩
  let mulW : O →ₗ[O] torsionBy O X a := LinearMap.toSpanSingleton O _ w
  have h_ker : Ideal.span {a} = LinearMap.ker mulW := by
    ext t
    have h_smul : t • w = 0 ↔ a * c ∣ t * c := by simp [w, Subtype.ext_iff, smul_smul, hb]
    simp [mulW, h_smul, Ideal.mem_span_singleton, mul_dvd_mul_iff_right hc]
  rw [← length_quot_span_eq_addVal]
  exact length_le_of_injective ((Ideal.span {a}).liftQ mulW h_ker.le)
    (LinearMap.ker_eq_bot.1 ((Ideal.span {a}).ker_liftQ_eq_bot' mulW h_ker))

/-- Let O be a discrete valuation ring with normalized valuation v = `addVal O` and fraction field
K, and write `DivisibleQuot O` for K/O. Let ψ : A → M_d(O) be onto and N an A-submodule of A^ι.
If all w in ((K/O)^d)^ι with ∑ j, ψ(t j) • w_j = 0 for every t ∈ N lie in a submodule Z of length
at most b, then some square matrix B with rows in N has v(det ψ(B)) ≤ b, where ψ(B) is read as a
block matrix. A matrix acts on (K/O)^d by multiplication. -/
lemma exists_rows_addVal_det_le_of_divisible {ι A d : Type} [Fintype ι] [DecidableEq ι] [Ring A]
    [Algebra O A] [Fintype d] [DecidableEq d] (ψ : A →ₐ[O] Matrix d d O)
    (hψ : Function.Surjective ψ) (N : Submodule A (ι → A)) {b : ℕ}
    {Z : Submodule O (ι → d → DivisibleQuot O)} (hZ : length O Z ≤ b)
    (hZ_mem : ∀ w : ι → d → DivisibleQuot O, (∀ t ∈ N, ∑ j : ι, ψ (t j) • w j = 0) → w ∈ Z) :
    ∃ B : Matrix ι ι A,
      (∀ i : ι, B i ∈ N) ∧ addVal O (Matrix.comp ι ι d d O (B.map ψ)).det ≤ b := by
  -- Take `p = ϖ ^ (b + 1)`. Division by `p` embeds the vectors modulo `p` killed by `N` in `Z`.
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  let p : O := ϖ ^ (b + 1)
  have hp : p ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hb : (b : ℕ∞) < addVal O p := by simp [p, hϖ, ENat.lt_natCast_add_one_iff]
  let E : (ι → d → QuotSpan p) →ₗ[O] (ι → d → DivisibleQuot O) :=
    ((divQuot p).compLeft d).compLeft ι
  have hE : Function.Injective E := (divQuot_injective hp).comp_left.comp_left
  have h_length : length O (Z.comap E) ≤ length O Z :=
    length_le_of_injective (E.restrict fun _ hw ↦ hw) fun _ _ h ↦
      Subtype.ext (hE (congrArg Subtype.val h))
  refine exists_rows_addVal_det_le ψ hψ N hp hb (h_length.trans hZ) fun w hw ↦
    hZ_mem (E w) fun t ht ↦ ?_
  have h_comm (j : ι) : ψ (t j) • E w j = (divQuot p).compLeft d (ψ (t j) • w j) :=
    funext fun l ↦ by simp [E, map_sum, map_smul]
  simp only [h_comm, ← map_sum, hw t ht, map_zero]

end New.Selmer
