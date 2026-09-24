import Mathlib.Analysis.Complex.Basic
import Surreal.HahnSeries.WickDomain

/-!
# Sign-coherent Wick families: raw and order-grouped strong summability

This file proves `wick:prop:signcoherent` of
`docs/surcomplex/wick-summability-certificates/article.tex`.

**Generic core.** A Hahn series is *coefficientwise nonnegative* (`CoeffNonneg`) when every
coefficient is `≥ 0`. For a family `T : ι → R((t^Γ))` and a map `π : ι → κ` with finite fibres,
`blockSum π hπ T b = ∑_{π i = b} T i` is the family of block sums. We prove:
* `stronglySummable_blockSum`: finite regrouping of a strongly summable family is strongly
  summable (no hypothesis on the terms);
* `stronglySummable_iff_of_support`: if no block erases support, the converse holds;
* `support_sum_eq_biUnion`, `support_sum_smul_eq`: a finite sum of coefficientwise nonnegative
  series, even after multiplication by one common scalar, has exactly the union of the supports;
* `stronglySummable_iff_blockSum`: if `T i = c (π i) • U i` with `U i` coefficientwise
  nonnegative and one scalar `c b` per block, then `T` is strongly summable iff its block
  family is. This holds for any semiring without zero divisors with a partial order compatible
  with addition (so for `ℂ` with its partial order `ComplexOrder`), for any partially ordered
  `Γ`, and with no condition `c b ≠ 0`.

**Wick instantiation.** With the Wick data, atoms and sectors of
`Surreal/HahnSeries/WickDomain.lean` (namespace `Surreal.WickDomain`: `atom`, `sector`, and
`StronglySummable`, which is `wick:def:strong`),
`orderBlock α ends g C β n` is the finite sum of the atoms `T_β(m, k)`, `(m, k) ∈ Q_β`, of total
interaction order `|m| = n` (finite by `finite_orderFiber`). If `gₐ = σ uₐ` with one common
`σ` and coefficientwise nonnegative `uₐ`, and all covariance entries are coefficientwise
nonnegative, then `atom_eq_pow_smul` writes each atom as `σ^{|m|}` times a coefficientwise
nonnegative series (its multiplier `W(Am + β, k) / ∏ₐ mₐ!` is a positive rational), and
* `support_orderBlock`: the support of an order block is the union of its atoms' supports;
* `stronglySummable_atom_iff_orderBlock`: (i) ⟺ (ii) of `wick:prop:signcoherent`;
* `signCoherent_tfae`: for a pairable sector (`Q_β ≠ ∅`), (i) and (ii) are equivalent to the
  conditions of `wick:thm:main` (`Surreal.WickDomain.main_tfae`).
These hold over any field `R` with a partial order making it an ordered ring in which
`PosMulReflectLT` holds (so casts of nonnegative rationals are nonnegative); this covers `ℝ` and
`ℂ` with `ComplexOrder`. The last item also assumes `σ ≠ 0`, `uₐ ≠ 0`, `Cₑ ≠ 0`, a nontrivial
divisible `Γ` and `CharZero R`.

**The source's setting.** `stronglySummable_atom_iff_orderBlock_complex` and
`signCoherent_tfae_complex` state the proposition for `K = ℂ((t^Γ))` and a covariance matrix
`C` with edge set `{(i, j) : i ≤ j, C_ij ≠ 0}` (`Surreal.WickDomain.MatrixEdge`), where
"coefficientwise nonnegative" is literally "every coefficient is a nonnegative real number"
(`coeffNonneg_complex_iff`).

**Generality.** The equivalence (i) ⟺ (ii) needs neither `σ ≠ 0`, nor `uₐ ≠ 0`, nor nonzero
covariance entries, nor divisibility of `Γ`; these hypotheses of the source are used only for
the final clause, whose proof is `wick:thm:main`. The pairing count `wick:lem:wickcount` is not
used: the atoms are given by the closed formula `wick:eq:atom`, of which only the positivity of
the rational multiplier enters. Nothing of `wick:prop:signcoherent` is pending.
-/

namespace Surreal.SignCoherent

open _root_.HahnSeries Surreal.WickDomain Surreal.Wick

noncomputable section

/-! ### Coefficientwise nonnegative Hahn series -/

section Nonneg

variable {Γ R : Type*}

/-- A Hahn series is *coefficientwise nonnegative* if every coefficient is `≥ 0`
(`wick:sec:cancellation`). Over `ℂ` with `ComplexOrder` this says that every coefficient is a
nonnegative real number (`coeffNonneg_complex_iff`). -/
def CoeffNonneg [PartialOrder Γ] [Zero R] [LE R] (f : R⟦Γ⟧) : Prop :=
  ∀ γ, 0 ≤ f.coeff γ

section Semiring

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommSemiring R]
  [PartialOrder R] [IsOrderedRing R]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- A nonnegative multiple of a coefficientwise nonnegative series is coefficientwise
nonnegative. -/
theorem CoeffNonneg.smul {c : R} (hc : 0 ≤ c) {f : R⟦Γ⟧} (hf : CoeffNonneg f) :
    CoeffNonneg (c • f) := fun γ => by
  rw [coeff_smul, smul_eq_mul]
  exact mul_nonneg hc (hf γ)

/-- The product of two coefficientwise nonnegative series is coefficientwise nonnegative. -/
theorem CoeffNonneg.mul {f h : R⟦Γ⟧} (hf : CoeffNonneg f) (hh : CoeffNonneg h) :
    CoeffNonneg (f * h) := fun γ => by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hf _) (hh _)

omit [IsOrderedCancelAddMonoid Γ] in
/-- The unit series is coefficientwise nonnegative. -/
theorem coeffNonneg_one : CoeffNonneg (1 : R⟦Γ⟧) := fun γ => by
  rw [coeff_one]
  split_ifs
  · exact zero_le_one
  · exact le_rfl

/-- A finite product of coefficientwise nonnegative series is coefficientwise nonnegative. -/
theorem coeffNonneg_prod {ι : Type*} (s : Finset ι) (f : ι → R⟦Γ⟧)
    (hf : ∀ i ∈ s, CoeffNonneg (f i)) : CoeffNonneg (∏ i ∈ s, f i) :=
  Finset.prod_induction f CoeffNonneg (fun _ _ ha hb => ha.mul hb) coeffNonneg_one hf

/-- Powers of a coefficientwise nonnegative series are coefficientwise nonnegative. -/
theorem CoeffNonneg.pow {f : R⟦Γ⟧} (hf : CoeffNonneg f) (n : ℕ) : CoeffNonneg (f ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using coeffNonneg_one
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hf

end Semiring

/-- In a partially ordered field satisfying `PosMulReflectLT` (for instance `ℝ`, or `ℂ` with
`ComplexOrder`), nonnegative rationals are nonnegative. -/
theorem ratCast_nonneg {K : Type*} [Field K] [PartialOrder K] [IsOrderedRing K]
    [PosMulReflectLT K] {q : ℚ} (hq : 0 ≤ q) : 0 ≤ (q : K) := by
  have hnum : (0 : K) ≤ (q.num : K) := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Rat.num_nonneg.2 hq)
    rw [hn, Int.cast_natCast]
    exact Nat.cast_nonneg n
  rw [Rat.cast_def]
  exact div_nonneg hnum (Nat.cast_nonneg _)

open scoped ComplexOrder in
/-- Over `ℂ` with `ComplexOrder`, coefficientwise nonnegativity is the source's condition:
every coefficient is a nonnegative real number. -/
theorem coeffNonneg_complex_iff [PartialOrder Γ] (f : ℂ⟦Γ⟧) :
    CoeffNonneg f ↔ ∀ γ, ∃ r : ℝ, 0 ≤ r ∧ f.coeff γ = r := by
  refine forall_congr' fun γ => ⟨fun h => ?_, ?_⟩
  · refine ⟨(f.coeff γ).re, (Complex.nonneg_iff.1 h).1, Complex.ext rfl ?_⟩
    simpa using (Complex.nonneg_iff.1 h).2.symm
  · rintro ⟨r, hr, e⟩
    rw [e]
    exact Complex.zero_le_real.2 hr

end Nonneg

/-! ### Supports of finite sums and finite regrouping -/

section Blocks

variable {Γ R ι κ : Type*} [PartialOrder Γ]

section AddCommMonoid

variable [AddCommMonoid R]

/-- Every exponent in the support of a finite sum lies in the support of a summand. -/
theorem support_finsetSum_subset (s : Finset ι) (T : ι → R⟦Γ⟧) :
    (∑ i ∈ s, T i).support ⊆ ⋃ i ∈ s, (T i).support := by
  intro γ hγ
  rw [mem_support, coeff_sum] at hγ
  obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
  exact Set.mem_biUnion hi ((mem_support _ _).2 h)

/-- The block sums `b ↦ ∑_{π i = b} T i` of a family `T` along a map `π` with finite fibres:
the family obtained by finite regrouping of `T`. -/
def blockSum (π : ι → κ) (hπ : ∀ b, (π ⁻¹' {b}).Finite) (T : ι → R⟦Γ⟧) (b : κ) : R⟦Γ⟧ :=
  ∑ i ∈ (hπ b).toFinset, T i

/-- The finite block over `b` consists of the indices `i` with `π i = b`. -/
@[simp]
theorem mem_blockFinset {π : ι → κ} (hπ : ∀ b, (π ⁻¹' {b}).Finite) {i : ι} {b : κ} :
    i ∈ (hπ b).toFinset ↔ π i = b := by
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]

/-- Finite regrouping preserves strong summability (the ordinary regrouping property of strong
sums used in the proof of `wick:prop:signcoherent`, for strong summability as in
`wick:def:strong`): the block family of a strongly summable family is strongly summable. -/
theorem stronglySummable_blockSum (π : ι → κ) (hπ : ∀ b, (π ⁻¹' {b}).Finite)
    {T : ι → R⟦Γ⟧} (hT : StronglySummable T) : StronglySummable (blockSum π hπ T) := by
  rw [stronglySummable_iff] at hT ⊢
  refine ⟨hT.1.mono ?_, fun γ => ((hT.2 γ).image π).subset ?_⟩
  · refine Set.iUnion_subset fun b => (support_finsetSum_subset _ T).trans ?_
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion (fun j => (T j).support) i
  · intro b hb
    have hb' : γ ∈ (blockSum π hπ T b).support := hb
    obtain ⟨i, hi, hγ⟩ := Set.mem_iUnion₂.1 (support_finsetSum_subset _ T hb')
    exact ⟨i, hγ, (mem_blockFinset hπ).1 hi⟩

/-- The converse of finite regrouping, when no block erases support (the step (ii) ⟹ (i) in the
proof of `wick:prop:signcoherent`): if the support of every block sum contains the supports of
its members, strong summability of the block family implies strong summability of the original
family. -/
theorem stronglySummable_of_blockSum (π : ι → κ) (hπ : ∀ b, (π ⁻¹' {b}).Finite)
    {T : ι → R⟦Γ⟧}
    (hsupp : ∀ b, ⋃ i ∈ (hπ b).toFinset, (T i).support ⊆ (blockSum π hπ T b).support)
    (hB : StronglySummable (blockSum π hπ T)) : StronglySummable T := by
  have key : ∀ i, (T i).support ⊆ (blockSum π hπ T (π i)).support := fun i =>
    (Set.subset_biUnion_of_mem (u := fun j => (T j).support)
      ((mem_blockFinset hπ).2 rfl)).trans (hsupp (π i))
  rw [stronglySummable_iff] at hB ⊢
  refine ⟨hB.1.mono ?_, fun γ => ?_⟩
  · exact Set.iUnion_subset fun i => (key i).trans
      (Set.subset_iUnion (fun b => (blockSum π hπ T b).support) (π i))
  · refine ((hB.2 γ).biUnion fun b _ => ((hπ b).toFinset : Set ι).toFinite).subset ?_
    intro i hi
    refine Set.mem_iUnion₂.2 ⟨π i, key i hi, ?_⟩
    exact Finset.mem_coe.2 ((mem_blockFinset hπ).2 rfl)

/-- Proof of `wick:prop:signcoherent`, abstract regrouping step: when no block erases support,
a family is strongly summable if and only if its family of finite block sums is. The hypothesis
on supports is the one whose failure is exhibited in `wick:sec:cancellation`. -/
theorem stronglySummable_iff_of_support (π : ι → κ) (hπ : ∀ b, (π ⁻¹' {b}).Finite)
    {T : ι → R⟦Γ⟧}
    (hsupp : ∀ b, ⋃ i ∈ (hπ b).toFinset, (T i).support ⊆ (blockSum π hπ T b).support) :
    StronglySummable T ↔ StronglySummable (blockSum π hπ T) :=
  ⟨stronglySummable_blockSum π hπ, stronglySummable_of_blockSum π hπ hsupp⟩

end AddCommMonoid

section Ordered

/-- A finite sum of coefficientwise nonnegative series has no cancellation: its support is the
union of the supports of the summands. -/
theorem support_sum_eq_biUnion [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    (s : Finset ι) (U : ι → R⟦Γ⟧) (hU : ∀ i ∈ s, CoeffNonneg (U i)) :
    (∑ i ∈ s, U i).support = ⋃ i ∈ s, (U i).support := by
  refine (support_finsetSum_subset s U).antisymm fun γ hγ => ?_
  obtain ⟨i, hi, hγ⟩ := Set.mem_iUnion₂.1 hγ
  rw [mem_support] at hγ ⊢
  rw [coeff_sum]
  intro h0
  exact hγ ((Finset.sum_eq_zero_iff_of_nonneg fun j hj => hU j hj γ).1 h0 i hi)

variable [Semiring R] [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R]

/-- A finite sum of coefficientwise nonnegative series multiplied by one common scalar `c`
(a sign-coherent block) has no cancellation: its support is the union of the supports of the
summands. No condition `c ≠ 0` is needed. -/
theorem support_sum_smul_eq (s : Finset ι) (c : R) (U : ι → R⟦Γ⟧)
    (hU : ∀ i ∈ s, CoeffNonneg (U i)) :
    (∑ i ∈ s, c • U i).support = ⋃ i ∈ s, (c • U i).support := by
  refine (support_finsetSum_subset s _).antisymm fun γ hγ => ?_
  obtain ⟨i, hi, hγ⟩ := Set.mem_iUnion₂.1 hγ
  rw [mem_support, coeff_smul, smul_eq_mul] at hγ
  rw [← Finset.smul_sum, mem_support, coeff_smul, smul_eq_mul]
  refine mul_ne_zero (left_ne_zero_of_mul hγ) ?_
  have hsum : γ ∈ (∑ j ∈ s, U j).support := by
    rw [support_sum_eq_biUnion s U hU]
    exact Set.mem_biUnion hi ((mem_support _ _).2 (right_ne_zero_of_mul hγ))
  exact (mem_support _ _).1 hsum

/-- The support of a sign-coherent block is the union of the supports of its members. -/
theorem support_blockSum (π : ι → κ) (hπ : ∀ b, (π ⁻¹' {b}).Finite) (c : κ → R)
    (U : ι → R⟦Γ⟧) (hU : ∀ i, CoeffNonneg (U i)) {T : ι → R⟦Γ⟧}
    (hT : ∀ i, T i = c (π i) • U i) (b : κ) :
    (blockSum π hπ T b).support = ⋃ i ∈ (hπ b).toFinset, (T i).support := by
  have hTb : ∀ i ∈ (hπ b).toFinset, T i = c b • U i := fun i hi => by
    rw [hT i, (mem_blockFinset hπ).1 hi]
  have e : blockSum π hπ T b = ∑ i ∈ (hπ b).toFinset, c b • U i :=
    Finset.sum_congr rfl hTb
  rw [e, support_sum_smul_eq _ (c b) U fun i _ => hU i]
  exact Set.iUnion₂_congr fun i hi => by rw [hTb i hi]

/-- `wick:prop:signcoherent`, generic block-sum core. Let `T i = c (π i) • U i`, where the
`U i` are coefficientwise nonnegative and the scalar `c b` depends only on the block `b = π i`,
and let the blocks `π ⁻¹' {b}` be finite. Then `T` is strongly summable iff its family of
block sums is: the support of every block is the union of the supports of its members. -/
theorem stronglySummable_iff_blockSum (π : ι → κ) (hπ : ∀ b, (π ⁻¹' {b}).Finite) (c : κ → R)
    (U : ι → R⟦Γ⟧) (hU : ∀ i, CoeffNonneg (U i)) {T : ι → R⟦Γ⟧}
    (hT : ∀ i, T i = c (π i) • U i) :
    StronglySummable T ↔ StronglySummable (blockSum π hπ T) :=
  stronglySummable_iff_of_support π hπ fun b =>
    (support_blockSum π hπ c U hU hT b).symm.subset

end Ordered

end Blocks

/-! ### Order blocks of a Wick sector -/

section WickBlocks

variable {V A E : Type*} [Fintype V] [DecidableEq V] [Fintype A] [Fintype E]

omit [Fintype E] in
/-- The total interaction order `|m| = ∑ₐ mₐ` of a count vector `q = (m, k)`. -/
def interactionOrder (q : A ⊕ E → ℕ) : ℕ :=
  ∑ a, q (Sum.inl a)

variable (α : A → V → ℕ) (ends : E → V × V)

omit [Fintype V] in
/-- Each order block of a sector is finite: `|m| = n` bounds every `mₐ` by `n`, and then
`Am + β = Dk` bounds every contraction count `kₑ`. -/
theorem finite_orderFiber (β : V → ℕ) (n : ℕ) :
    ((fun q : sector α ends β => interactionOrder q.1) ⁻¹' {n}).Finite := by
  let bnd : A ⊕ E → ℕ :=
    Sum.elim (fun _ => n) fun e => ∑ a, n * α a (ends e).1 + β (ends e).1
  have key : {q : A ⊕ E → ℕ | q ∈ sector α ends β ∧ interactionOrder q = n} ⊆
      {q | ∀ j, q j ∈ Set.Iic (bnd j)} := by
    rintro q ⟨hq, hn⟩ j
    have hm : ∀ a, q (Sum.inl a) ≤ n := fun a => by
      rw [← hn]
      exact Finset.single_le_sum (f := fun a => q (Sum.inl a)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ a)
    rcases j with a | e
    · exact hm a
    · have hs := congrFun (mem_sector_iff.1 hq) (ends e).1
      simp only [Pi.add_apply, vertexCount, edgeCount] at hs
      have h1 : 1 ≤ edgeVec ends e (ends e).1 := by
        simp only [edgeVec, Pi.add_apply, Pi.single_eq_same]
        omega
      have h2 : q (Sum.inr e) * edgeVec ends e (ends e).1 ≤
          ∑ e', q (Sum.inr e') * edgeVec ends e' (ends e).1 :=
        Finset.single_le_sum (f := fun e' => q (Sum.inr e') * edgeVec ends e' (ends e).1)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      have h3 : ∑ a, q (Sum.inl a) * α a (ends e).1 ≤ ∑ a, n * α a (ends e).1 :=
        Finset.sum_le_sum fun a _ => Nat.mul_le_mul_right _ (hm a)
      have h4 : q (Sum.inr e) ≤ q (Sum.inr e) * edgeVec ends e (ends e).1 :=
        Nat.le_mul_of_pos_right _ h1
      show q (Sum.inr e) ≤ ∑ a, n * α a (ends e).1 + β (ends e).1
      omega
  have hfin : {q : A ⊕ E → ℕ | q ∈ sector α ends β ∧ interactionOrder q = n}.Finite :=
    (Set.Finite.pi' fun j => Set.finite_Iic (bnd j)).subset key
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro q hq
  exact ⟨q.2, hq⟩

omit [Fintype V] in
/-- The order block `n` of `Q_β` consists of the count vectors with `|m| = n`. -/
@[simp]
theorem mem_orderFinset {β : V → ℕ} {n : ℕ} {q : sector α ends β} :
    q ∈ (finite_orderFiber α ends β n).toFinset ↔ interactionOrder q.1 = n :=
  mem_blockFinset (π := fun q : sector α ends β => interactionOrder q.1)
    (finite_orderFiber α ends β)

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]

/-- The order-grouped Wick family of `wick:prop:signcoherent`(ii): its `n`-th member is the
finite sum of the atoms `T_β(m, k)`, `(m, k) ∈ Q_β`, of total interaction order `|m| = n`. -/
def orderBlock (g : A → R⟦Γ⟧) (C : E → R⟦Γ⟧) (β : V → ℕ) : ℕ → R⟦Γ⟧ :=
  blockSum (fun q : sector α ends β => interactionOrder q.1) (finite_orderFiber α ends β)
    (atom α ends g C β)

/-- The `n`-th order block is the finite sum `∑_{(m, k) ∈ Q_β, |m| = n} T_β(m, k)`. -/
theorem orderBlock_apply (g : A → R⟦Γ⟧) (C : E → R⟦Γ⟧) (β : V → ℕ) (n : ℕ) :
    orderBlock α ends g C β n =
      ∑ q ∈ (finite_orderFiber α ends β n).toFinset, atom α ends g C β q :=
  rfl

variable {g : A → R⟦Γ⟧} {C : E → R⟦Γ⟧}

/-- With a common factor `gₐ = σ • uₐ`, the atom `T_β(m, k)` is `σ^{|m|}` times
`W(Am + β, k) / ∏ₐ mₐ! · u^m C^k`. -/
theorem atom_eq_pow_smul (σ : R) (u : A → R⟦Γ⟧) (hg : ∀ a, g a = σ • u a) (β : V → ℕ)
    (q : sector α ends β) :
    atom α ends g C β q = σ ^ interactionOrder q.1 •
      (((atomCoeff α ends β q.1 : ℚ) : R) •
        ((∏ a, u a ^ q.1 (Sum.inl a)) * ∏ e, C e ^ q.1 (Sum.inr e))) := by
  simp only [atom, hg, Algebra.smul_def, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, interactionOrder, map_pow]
  ring

variable [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]

/-- With coefficientwise nonnegative `uₐ` and covariance entries, the cofactor of `σ^{|m|}` in
`atom_eq_pow_smul` is coefficientwise nonnegative. -/
theorem coeffNonneg_atom_cofactor {u : A → R⟦Γ⟧} (hu : ∀ a, CoeffNonneg (u a))
    (hC : ∀ e, CoeffNonneg (C e)) (β : V → ℕ) (q : A ⊕ E → ℕ) :
    CoeffNonneg (((atomCoeff α ends β q : ℚ) : R) •
      ((∏ a, u a ^ q (Sum.inl a)) * ∏ e, C e ^ q (Sum.inr e))) := by
  refine CoeffNonneg.smul (ratCast_nonneg (atomCoeff_pos α ends β q).le) ?_
  exact (coeffNonneg_prod _ _ fun a _ => (hu a).pow _).mul
    (coeffNonneg_prod _ _ fun e _ => (hC e).pow _)

/-- `wick:prop:signcoherent`, support claim of the proof: in the sign-coherent case, the
support of the order block `n` is exactly the union of the supports of its atoms. -/
theorem support_orderBlock (σ : R) {u : A → R⟦Γ⟧} (hg : ∀ a, g a = σ • u a)
    (hu : ∀ a, CoeffNonneg (u a)) (hC : ∀ e, CoeffNonneg (C e)) (β : V → ℕ) (n : ℕ) :
    (orderBlock α ends g C β n).support =
      ⋃ q ∈ (finite_orderFiber α ends β n).toFinset, (atom α ends g C β q).support :=
  support_blockSum _ (finite_orderFiber α ends β) (fun n => σ ^ n) _
    (fun q => coeffNonneg_atom_cofactor α ends hu hC β q.1)
    (atom_eq_pow_smul α ends σ u hg β) n

/-- **Sign-coherent equivalence** (`wick:prop:signcoherent`, (i) ⟺ (ii)). Suppose the
covariance entries `Cₑ` are coefficientwise nonnegative and `gₐ = σ • uₐ` for one common
scalar `σ`, with every `uₐ` coefficientwise nonnegative. Then, in a fixed sector `Q_β`, the
raw Wick atom family is strongly summable iff the family obtained by grouping the atoms of equal
total interaction order `|m| = n` is strongly summable. -/
theorem stronglySummable_atom_iff_orderBlock (σ : R) {u : A → R⟦Γ⟧} (hg : ∀ a, g a = σ • u a)
    (hu : ∀ a, CoeffNonneg (u a)) (hC : ∀ e, CoeffNonneg (C e)) (β : V → ℕ) :
    StronglySummable (atom α ends g C β) ↔ StronglySummable (orderBlock α ends g C β) :=
  stronglySummable_iff_blockSum _ (finite_orderFiber α ends β) (fun n => σ ^ n) _
    (fun q => coeffNonneg_atom_cofactor α ends hu hC β q.1) (atom_eq_pow_smul α ends σ u hg β)

/-- **Sign-coherent equivalence** (`wick:prop:signcoherent`, full statement). In addition to
the hypotheses of `stronglySummable_atom_iff_orderBlock`, let `σ ≠ 0`, `uₐ ≠ 0` and `Cₑ ≠ 0`,
let `Γ` be a nonzero divisible ordered group and `R` of characteristic zero. For a pairable
sector (`Q_β ≠ ∅`), the raw sector family (i) and the order-grouped family (ii) are strongly
summable exactly when the conditions of `wick:thm:main` (`Surreal.WickDomain.main_tfae`) hold:
the vacuum family is strongly summable, `L > 0` on `S ∖ {0}`, `L > 0` on the Hilbert basis of
`S`, the balancing system is solvable, and every sector family is strongly summable. -/
theorem signCoherent_tfae [CharZero R] [Module ℚ Γ] [Nontrivial Γ] {σ : R} (hσ : σ ≠ 0)
    {u : A → R⟦Γ⟧} (hg : ∀ a, g a = σ • u a) (hu0 : ∀ a, u a ≠ 0)
    (hu : ∀ a, CoeffNonneg (u a)) (hC0 : ∀ e, C e ≠ 0) (hC : ∀ e, CoeffNonneg (C e))
    {β : V → ℕ} (hβ : (sector α ends β).Nonempty) :
    List.TFAE [StronglySummable (atom α ends g C β),
      StronglySummable (orderBlock α ends g C β),
      StronglySummable (atom α ends g C 0),
      ∀ q ∈ sector α ends 0, q ≠ 0 → 0 < wickWeight g C q,
      ∀ h ∈ hilbertBasis (incidence α ends), 0 < wickWeight g C h,
      ∃ p : V → Γ, (∀ a, 0 < (g a).order + ∑ i, α a i • p i) ∧
        ∀ e, 0 < (C e).order - p (ends e).1 - p (ends e).2,
      ∀ β' : V → ℕ, StronglySummable (atom α ends g C β')] := by
  have hg0 : ∀ a, g a ≠ 0 := fun a => by
    rw [hg a]
    exact (smul_ne_zero_and_order hσ (hu0 a)).1
  have hm := main_tfae α ends hg0 hC0
  tfae_have 1 ↔ 2 := stronglySummable_atom_iff_orderBlock α ends σ hg hu hC β
  tfae_have 1 ↔ 3 := stronglySummable_atom_iff_vacuum α ends hg0 hC0 hβ
  tfae_have 3 ↔ 4 := hm.out 0 1
  tfae_have 3 ↔ 5 := hm.out 0 2
  tfae_have 3 ↔ 6 := hm.out 0 3
  tfae_have 3 ↔ 7 := hm.out 0 4
  tfae_finish

end WickBlocks

/-! ### The source's setting: `K = ℂ((t^Γ))` and a covariance matrix -/

section Complex

variable {Γ V A : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Fintype V] [LinearOrder V] [Fintype A]

open scoped ComplexOrder in
/-- **Sign-coherent equivalence** (`wick:prop:signcoherent`, (i) ⟺ (ii)) in the source's
setting: couplings `gₐ = σ uₐ ∈ ℂ((t^Γ))` with one common `σ ∈ ℂ` and every coefficient of every
`uₐ` a nonnegative real number, and a covariance matrix `C` whose nonzero entries `C_ij`,
`i ≤ j`, have only nonnegative real coefficients. For every `β`, the raw Wick atom family of
`Q_β` is strongly summable iff its order-grouped family is. -/
theorem stronglySummable_atom_iff_orderBlock_complex (α : A → V → ℕ) (C : Matrix V V ℂ⟦Γ⟧)
    {g : A → ℂ⟦Γ⟧} (σ : ℂ) {u : A → ℂ⟦Γ⟧} (hg : ∀ a, g a = σ • u a)
    (hu : ∀ a γ, ∃ r : ℝ, 0 ≤ r ∧ (u a).coeff γ = r)
    (hC : ∀ i j, i ≤ j → C i j ≠ 0 → ∀ γ, ∃ r : ℝ, 0 ≤ r ∧ (C i j).coeff γ = r)
    (β : V → ℕ) :
    StronglySummable (atom α Subtype.val g (matrixCov C) β) ↔
      StronglySummable (orderBlock α Subtype.val g (matrixCov C) β) :=
  stronglySummable_atom_iff_orderBlock α Subtype.val σ hg
    (fun a => (coeffNonneg_complex_iff _).2 (hu a))
    (fun e => (coeffNonneg_complex_iff _).2 (hC _ _ e.2.1 e.2.2)) β

open scoped ComplexOrder in
/-- **Sign-coherent equivalence** (`wick:prop:signcoherent`, full statement) in the source's
setting of `stronglySummable_atom_iff_orderBlock_complex`, with `σ ∈ ℂ^×`, nonzero `uₐ`, and a
nonzero divisible ordered group `Γ`. For a pairable sector `Q_β`, the raw and order-grouped
families are strongly summable exactly when the conditions of `wick:thm:main`
(`Surreal.WickDomain.main_tfae_matrix`) hold. -/
theorem signCoherent_tfae_complex [Module ℚ Γ] [Nontrivial Γ] (α : A → V → ℕ)
    (C : Matrix V V ℂ⟦Γ⟧) {g : A → ℂ⟦Γ⟧} {σ : ℂ} (hσ : σ ≠ 0) {u : A → ℂ⟦Γ⟧}
    (hg : ∀ a, g a = σ • u a) (hu0 : ∀ a, u a ≠ 0)
    (hu : ∀ a γ, ∃ r : ℝ, 0 ≤ r ∧ (u a).coeff γ = r)
    (hC : ∀ i j, i ≤ j → C i j ≠ 0 → ∀ γ, ∃ r : ℝ, 0 ≤ r ∧ (C i j).coeff γ = r)
    {β : V → ℕ} (hβ : (sector α (Subtype.val : MatrixEdge C → V × V) β).Nonempty) :
    List.TFAE [StronglySummable (atom α Subtype.val g (matrixCov C) β),
      StronglySummable (orderBlock α Subtype.val g (matrixCov C) β),
      StronglySummable (atom α Subtype.val g (matrixCov C) 0),
      ∀ q ∈ sector α (Subtype.val : MatrixEdge C → V × V) 0, q ≠ 0 →
        0 < wickWeight g (matrixCov C) q,
      ∀ h ∈ hilbertBasis (incidence α (Subtype.val : MatrixEdge C → V × V)),
        0 < wickWeight g (matrixCov C) h,
      ∃ p : V → Γ, (∀ a, 0 < (g a).order + ∑ i, α a i • p i) ∧
        ∀ i j, i ≤ j → C i j ≠ 0 → 0 < (C i j).order - p i - p j,
      ∀ β' : V → ℕ, StronglySummable (atom α Subtype.val g (matrixCov C) β')] := by
  have hg0 : ∀ a, g a ≠ 0 := fun a => by
    rw [hg a]
    exact (smul_ne_zero_and_order hσ (hu0 a)).1
  have hm := main_tfae_matrix α hg0 C
  tfae_have 1 ↔ 2 := stronglySummable_atom_iff_orderBlock_complex α C σ hg hu hC β
  tfae_have 1 ↔ 3 := stronglySummable_atom_iff_vacuum α Subtype.val hg0 (fun e => e.2.2) hβ
  tfae_have 3 ↔ 4 := hm.out 0 1
  tfae_have 3 ↔ 5 := hm.out 0 2
  tfae_have 3 ↔ 6 := hm.out 0 3
  tfae_have 3 ↔ 7 := hm.out 0 4
  tfae_finish

end Complex

end

end Surreal.SignCoherent
