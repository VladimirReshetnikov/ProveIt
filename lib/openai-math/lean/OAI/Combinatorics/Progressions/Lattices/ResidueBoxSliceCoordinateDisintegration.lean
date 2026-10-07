/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Logic.Equiv.Prod
import OAI.Combinatorics.Progressions.Estimates.NestedProgressionReindex
import OAI.Combinatorics.Progressions.Geometry.SampledCommonBox

namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} {N : U → ℕ} {q : ℕ}

def integerPoint (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) : U → ℤ :=
  fun i => ((A.point j i).val : ℤ)

theorem integerPoint_eq (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) :
    A.integerPoint j = commonStridePoint (fun i => (A.start i : ℤ)) q
      (fun i => ((j i).val : ℤ)) := by
  funext i
  simp only [integerPoint, point, commonStridePoint, Nat.cast_add, Nat.cast_mul]

@[simp] theorem commonStrideIndex_integerPoint (A : ResidueBoxSlice N q) (hq : 0 < q)
    (j : ∀ i, Fin (A.length i)) :
    commonStrideIndex (fun i => (A.start i : ℤ)) q (A.integerPoint j) =
      (fun i => ((j i).val : ℤ)) := by
  rw [integerPoint_eq, commonStrideIndex_point _ hq]

theorem integerPoint_injective (A : ResidueBoxSlice N q) (hq : 0 < q) :
    Function.Injective A.integerPoint := by
  intro j k h
  have hi := congrArg (commonStrideIndex (fun i => (A.start i : ℤ)) q) h
  rw [A.commonStrideIndex_integerPoint hq, A.commonStrideIndex_integerPoint hq] at hi
  funext i
  apply Fin.ext
  exact_mod_cast congrFun hi i

variable [Fintype U] [DecidableEq U]

noncomputable def integerPoints (A : ResidueBoxSlice N q) : Finset (U → ℤ) :=
  Finset.univ.image A.integerPoint

theorem integerPoints_eq_commonStrideBox (A : ResidueBoxSlice N q) :
    A.integerPoints = commonStrideBox (fun i => (A.start i : ℤ)) q A.length := by
  classical
  rw [commonStrideBox_eq_image]
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨fun i => ((j i).val : ℤ), ?_, (A.integerPoint_eq j).symm⟩
    exact (mem_integerBox _ _).mpr (fun i => ⟨by positivity, by exact_mod_cast (j i).isLt⟩)
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hz' := (mem_integerBox _ _).mp hz
    let j : ∀ i, Fin (A.length i) := fun i => ⟨(z i).toNat, by
      have hzi := hz' i
      omega⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    rw [A.integerPoint_eq]
    congr 1
    funext i
    exact Int.toNat_of_nonneg (hz' i).1

omit [Fintype U] [DecidableEq U] in
theorem progression_inside (A : ResidueBoxSlice N q) (i : U) :
    integerProgressionSupport (A.start i : ℤ) q (A.length i) ⊆
      Finset.Ico (0 : ℤ) (N i) := by
  intro y hy
  obtain ⟨j, hj0, hjlt, rfl⟩ := (mem_integerProgressionSupport_iff_parameter _ _ _ _).mp hy
  have hj : j.toNat < A.length i := by omega
  have hinside := A.inside i j.toNat hj
  have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
  apply Finset.mem_Ico.mpr
  constructor
  · positivity
  · rw [← he]
    exact_mod_cast hinside

theorem isDenseCommonStrideBox (A : ResidueBoxSlice N q) (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ i, 0 < A.length i)
    (hlength : ∀ i, ρ * N i ≤ 4 * q * A.length i) :
    IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints := by
  refine ⟨fun i => (A.start i : ℤ), q, A.length, hq, hA,
    A.progression_inside, ?_, A.integerPoints_eq_commonStrideBox⟩
  intro i
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4 * (q : ℝ) / ρ), inv_div]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (q : ℝ))).mpr
  nlinarith [hlength i]

theorem densityCost_nonneg (hq : 0 < q) {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1) :
    0 ≤ Real.log (4 * (q : ℝ) / ρ) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ hρ).mpr
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  linarith

theorem expect_integerPoints (A : ResidueBoxSlice N q) (hq : 0 < q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (U → ℤ) → V) :
    (𝔼 x ∈ A.integerPoints, f x) =
      (𝔼 j : (∀ i, Fin (A.length i)), f (A.integerPoint j)) := by
  exact Finset.expect_image (A.integerPoint_injective hq).injOn

end Erdos3.ResidueBoxSlice

namespace Erdos3

theorem IsDenseCommonStrideBox.mono {U : Type*} [Fintype U] [DecidableEq U]
    {N : U → ℕ} {p p' : ℝ} {A : Finset (U → ℤ)}
    (hA : IsDenseCommonStrideBox N p A) (hpp' : p ≤ p') :
    IsDenseCommonStrideBox N p' A := by
  obtain ⟨c, m, H, hm, hH, hinside, hlength, heq⟩ := hA
  refine ⟨c, m, H, hm, hH, hinside, ?_, heq⟩
  intro i
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg hpp')) (Nat.cast_nonneg (N i))).trans (hlength i)

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem commonStrideBox_axis_card (c : I → ℤ) (m : ℕ) (H : I → ℕ)
    (hm : 0 < m) (hH : ∀ i, 0 < H i) (i : I) :
    ((commonStrideBox c m H).image (fun x => x i)).card = H i := by
  classical
  have hnonempty (j : I) : (integerProgressionSupport (c j) m (H j)).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_integerProgressionSupport _ _ _ hm]
    exact hH j
  have hproject := Fintype.eval_image_piFinset
    (fun j => integerProgressionSupport (c j) m (H j)) i (fun j _ => hnonempty j)
  exact (congrArg Finset.card hproject).trans (card_integerProgressionSupport _ _ _ hm)

namespace ResidueBoxSlice

variable {N : I → ℕ} {q : ℕ}

theorem length_pos_of_integerPoints_nonempty (A : ResidueBoxSlice N q)
    (hA : A.integerPoints.Nonempty) (i : I) : 0 < A.length i := by
  classical
  obtain ⟨x, hx⟩ := hA
  obtain ⟨j, _, _⟩ := Finset.mem_image.mp hx
  exact lt_of_le_of_lt (Nat.zero_le ((j i).val)) (j i).isLt

theorem length_pos_of_dense (A : ResidueBoxSlice N q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (i : I) :
    0 < A.length i :=
  A.length_pos_of_integerPoints_nonempty hA.nonempty i

theorem length_lower_of_dense (A : ResidueBoxSlice N q) (hq : 0 < q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (i : I) :
    Real.exp (-c) * (N i : ℝ) ≤ (A.length i : ℝ) := by
  have hlength := A.length_pos_of_dense hA
  obtain ⟨start, m, H, hm, hH, _, hdense, heq⟩ := hA
  have hcard := congrArg
    (fun s : Finset (I → ℤ) => (s.image (fun x => x i)).card) heq
  rw [A.integerPoints_eq_commonStrideBox,
    commonStrideBox_axis_card _ _ _ hq hlength,
    commonStrideBox_axis_card _ _ _ hm hH] at hcard
  rw [hcard]
  exact hdense i

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} {P N : I → ℕ} {q : ℕ}

namespace ResidueBoxSlice

def enlargeBox (S : ResidueBoxSlice P q) (N : I → ℕ)
    (hPN : ∀ i, P i ≤ N i) : ResidueBoxSlice N q where
  start := S.start
  length := S.length
  inside i j hj := (S.inside i j hj).trans_le (hPN i)

@[simp] theorem enlargeBox_start (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) : (S.enlargeBox N hPN).start = S.start := rfl

@[simp] theorem enlargeBox_length (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) : (S.enlargeBox N hPN).length = S.length := rfl

@[simp] theorem enlargeBox_integerPoint (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) (u : ∀ i, Fin (S.length i)) :
    (S.enlargeBox N hPN).integerPoint u = S.integerPoint u := rfl

variable [Fintype I] [DecidableEq I]

@[simp] theorem enlargeBox_integerPoints (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) :
    (S.enlargeBox N hPN).integerPoints = S.integerPoints := rfl

theorem expect_enlargeBox (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V]
    (f : (I → ℤ) → V) :
    (𝔼 x ∈ (S.enlargeBox N hPN).integerPoints, f x) =
      𝔼 x ∈ S.integerPoints, f x := rfl

end ResidueBoxSlice

variable [Fintype I] [DecidableEq I]

def integerBoxInclusion (hPN : ∀ i, P i ≤ N i) : integerBox P → integerBox N :=
  fun x => ⟨x.val, (mem_integerBox N x.val).mpr (fun i =>
    ⟨((mem_integerBox P x.val).mp x.property i).1,
      (((mem_integerBox P x.val).mp x.property i).2).trans_le
        (by exact_mod_cast hPN i)⟩)⟩

@[simp] theorem integerBoxInclusion_val (hPN : ∀ i, P i ≤ N i)
    (x : integerBox P) : (integerBoxInclusion hPN x).val = x.val := rfl

theorem IsDenseCommonStrideBox.enlargeBox {c extra : ℝ} {A : Finset (I → ℤ)}
    (hA : IsDenseCommonStrideBox P c A) (hPN : ∀ i, P i ≤ N i)
    (hside : ∀ i, Real.exp (-extra) * (N i : ℝ) ≤ (P i : ℝ)) :
    IsDenseCommonStrideBox N (c + extra) A := by
  obtain ⟨start, m, H, hm, hH, hinside, hlength, heq⟩ := hA
  refine ⟨start, m, H, hm, hH, ?_, ?_, heq⟩
  · intro i x hx
    have h := Finset.mem_Ico.mp (hinside i hx)
    exact Finset.mem_Ico.mpr ⟨h.1, h.2.trans_le (by exact_mod_cast hPN i)⟩
  · intro i
    calc
      Real.exp (-(c + extra)) * (N i : ℝ) =
          Real.exp (-c) * (Real.exp (-extra) * (N i : ℝ)) := by
            rw [neg_add, Real.exp_add, mul_assoc]
      _ ≤ Real.exp (-c) * (P i : ℝ) :=
        mul_le_mul_of_nonneg_left (hside i) (Real.exp_pos _).le
      _ ≤ (H i : ℝ) := hlength i

namespace ResidueBoxSlice

theorem enlargeBox_dense (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) {c extra : ℝ}
    (hS : IsDenseCommonStrideBox P c S.integerPoints)
    (hside : ∀ i, Real.exp (-extra) * (N i : ℝ) ≤ (P i : ℝ)) :
    IsDenseCommonStrideBox N (c + extra) (S.enlargeBox N hPN).integerPoints :=
  hS.enlargeBox hPN hside

omit [Fintype I] [DecidableEq I] in
theorem enlargeBox_length_lower (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) {c extra : ℝ}
    (hlength : ∀ i, Real.exp (-c) * (P i : ℝ) ≤ (S.length i : ℝ))
    (hside : ∀ i, Real.exp (-extra) * (N i : ℝ) ≤ (P i : ℝ)) (i : I) :
    Real.exp (-(c + extra)) * (N i : ℝ) ≤ ((S.enlargeBox N hPN).length i : ℝ) := by
  calc
    Real.exp (-(c + extra)) * (N i : ℝ) =
        Real.exp (-c) * (Real.exp (-extra) * (N i : ℝ)) := by
          rw [neg_add, Real.exp_add, mul_assoc]
    _ ≤ Real.exp (-c) * (P i : ℝ) :=
      mul_le_mul_of_nonneg_left (hside i) (Real.exp_pos _).le
    _ ≤ ((S.enlargeBox N hPN).length i : ℝ) := hlength i

@[simp] theorem enlargeBox_fullSlicePointInIntegerBox (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) (u : ∀ i, Fin (S.length i)) :
    (S.enlargeBox N hPN).fullSlicePointInIntegerBox u =
      integerBoxInclusion hPN (S.fullSlicePointInIntegerBox u) := rfl

theorem enlargeBox_fullSliceLaw_mean (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) (hlen : ∀ i, 0 < S.length i)
    (f : integerBox N → ℝ) :
    ((S.enlargeBox N hPN).fullSliceLaw hlen).mean f =
      (S.fullSliceLaw hlen).mean (fun x => f (integerBoxInclusion hPN x)) := by
  exact ((S.enlargeBox N hPN).fullSliceLaw_mean hlen f).trans
    (S.fullSliceLaw_mean hlen (fun x => f (integerBoxInclusion hPN x))).symm

theorem enlargeBox_fullSliceLaw_mean_ambient (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) (hlen : ∀ i, 0 < S.length i)
    (f : (I → ℤ) → ℝ) :
    ((S.enlargeBox N hPN).fullSliceLaw hlen).mean (fun x => f x.val) =
      (S.fullSliceLaw hlen).mean (fun x => f x.val) :=
  S.enlargeBox_fullSliceLaw_mean hPN hlen (fun x => f x.val)

theorem enlargeBox_fullSliceLaw (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) (hlen : ∀ i, 0 < S.length i) :
    (S.enlargeBox N hPN).fullSliceLaw hlen =
      (S.fullSliceLaw hlen).finitePushforward (integerBoxInclusion hPN) := by
  have ext_weight {p p' : FiniteProbabilityWeights (integerBox N)}
      (h : p.weight = p'.weight) : p = p' := by
    cases p
    cases p'
    cases h
    rfl
  apply ext_weight
  funext x
  have hm := (S.enlargeBox_fullSliceLaw_mean hPN hlen
    (fun y => if y = x then 1 else 0)).trans
    (FiniteProbabilityWeights.mean_finitePushforward (S.fullSliceLaw hlen)
      (integerBoxInclusion hPN) (fun y => if y = x then 1 else 0)).symm
  simpa [FiniteProbabilityWeights.mean] using hm

end ResidueBoxSlice

omit [DecidableEq I] in

theorem RelativePatchSliceConclusion.enlargeBox {s rankBound : ℕ}
    {f : (I → ℤ) → ℝ} {target c extra : ℝ}
    (h : RelativePatchSliceConclusion s P f target rankBound c)
    (hPN : ∀ i, P i ≤ N i)
    (hside : ∀ i, Real.exp (-extra) * (N i : ℝ) ≤ (P i : ℝ))
    (hextra : 0 ≤ extra) :
    RelativePatchSliceConclusion s N f target rankBound (c + extra) := by
  obtain ⟨q, hq, S, d, Q, hlength, hd, hcost, hscore⟩ := h
  refine ⟨q, hq, S.enlargeBox N hPN, d, Q,
    S.enlargeBox_length_lower hPN hlength hside, hd, ?_, ?_⟩
  · exact hcost.trans (le_add_of_nonneg_right hextra)
  · exact (Real.exp_le_exp.mpr (neg_le_neg (le_add_of_nonneg_right hextra))).trans hscore

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} [Fintype U] [DecidableEq U] {N : U → ℕ} {q : ℕ}

noncomputable def finiteSites (A : ResidueBoxSlice N q) : Finset (∀ i, Fin (N i)) :=
  Finset.univ.image A.point

theorem finiteSites_image_integerCast (A : ResidueBoxSlice N q) :
    A.finiteSites.image (fun t i => ((t i).val : ℤ)) = A.integerPoints := by
  classical
  simp only [finiteSites, integerPoints, Finset.image_image]
  rfl

omit [Fintype U] [DecidableEq U] in

theorem finiteBox_integerCast_injective :
    Function.Injective (fun t : (∀ i, Fin (N i)) => fun i => ((t i).val : ℤ)) := by
  intro t u h
  funext i
  apply Fin.ext
  exact Int.ofNat_inj.mp (congrFun h i)

theorem expect_finiteSites (A : ResidueBoxSlice N q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (U → ℤ) → V) :
    (𝔼 t ∈ A.finiteSites, f (fun i => ((t i).val : ℤ))) =
      𝔼 x ∈ A.integerPoints, f x := by
  classical
  rw [← A.finiteSites_image_integerCast]
  exact (Finset.expect_image finiteBox_integerCast_injective.injOn).symm

theorem finiteSites_nonempty (A : ResidueBoxSlice N q)
    (hA : ∀ i, 0 < A.length i) : A.finiteSites.Nonempty := by
  classical
  let j : ∀ i, Fin (A.length i) := fun i => ⟨0, hA i⟩
  exact ⟨A.point j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

theorem finiteSites_nonempty_of_integerPoints (A : ResidueBoxSlice N q)
    (h : A.integerPoints.Nonempty) : A.finiteSites.Nonempty := by
  classical
  rw [← A.finiteSites_image_integerCast, Finset.image_nonempty] at h
  exact h

theorem finiteSites_dense (A : ResidueBoxSlice N q) {p : ℝ}
    (h : IsDenseCommonStrideBox N p A.integerPoints) :
    IsDenseCommonStrideBox N p
      (A.finiteSites.image (fun t i => ((t i).val : ℤ))) := by
  classical
  rw [A.finiteSites_image_integerCast]
  exact h

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I V : Type*} {N : I → ℕ} {q : ℕ}

def comap (A : ResidueBoxSlice N q) (e : V → I) :
    ResidueBoxSlice (fun v => N (e v)) q where
  start v := A.start (e v)
  length v := A.length (e v)
  inside v j hj := A.inside (e v) j hj

def coordinateProjection (A : ResidueBoxSlice N q) (keep : I → Prop) :
    ResidueBoxSlice (fun i : {i // keep i} => N i) q :=
  A.comap Subtype.val

variable [Fintype I] [DecidableEq I]

theorem comap_isDenseCommonStrideBox [Fintype V] [DecidableEq V]
    (A : ResidueBoxSlice N q) (hq : 0 < q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (e : V → I) :
    IsDenseCommonStrideBox (fun v => N (e v)) c (A.comap e).integerPoints := by
  refine ⟨fun v => ((A.comap e).start v : ℤ), q, (A.comap e).length,
    hq, ?_, (A.comap e).progression_inside, ?_,
    (A.comap e).integerPoints_eq_commonStrideBox⟩
  · intro v
    exact A.length_pos_of_dense hA (e v)
  · intro v
    exact A.length_lower_of_dense hq hA (e v)

theorem coordinateProjection_isDenseCommonStrideBox
    (A : ResidueBoxSlice N q) (hq : 0 < q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (keep : I → Prop) :
    IsDenseCommonStrideBox (fun i : {i // keep i} => N i) c
      (A.coordinateProjection keep).integerPoints :=
  A.comap_isDenseCommonStrideBox hq hA Subtype.val

theorem mem_integerPoints_iff (A : ResidueBoxSlice N q) (x : I → ℤ) :
    x ∈ A.integerPoints ↔
      ∀ i, x i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i) := by
  rw [A.integerPoints_eq_commonStrideBox]
  exact Fintype.mem_piFinset

theorem finiteSplitPoint_mem_integerPoints
    (A : ResidueBoxSlice N q) (keep : I → Prop)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i : {i // ¬keep i},
      fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i))
    {x : {i // keep i} → ℤ} (hx : x ∈ (A.coordinateProjection keep).integerPoints) :
    finiteSplitPoint keep x fixed ∈ A.integerPoints := by
  apply (A.mem_integerPoints_iff _).mpr
  have hx' := ((A.coordinateProjection keep).mem_integerPoints_iff x).mp hx
  intro i
  by_cases hi : keep i
  · simpa only [finiteSplitPoint, dite_eq_left hi, coordinateProjection, comap] using hx' ⟨i, hi⟩
  · simpa only [finiteSplitPoint, dite_eq_right hi] using hfixed ⟨i, hi⟩

theorem exists_coordinate_fiber_score
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (score : (I → ℤ) → ℝ) {a : ℝ}
    (hmean : a ≤ 𝔼 x ∈ A.integerPoints, score x) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i : {i // ¬keep i},
        fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i)) ∧
      (∀ x ∈ (A.coordinateProjection keep).integerPoints,
        finiteSplitPoint keep x fixed ∈ A.integerPoints) ∧
      a ≤ 𝔼 x ∈ (A.coordinateProjection keep).integerPoints,
        score (finiteSplitPoint keep x fixed) := by
  let e := Equiv.piEquivPiSubtypeProd keep (fun i => Fin (A.length i))
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, hlength i⟩⟩
  let fixedOf (v : ∀ i : {i // ¬keep i}, Fin (A.length i)) : {i // ¬keep i} → ℤ :=
    fun i => ((A.start i + q * (v i).val : ℕ) : ℤ)
  have hsplit : (𝔼 j : (∀ i, Fin (A.length i)), score (A.integerPoint j)) =
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        𝔼 u : (∀ i : {i // keep i}, Fin (A.length i)),
          score (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint u)
            (fixedOf v)) := by
    calc
      _ = 𝔼 uv : (∀ i : {i // keep i}, Fin (A.length i)) ×
          (∀ i : {i // ¬keep i}, Fin (A.length i)),
          score (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint uv.1)
            (fixedOf uv.2)) := by
        apply Fintype.expect_equiv e
        intro j
        congr 1
        funext i
        by_cases hi : keep i <;>
          simp [e, integerPoint, point, coordinateProjection, comap, fixedOf,
            finiteSplitPoint, hi, Equiv.piEquivPiSubtypeProd]
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  rw [A.expect_integerPoints hq score, hsplit] at hmean
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have hfixed (i : {i // ¬keep i}) :
      fixedOf v i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i) := by
    simpa only [fixedOf, Nat.cast_add, Nat.cast_mul] using
      integerProgressionSupport_point (A.start i : ℤ) q (A.length i) hq
        (v i).val (v i).isLt
  refine ⟨fixedOf v, hfixed, ?_, ?_⟩
  · intro x hx
    exact A.finiteSplitPoint_mem_integerPoints keep (fixedOf v) hfixed hx
  · rw [(A.coordinateProjection keep).expect_integerPoints hq]
    exact hv

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {K : Type*} (oldKeep keep : K → Prop)

def axisInclusion (hsub : ∀ i, keep i → oldKeep i) (i : {i // keep i}) :
    {i // oldKeep i} :=
  ⟨i.val, hsub i.val i.property⟩

noncomputable def axisInsertion
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (u : {i // keep i} → ℤ) : {i // oldKeep i} → ℤ :=
  fun i => if hi : keep i.val then u ⟨i.val, hi⟩ else fixed ⟨i, hi⟩

@[simp] theorem axisInsertion_kept (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (u : {i // keep i} → ℤ) (i : {i // keep i}) :
    axisInsertion oldKeep keep fixed u (axisInclusion oldKeep keep hsub i) = u i := by
  simp [axisInsertion, axisInclusion, i.property]

theorem axisInsertion_injective (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ) :
    Function.Injective (axisInsertion oldKeep keep fixed) := by
  intro x y h
  funext i
  simpa only [axisInsertion_kept] using
    congrFun h (axisInclusion oldKeep keep hsub i)

variable {oldKeep keep} {N : K → ℕ} {q oldq : ℕ}

noncomputable def extendAxes
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val)) :
    ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) q where
  start i := if hi : keep i.val then S.start ⟨i.val, hi⟩ else (fixed ⟨i, hi⟩).toNat
  length i := if hi : keep i.val then S.length ⟨i.val, hi⟩ else 1
  inside i j hj := by
    by_cases hi : keep i.val
    · simpa only [dite_eq_left hi] using
        S.inside ⟨i.val, hi⟩ j (by simpa only [dite_eq_left hi] using hj)
    · have hj0 : j = 0 := by
        simpa only [dite_eq_right hi, Nat.lt_one_iff] using hj
      have hf := Finset.mem_Ico.mp (A.progression_inside i (hfixed ⟨i, hi⟩))
      simpa only [dite_eq_right hi, hj0, mul_zero, add_zero] using
        (show (fixed ⟨i, hi⟩).toNat < N i.val by omega)

attribute [local irreducible] integerProgressionSupport

variable [Fintype K]

theorem extendAxes_integerPoints
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val)) :
    (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints =
      S.integerPoints.image (axisInsertion oldKeep keep fixed) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    let t : ∀ i : {i // keep i}, Fin (S.length i) := fun i =>
      ⟨(j (axisInclusion oldKeep keep hsub i)).val, by
        simpa [extendAxes, axisInclusion, i.property] using
          (j (axisInclusion oldKeep keep hsub i)).isLt⟩
    refine Finset.mem_image.mpr ⟨S.integerPoint t,
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
    funext i
    by_cases hi : keep i.val
    · simp [axisInsertion, integerPoint, point, extendAxes, hi, t, axisInclusion]
    · have hj0 : (j i).val = 0 := by
        have := (j i).isLt
        simpa only [extendAxes, dite_eq_right hi, Nat.lt_one_iff] using this
      have hf := (Finset.mem_Ico.mp (A.progression_inside i (hfixed ⟨i, hi⟩))).1
      simp [axisInsertion, integerPoint, point, extendAxes, hi, hj0,
        Int.toNat_of_nonneg hf]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
    let j : ∀ i, Fin ((@extendAxes K oldKeep keep N q oldq S A fixed hfixed).length i) := fun i =>
      if hi : keep i.val then
        ⟨(t ⟨i.val, hi⟩).val, by
          simp only [extendAxes, dite_eq_left hi]
          exact (t ⟨i.val, hi⟩).isLt⟩
      else ⟨0, by simp [extendAxes, hi]⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : keep i.val
    · simp [axisInsertion, integerPoint, point, extendAxes, hi, j]
    · have hf := (Finset.mem_Ico.mp (A.progression_inside i (hfixed ⟨i, hi⟩))).1
      simp [axisInsertion, integerPoint, point, extendAxes, hi, j,
        Int.toNat_of_nonneg hf]

theorem expect_extendAxes
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val))
    {W : Type*} [AddCommMonoid W] [Module ℚ≥0 W]
    (f : ({i // oldKeep i} → ℤ) → W) :
    (𝔼 x ∈ (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints, f x) =
      𝔼 x ∈ S.integerPoints, f (axisInsertion oldKeep keep fixed x) := by
  rw [S.extendAxes_integerPoints (N := N) A hsub fixed hfixed]
  exact Finset.expect_image (axisInsertion_injective oldKeep keep hsub fixed).injOn

theorem extendAxes_dense
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val))
    (hq : 0 < q) {outCost shortCost : ℝ}
    (hS : IsDenseCommonStrideBox (fun i : {i // keep i} => N i.val)
      outCost S.integerPoints)
    (hshort : ∀ i : {i // oldKeep i}, ¬keep i.val →
      (N i.val : ℝ) ≤ Real.exp shortCost) :
    IsDenseCommonStrideBox (fun i : {i // oldKeep i} => N i.val)
      (max outCost shortCost) (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints := by
  let T := @extendAxes K oldKeep keep N q oldq S A fixed hfixed
  refine ⟨fun i => (T.start i : ℤ), q, T.length, hq, ?_,
    T.progression_inside, ?_, T.integerPoints_eq_commonStrideBox⟩
  · intro i
    by_cases hi : keep i.val
    · simpa only [T, extendAxes, dite_eq_left hi] using S.length_pos_of_dense hS ⟨i.val, hi⟩
    · simp [T, extendAxes, hi]
  · intro i
    by_cases hi : keep i.val
    · calc
        _ ≤ Real.exp (-outCost) * (N i.val : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _))) (Nat.cast_nonneg _)
        _ ≤ T.length i := by
          simpa only [T, extendAxes, dite_eq_left hi] using
            S.length_lower_of_dense hq hS ⟨i.val, hi⟩
    · simp only [T, extendAxes, dite_eq_right hi, Nat.cast_one]
      calc
        _ ≤ Real.exp (-shortCost) * (N i.val : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))) (Nat.cast_nonneg _)
        _ ≤ Real.exp (-shortCost) * Real.exp shortCost :=
          mul_le_mul_of_nonneg_left (hshort i hi) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem extendAxes_subset
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val))
    (hS : S.integerPoints ⊆
      (A.comap (axisInclusion oldKeep keep hsub)).integerPoints) :
    (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints ⊆ A.integerPoints := by
  rw [S.extendAxes_integerPoints (N := N) A hsub fixed hfixed]
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  apply (A.mem_integerPoints_iff _).mpr
  have hu' := ((A.comap (axisInclusion oldKeep keep hsub)).mem_integerPoints_iff _).mp (hS hu)
  intro i
  by_cases hi : keep i.val
  · simpa only [axisInsertion, dite_eq_left hi, comap, axisInclusion] using hu' ⟨i.val, hi⟩
  · simpa only [axisInsertion, dite_eq_right hi] using hfixed ⟨i, hi⟩

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

theorem coordinate_complexMean
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (f : (I → ℤ) → ℂ) :
    (𝔼 x ∈ A.integerPoints, f x) =
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
          f (finiteSplitPoint keep u
            (fun i => ((A.start i + q * (v i).val : ℕ) : ℤ))) := by
  let e := Equiv.piEquivPiSubtypeProd keep (fun i => Fin (A.length i))
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, hlength i⟩⟩
  let fixedOf (v : ∀ i : {i // ¬keep i}, Fin (A.length i)) : {i // ¬keep i} → ℤ :=
    fun i => ((A.start i + q * (v i).val : ℕ) : ℤ)
  have hsplit : (𝔼 j : (∀ i, Fin (A.length i)), f (A.integerPoint j)) =
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        𝔼 u : (∀ i : {i // keep i}, Fin (A.length i)),
          f (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint u)
            (fixedOf v)) := by
    calc
      _ = 𝔼 uv : (∀ i : {i // keep i}, Fin (A.length i)) ×
          (∀ i : {i // ¬keep i}, Fin (A.length i)),
          f (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint uv.1)
            (fixedOf uv.2)) := by
        apply Fintype.expect_equiv e
        intro j
        congr 1
        funext i
        by_cases hi : keep i <;>
          simp [e, integerPoint, point, coordinateProjection, comap, fixedOf,
            finiteSplitPoint, hi, Equiv.piEquivPiSubtypeProd]
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  rw [A.expect_integerPoints hq f, hsplit]
  apply Finset.expect_congr rfl
  intro v _
  exact ((A.coordinateProjection keep).expect_integerPoints hq
    (fun u => f (finiteSplitPoint keep u (fixedOf v)))).symm

theorem exists_coordinate_fiber_norm
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (f : (I → ℤ) → ℂ) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i : {i // ¬keep i},
        fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i)) ∧
      (∀ x ∈ (A.coordinateProjection keep).integerPoints,
        finiteSplitPoint keep x fixed ∈ A.integerPoints) ∧
      ‖𝔼 x ∈ A.integerPoints, f x‖ ≤
        ‖𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
          f (finiteSplitPoint keep u fixed)‖ := by
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, hlength i⟩⟩
  let fixedOf (v : ∀ i : {i // ¬keep i}, Fin (A.length i)) : {i // ¬keep i} → ℤ :=
    fun i => ((A.start i + q * (v i).val : ℕ) : ℤ)
  have hmean : ‖𝔼 x ∈ A.integerPoints, f x‖ ≤
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        ‖𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
          f (finiteSplitPoint keep u (fixedOf v))‖ := by
    rw [A.coordinate_complexMean hq hlength keep f]
    exact RCLike.norm_expect_le (K := ℂ)
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have hfixed (i : {i // ¬keep i}) :
      fixedOf v i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i) := by
    simpa only [fixedOf, Nat.cast_add, Nat.cast_mul] using
      integerProgressionSupport_point (A.start i : ℤ) q (A.length i) hq
        (v i).val (v i).isLt
  exact ⟨fixedOf v, hfixed,
    fun _ hx => A.finiteSplitPoint_mem_integerPoints keep (fixedOf v) hfixed hx, hv⟩

theorem exists_coordinate_fiber_correlation
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (f : (I → ℤ) → ℂ) {δ : ℝ}
    (hmean : δ ≤ ‖𝔼 x ∈ A.integerPoints, f x‖) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i : {i // ¬keep i},
        fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i)) ∧
      (∀ x ∈ (A.coordinateProjection keep).integerPoints,
        finiteSplitPoint keep x fixed ∈ A.integerPoints) ∧
      δ ≤ ‖𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
        f (finiteSplitPoint keep u fixed)‖ := by
  obtain ⟨fixed, hfixed, hinside, hnorm⟩ :=
    A.exists_coordinate_fiber_norm hq hlength keep f
  exact ⟨fixed, hfixed, hinside, hmean.trans hnorm⟩

end Erdos3.ResidueBoxSlice

end

end OAI
