import Mathlib.LinearAlgebra.Multilinear.Curry
import OAI.Combinatorics.Progressions.Estimates.MultilinearFirstOrder
import OAI.Combinatorics.Progressions.Geometry.LieTreeSupport
import OAI.Combinatorics.Progressions.Nilpotent.DegreeRankLieBrackets

namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

def lieTreeWeight (w : I → ℕ) : FreeMagma I → ℕ
  | .of i => w i
  | .mul a b => lieTreeWeight w a + lieTreeWeight w b

theorem lieTree_length_le_weight (w : I → ℕ) (hw : ∀ i, 0 < w i) (a : FreeMagma I) :
    a.length ≤ lieTreeWeight w a := by
  induction a using FreeMagma.rec with
  | of i => exact hw i
  | mul a b ha hb => exact Nat.add_le_add ha hb

def weightedLieTreeGenerators (v : I → L) (w : I → ℕ) (d r : ℕ) : Set L :=
  {x | ∃ a : FreeMagma I, lieTreeWeight w a = d ∧ r ≤ a.length ∧ lieTreeEval v a = x}

def weightedLieTreeSpan (v : I → L) (w : I → ℕ) (d r : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ (weightedLieTreeGenerators v w d r)

theorem weightedLieTreeSpan_antitone (v : I → L) (w : I → ℕ) (d : ℕ) :
    Antitone (weightedLieTreeSpan v w d) := by
  intro r t hrt
  apply Submodule.span_mono
  rintro x ⟨a, ha, ht, hx⟩
  exact ⟨a, ha, hrt.trans ht, hx⟩

theorem weightedLieTreeSpan_lie_mem (v : I → L) (w : I → ℕ) {d e r t : ℕ} {x y : L}
    (hx : x ∈ weightedLieTreeSpan v w d r) (hy : y ∈ weightedLieTreeSpan v w e t) :
    ⁅x, y⁆ ∈ weightedLieTreeSpan v w (d + e) (r + t) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, hi, rfl⟩ := hx
    obtain ⟨b, hb, hj, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, congrArg₂ (· + ·) ha hb, Nat.add_le_add hi hj, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem span_weighted_leaves_le (v : I → L) (w : I → ℕ) (d : ℕ) :
    Submodule.span ℚ (v '' {i | w i = d}) ≤ weightedLieTreeSpan v w d 1 := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, hi, rfl⟩
  exact Submodule.subset_span ⟨.of i, hi, le_rfl, rfl⟩

theorem FilteredLieTree.eval_mem_weighted_span {s : ℕ} {F : NilpotentLieFiltration L s}
    (v : I → L) (w : I → ℕ)
    (hspan : ∀ d, 0 < d → F.layer d ≤ Submodule.span ℚ (v '' {i | w i = d}))
    {d r : ℕ} (a : FilteredLieTree F d r) : a.eval ∈ weightedLieTreeSpan v w d r := by
  induction a with
  | leaf hd x hx => exact span_weighted_leaves_le v w _ (hspan _ hd hx)
  | bracket a b ha hb => exact weightedLieTreeSpan_lie_mem v w ha hb

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem lieTreeEval_mem_rankLayer (v : I → L) (w : I → ℕ) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i)) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.rankLayer (lieTreeWeight w a) a.length := by
  induction a using FreeMagma.rec with
  | of i => exact F.tree_eval_mem_rankLayer (.leaf (hw i) (v i) (hv i)) le_rfl
  | mul a b ha hb => exact F.rankLayer_lie_mem ha hb

theorem rankLayer_eq_weighted_tree_span (v : I → L) (w : I → ℕ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i))
    (hspan : ∀ d, 0 < d → F.layer d ≤ Submodule.span ℚ (v '' {i | w i = d})) (d r : ℕ) :
    F.rankLayer d r = F.layer (d + 1) ⊔ weightedLieTreeSpan v w d r := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro x ⟨k, hrk, a, rfl⟩
    have h := weightedLieTreeSpan_antitone v w d hrk (a.eval_mem_weighted_span v w hspan)
    exact (show weightedLieTreeSpan v w d r ≤ F.layer (d + 1) ⊔ weightedLieTreeSpan v w d r from
      le_sup_right) h
  · apply sup_le (F.layer_succ_le_rankLayer d r)
    apply Submodule.span_le.mpr
    rintro x ⟨a, ha, hr, rfl⟩
    have h := F.lieTreeEval_mem_rankLayer v w hw hv a
    rw [ha] at h
    exact F.rankLayer_rank_antitone d hr h

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3

variable (I : Type*) [Fintype I]

noncomputable def finiteLieTrees : ℕ → Finset (FreeMagma I)
  | 0 => ∅
  | n + 1 => by
    classical
    exact (Finset.univ.image FreeMagma.of) ∪
      (((finiteLieTrees n).product (finiteLieTrees n)).image (fun z => z.1 * z.2))

theorem mem_finiteLieTrees_of_length_le (a : FreeMagma I) {n : ℕ} (hn : a.length ≤ n) :
    a ∈ finiteLieTrees I n := by
  classical
  induction a using FreeMagma.rec generalizing n with
  | of i =>
    cases n with
    | zero => simp only [FreeMagma.length] at hn; omega
    | succ n =>
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  | mul a b ha hb =>
    have hapos := a.length_pos
    have hbpos := b.length_pos
    change a.length + b.length ≤ n at hn
    cases n with
    | zero => omega
    | succ n =>
      apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_image.mpr ⟨(a, b),
        Finset.mem_product.mpr ⟨ha (n := n) (by omega), hb (n := n) (by omega)⟩, rfl⟩

theorem finiteLieTrees_card_le (n : ℕ) :
    (finiteLieTrees I n).card ≤ (Fintype.card I + 2) ^ (3 ^ n) := by
  classical
  induction n with
  | zero => simp only [finiteLieTrees, Finset.card_empty, Nat.zero_le]
  | succ n ih =>
    let B := (Fintype.card I + 2) ^ (3 ^ n)
    have hB : Fintype.card I + 2 ≤ B := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (show 0 < Fintype.card I + 2 by omega)
        (show 1 ≤ 3 ^ n from pow_pos (show 0 < (3 : ℕ) by norm_num) n)
    have hm : Fintype.card I ≤ B ^ 2 := by
      have h := Nat.le_mul_of_pos_right B (show 0 < B by omega)
      nlinarith
    have hrec : (finiteLieTrees I (n + 1)).card ≤
        Fintype.card I + (finiteLieTrees I n).card ^ 2 := by
      apply (Finset.card_union_le _ _).trans
      have h1 := Finset.card_image_le (s := (Finset.univ : Finset I)) (f := FreeMagma.of)
      have h2 : (((finiteLieTrees I n).product (finiteLieTrees I n)).image
          (fun z => z.1 * z.2)).card ≤ (finiteLieTrees I n).card * (finiteLieTrees I n).card := by
        exact Finset.card_image_le.trans_eq (Finset.card_product _ _)
      simp only [Finset.card_univ] at h1
      simpa only [pow_two] using Nat.add_le_add h1 h2
    calc
      _ ≤ Fintype.card I + B ^ 2 := hrec.trans (Nat.add_le_add_left (Nat.pow_le_pow_left ih 2) _)
      _ ≤ B ^ 2 + B ^ 2 := Nat.add_le_add_right hm _
      _ = 2 * B ^ 2 := by omega
      _ ≤ B * B ^ 2 := Nat.mul_le_mul_right (B ^ 2) (show 2 ≤ B by omega)
      _ = B ^ 3 := by ring
      _ = _ := by dsimp [B]; rw [show 3 ^ (n + 1) = 3 ^ n * 3 from pow_succ 3 n, pow_mul]

variable {I} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def finiteWeightedLieValues (v : I → L) (w : I → ℕ) (d r : ℕ) : Finset L := by
  classical
  exact ((finiteLieTrees I d).filter (fun a => lieTreeWeight w a = d ∧ r ≤ a.length)).image
    (lieTreeEval v)

theorem weightedLieTreeSpan_eq_finite_span (v : I → L) (w : I → ℕ) (hw : ∀ i, 0 < w i)
    (d r : ℕ) : weightedLieTreeSpan v w d r =
      Submodule.span ℚ (finiteWeightedLieValues v w d r : Set L) := by
  classical
  unfold weightedLieTreeSpan
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, hr, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨?_, ha, hr⟩, rfl⟩
    apply mem_finiteLieTrees_of_length_le
    exact (lieTree_length_le_weight w hw a).trans_eq ha
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, hd, hr⟩ := Finset.mem_filter.mp ha
    exact ⟨a, hd, hr, rfl⟩

omit [LieAlgebra ℚ L] in
theorem finiteWeightedLieValues_card_le (v : I → L) (w : I → ℕ) (d r : ℕ) :
    (finiteWeightedLieValues v w d r).card ≤ (Fintype.card I + 2) ^ (3 ^ d) := by
  classical
  exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans (finiteLieTrees_card_le I d)

end Erdos3

end

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

theorem lieTreeEval_relabel (v : J → L) (f : I → J) (a : FreeMagma I) :
    lieTreeEval v (FreeMagma.map f a) = lieTreeEval (v ∘ f) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change ⁅lieTreeEval v (FreeMagma.map f a), lieTreeEval v (FreeMagma.map f b)⁆ = _
    exact congrArg₂ (fun x y : L => ⁅x, y⁆) ha hb

theorem lieTreeWeight_relabel (w : J → ℕ) (f : I → J) (a : FreeMagma I) :
    lieTreeWeight w (FreeMagma.map f a) = lieTreeWeight (w ∘ f) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change lieTreeWeight w (FreeMagma.map f a) + lieTreeWeight w (FreeMagma.map f b) = _
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeLength_relabel (f : I → J) (a : FreeMagma I) :
    (FreeMagma.map f a).length = a.length := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change (FreeMagma.map f a).length + (FreeMagma.map f b).length = _
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeSupport_relabel (f : I → J) (a : FreeMagma I) :
    lieTreeSupport (FreeMagma.map f a) = f '' lieTreeSupport a := by
  induction a using FreeMagma.rec with
  | of i => simp only [FreeMagma.map_of, lieTreeSupport, Set.image_singleton]
  | mul a b ha hb =>
    change lieTreeSupport (FreeMagma.map f a) ∪ lieTreeSupport (FreeMagma.map f b) = _
    rw [ha, hb, ← Set.image_union]
    rfl

abbrev LieTreeOccurrences : FreeMagma I → Type
  | .of _ => Unit
  | .mul a b => LieTreeOccurrences a ⊕ LieTreeOccurrences b

instance lieTreeOccurrencesFintype (a : FreeMagma I) : Fintype (LieTreeOccurrences a) := by
  induction a using FreeMagma.rec with
  | of i => exact inferInstanceAs (Fintype Unit)
  | mul a b ha hb =>
    let := ha
    let := hb
    exact inferInstanceAs (Fintype (LieTreeOccurrences a ⊕ LieTreeOccurrences b))

def lieTreeOccurrenceLabel : (a : FreeMagma I) → LieTreeOccurrences a → I
  | .of i => fun _ => i
  | .mul a b => Sum.elim (lieTreeOccurrenceLabel a) (lieTreeOccurrenceLabel b)

def lieTreeOccurrenceTree : (a : FreeMagma I) → FreeMagma (LieTreeOccurrences a)
  | .of _ => .of ()
  | .mul a b => .mul (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a))
    (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b))

theorem lieTreeOccurrenceTree_eval (v : I → L) (a : FreeMagma I) :
    lieTreeEval (v ∘ lieTreeOccurrenceLabel a) (lieTreeOccurrenceTree a) = lieTreeEval v a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change ⁅lieTreeEval _ (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)),
      lieTreeEval _ (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b))⁆ = _
    rw [lieTreeEval_relabel, lieTreeEval_relabel]
    exact congrArg₂ (fun x y : L => ⁅x, y⁆) ha hb

theorem lieTreeOccurrenceTree_weight (w : I → ℕ) (a : FreeMagma I) :
    lieTreeWeight (w ∘ lieTreeOccurrenceLabel a) (lieTreeOccurrenceTree a) = lieTreeWeight w a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change lieTreeWeight _ (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)) +
      lieTreeWeight _ (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b)) = _
    rw [lieTreeWeight_relabel, lieTreeWeight_relabel]
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeOccurrenceTree_length (a : FreeMagma I) :
    (lieTreeOccurrenceTree a).length = a.length := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)).length +
      (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b)).length = _
    rw [lieTreeLength_relabel, lieTreeLength_relabel]
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeOccurrenceTree_support (a : FreeMagma I) :
    lieTreeSupport (lieTreeOccurrenceTree a) = Set.univ := by
  induction a using FreeMagma.rec with
  | of i =>
    ext j
    cases j
    exact iff_of_true rfl trivial
  | mul a b ha hb =>
    change lieTreeSupport (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)) ∪
      lieTreeSupport (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b)) = _
    rw [lieTreeSupport_relabel, lieTreeSupport_relabel, ha, hb]
    ext j
    constructor
    · intro _; trivial
    · intro _
      cases j with
      | inl j => exact Or.inl ⟨j, Set.mem_univ _, rfl⟩
      | inr j => exact Or.inr ⟨j, Set.mem_univ _, rfl⟩

end Erdos3

end

section

namespace Erdos3

variable {R I J L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def bracketMultilinear
    (f : MultilinearMap R (fun _ : I => L) L)
    (g : MultilinearMap R (fun _ : J => L) L) :
    MultilinearMap R (fun _ : I ⊕ J => L) L :=
  MultilinearMap.uncurrySum
    { toFun := fun m =>
        ({ toFun := fun y => ⁅f m, y⁆
           map_add' := fun y z => lie_add (f m) y z
           map_smul' := fun c y => lie_smul c (f m) y } : L →ₗ[R] L).compMultilinearMap g
      map_update_add' m i x y := by
        ext v
        change ⁅f (Function.update m i (x + y)), g v⁆ =
          ⁅f (Function.update m i x), g v⁆ + ⁅f (Function.update m i y), g v⁆
        rw [f.map_update_add, add_lie]
      map_update_smul' m i c x := by
        ext v
        change ⁅f (Function.update m i (c • x)), g v⁆ = c • ⁅f (Function.update m i x), g v⁆
        rw [f.map_update_smul, smul_lie] }

theorem bracketMultilinear_apply
    (f : MultilinearMap R (fun _ : I => L) L)
    (g : MultilinearMap R (fun _ : J => L) L) (v : I ⊕ J → L) :
    bracketMultilinear f g v = ⁅f (v ∘ Sum.inl), g (v ∘ Sum.inr)⁆ := rfl

noncomputable def lieTreeOccurrenceMultilinear :
    (a : FreeMagma I) → MultilinearMap R (fun _ : LieTreeOccurrences a => L) L
  | .of _ => MultilinearMap.ofSubsingleton R L L () LinearMap.id
  | .mul a b => bracketMultilinear (lieTreeOccurrenceMultilinear a) (lieTreeOccurrenceMultilinear b)

theorem lieTreeOccurrenceMultilinear_apply (a : FreeMagma I) :
    ∀ v : LieTreeOccurrences a → L,
      lieTreeOccurrenceMultilinear (R := R) a v = lieTreeEval v (lieTreeOccurrenceTree a) := by
  induction a using FreeMagma.rec with
  | of i => intro v; rfl
  | mul a b ha hb =>
    intro v
    change ⁅lieTreeOccurrenceMultilinear a (v ∘ Sum.inl),
      lieTreeOccurrenceMultilinear b (v ∘ Sum.inr)⁆ = _
    rw [ha, hb]
    change _ = ⁅lieTreeEval v (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)),
      lieTreeEval v (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b))⁆
    rw [lieTreeEval_relabel, lieTreeEval_relabel]

theorem lieTreeOccurrenceMultilinear_original (v : I → L) (a : FreeMagma I) :
    lieTreeOccurrenceMultilinear (R := R) a (v ∘ lieTreeOccurrenceLabel a) = lieTreeEval v a :=
  (lieTreeOccurrenceMultilinear_apply a _).trans (lieTreeOccurrenceTree_eval v a)

theorem exists_linear_lieTree_expansion {E : Type*} [AddCommGroup E] [Module R E]
    (η : L →ₗ[R] E) (C D : I → Submodule R L) (hDC : ∀ i, D i ≤ C i)
    (a : FreeMagma I) (x : I → L) (hx : ∀ i, x i ∈ C i)
    (hvanish : ∀ v : LieTreeOccurrences a → L,
      (∀ i, v i ∈ C (lieTreeOccurrenceLabel a i)) → ∀ i j, i ≠ j →
        v i ∈ D (lieTreeOccurrenceLabel a i) → v j ∈ D (lieTreeOccurrenceLabel a j) →
        η (lieTreeEval v (lieTreeOccurrenceTree a)) = 0) :
    ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
      η (lieTreeEval (fun i => x i + (y i : L)) a) = η (lieTreeEval x a) + A y := by
  classical
  let f := η.compMultilinearMap (lieTreeOccurrenceMultilinear (R := R) a)
  obtain ⟨A, hA⟩ := exists_linear_expansion_of_two_vanish f
    (C ∘ lieTreeOccurrenceLabel a) (D ∘ lieTreeOccurrenceLabel a)
    (fun i => hDC (lieTreeOccurrenceLabel a i))
    (fun v hv i j hij hi hj => by
      change η (lieTreeOccurrenceMultilinear a v) = 0
      rw [lieTreeOccurrenceMultilinear_apply]
      exact hvanish v hv i j hij hi hj)
    (x ∘ lieTreeOccurrenceLabel a) (fun i => hx (lieTreeOccurrenceLabel a i))
  let diagonal : (∀ i, D i) →ₗ[R] (∀ j : LieTreeOccurrences a, D (lieTreeOccurrenceLabel a j)) :=
    LinearMap.pi (fun j => LinearMap.proj (lieTreeOccurrenceLabel a j))
  refine ⟨A.comp diagonal, ?_⟩
  intro y
  have h := hA (diagonal y)
  change η (lieTreeOccurrenceMultilinear a ((fun i => x i + (y i : L)) ∘
      lieTreeOccurrenceLabel a)) =
    η (lieTreeOccurrenceMultilinear a (x ∘ lieTreeOccurrenceLabel a)) + A (diagonal y) at h
  simpa only [lieTreeOccurrenceMultilinear_original, LinearMap.comp_apply] using h

end Erdos3

end

section

namespace Erdos3

variable {I : Type*}

def lieTreeMarkedCount (marked : I → Bool) (a : FreeMagma I) : ℕ :=
  lieTreeWeight (fun i => if marked i then 1 else 0) a

@[simp] theorem lieTreeMarkedCount_leaf (marked : I → Bool) (i : I) :
    lieTreeMarkedCount marked (.of i) = if marked i then 1 else 0 := rfl

@[simp] theorem lieTreeMarkedCount_mul (marked : I → Bool) (a b : FreeMagma I) :
    lieTreeMarkedCount marked (a * b) =
      lieTreeMarkedCount marked a + lieTreeMarkedCount marked b := rfl

theorem lieTreeMarkedCount_le_length (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMarkedCount marked a ≤ a.length := by
  induction a using FreeMagma.rec with
  | of i => simp only [lieTreeMarkedCount_leaf, FreeMagma.length]; split <;> omega
  | mul a b ha hb => exact Nat.add_le_add ha hb

theorem lieTreeWeight_eq_sum_occurrences (w : I → ℕ) (a : FreeMagma I) :
    lieTreeWeight w a = ∑ i : LieTreeOccurrences a, w (lieTreeOccurrenceLabel a i) := by
  induction a using FreeMagma.rec with
  | of i => simp [lieTreeWeight, LieTreeOccurrences, lieTreeOccurrenceLabel]
  | mul a b ha hb =>
    change lieTreeWeight w a + lieTreeWeight w b =
      ∑ i : LieTreeOccurrences a ⊕ LieTreeOccurrences b,
        w (Sum.elim (lieTreeOccurrenceLabel a) (lieTreeOccurrenceLabel b) i)
    rw [Fintype.sum_sum_type, ha, hb]
    rfl

theorem lieTreeMarkedCount_eq_card (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMarkedCount marked a =
      (Finset.univ.filter (fun i : LieTreeOccurrences a => marked (lieTreeOccurrenceLabel a i))).card := by
  classical
  rw [lieTreeMarkedCount, lieTreeWeight_eq_sum_occurrences]
  simp only [Finset.card_filter]

theorem exists_two_marked_occurrences (marked : I → Bool) (a : FreeMagma I)
    (ha : 2 ≤ lieTreeMarkedCount marked a) :
    ∃ i j : LieTreeOccurrences a, i ≠ j ∧
      marked (lieTreeOccurrenceLabel a i) = true ∧
      marked (lieTreeOccurrenceLabel a j) = true := by
  classical
  rw [lieTreeMarkedCount_eq_card] at ha
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < _ from ha)
  exact ⟨i, j, hij, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem multilinear_eq_of_one_vanish
    {R I L E : Type*} [CommRing R] [Fintype I]
    [AddCommGroup L] [Module R L] [AddCommGroup E] [Module R E]
    (f : MultilinearMap R (fun _ : I => L) E) (C P : I → Submodule R L)
    (hPC : ∀ i, P i ≤ C i)
    (hvanish : ∀ v : I → L, (∀ i, v i ∈ C i) → ∀ i, v i ∈ P i → f v = 0)
    (x y : I → L) (hx : ∀ i, x i ∈ C i) (hy : ∀ i, y i ∈ P i) :
    f (x + y) = f x := by
  classical
  rw [multilinear_eq_first_order_of_two_vanish f C P hPC
    (fun v hv i _j _hij hi _hj => hvanish v hv i hi) x y hx hy]
  suffices h : f.linearDeriv x y = 0 by rw [h, add_zero]
  rw [MultilinearMap.linearDeriv_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  refine hvanish (Function.update x i (y i)) ?_ i ?_
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hPC i (hy i)
    · simpa only [Function.update_of_ne hji] using hx j
  · simpa only [Function.update_self] using hy i

theorem lieTree_eq_of_one_petal_vanish
    {R I L E : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup E] [Module R E]
    (η : L →ₗ[R] E) (C P : I → Submodule R L) (hPC : ∀ i, P i ≤ C i)
    (a : FreeMagma I)
    (hvanish : ∀ v : LieTreeOccurrences a → L,
      (∀ i, v i ∈ C (lieTreeOccurrenceLabel a i)) →
      ∀ i, v i ∈ P (lieTreeOccurrenceLabel a i) →
        η (lieTreeEval v (lieTreeOccurrenceTree a)) = 0)
    (x y : I → L) (hx : ∀ i, x i ∈ C i) (hy : ∀ i, y i ∈ P i) :
    η (lieTreeEval (x + y) a) = η (lieTreeEval x a) := by
  let f := η.compMultilinearMap (lieTreeOccurrenceMultilinear (R := R) a)
  have h := multilinear_eq_of_one_vanish f (C ∘ lieTreeOccurrenceLabel a)
    (P ∘ lieTreeOccurrenceLabel a) (fun i => hPC (lieTreeOccurrenceLabel a i))
    (fun v hv i hi => by
      change η (lieTreeOccurrenceMultilinear a v) = 0
      rw [lieTreeOccurrenceMultilinear_apply]
      exact hvanish v hv i hi)
    (x ∘ lieTreeOccurrenceLabel a) (y ∘ lieTreeOccurrenceLabel a)
    (fun i => hx (lieTreeOccurrenceLabel a i)) (fun i => hy (lieTreeOccurrenceLabel a i))
  change η (lieTreeOccurrenceMultilinear a ((x + y) ∘ lieTreeOccurrenceLabel a)) =
    η (lieTreeOccurrenceMultilinear a (x ∘ lieTreeOccurrenceLabel a)) at h
  simpa only [lieTreeOccurrenceMultilinear_original] using h

end Erdos3

end

section

namespace Erdos3

variable {I σ : Type*}

noncomputable def lieTreeMultidegree (g : I → σ →₀ ℕ) : FreeMagma I → σ →₀ ℕ
  | .of i => g i
  | .mul a b => lieTreeMultidegree g a + lieTreeMultidegree g b

@[simp] theorem lieTreeMultidegree_leaf (g : I → σ →₀ ℕ) (i : I) :
    lieTreeMultidegree g (.of i) = g i := rfl

@[simp] theorem lieTreeMultidegree_mul (g : I → σ →₀ ℕ) (a b : FreeMagma I) :
    lieTreeMultidegree g (a * b) = lieTreeMultidegree g a + lieTreeMultidegree g b := rfl

theorem lieTreeMultidegree_apply (g : I → σ →₀ ℕ) (a : FreeMagma I) (j : σ) :
    lieTreeMultidegree g a j = lieTreeWeight (fun i => g i j) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb => exact congrArg₂ (· + ·) ha hb

noncomputable def markedGeneratorGrade (w : I → ℕ) (marked : I → Bool) (i : I) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 (w i) + Finsupp.single 1 (if marked i then 1 else 0) + Finsupp.single 2 1

theorem markedTreeGrade_weight (w : I → ℕ) (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMultidegree (markedGeneratorGrade w marked) a 0 = lieTreeWeight w a := by
  rw [lieTreeMultidegree_apply]
  simp [markedGeneratorGrade]

theorem markedTreeGrade_count (w : I → ℕ) (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMultidegree (markedGeneratorGrade w marked) a 1 = lieTreeMarkedCount marked a := by
  rw [lieTreeMultidegree_apply]
  simp [markedGeneratorGrade, lieTreeMarkedCount]

theorem markedTreeGrade_length (w : I → ℕ) (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMultidegree (markedGeneratorGrade w marked) a 2 = a.length := by
  induction a using FreeMagma.rec with
  | of i => simp [markedGeneratorGrade, FreeMagma.length]
  | mul a b ha hb => exact congrArg₂ (· + ·) ha hb

end Erdos3

end

end OAI
