/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.TruncatedSeriesFiltration
import OAI.Combinatorics.Progressions.Geometry.LieCoordinateScalarExtension

namespace OAI

section

namespace Erdos3
variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem map_freeLie_lift (φ : L →ₗ⁅ℚ⁆ M) (f : X → L) (p : FreeLieAlgebra ℚ X) :
    φ (FreeLieAlgebra.lift ℚ f p) = FreeLieAlgebra.lift ℚ (fun x => φ (f x)) p := by
  have h : φ.comp (FreeLieAlgebra.lift ℚ f) = FreeLieAlgebra.lift ℚ (fun x => φ (f x)) := by
    apply FreeLieAlgebra.hom_ext
    intro x
    simp
  exact DFunLike.congr_fun h p

theorem map_lieBCH (φ : L →ₗ⁅ℚ⁆ M) (s : ℕ) (a b : L) :
    φ (lieBCH s a b) = lieBCH s (φ a) (φ b) := by
  have hf : (fun x : Fin 2 => φ (![a, b] x)) = ![φ a, φ b] := by
    funext x
    fin_cases x <;> rfl
  simpa only [lieBCH, hf] using map_freeLie_lift φ ![a, b] (bchLiePolynomial s)

attribute [local instance] LieRing.ofAssociativeRing

noncomputable def scaledFreeLieEval (s : ℕ) :
    FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ TruncatedSeries (FreeAlgebra ℚ X) s :=
  FreeLieAlgebra.lift ℚ (scaledFreeGenerator s)

@[simp] theorem scaledFreeLieEval_of (s : ℕ) (x : X) :
    scaledFreeLieEval s (FreeLieAlgebra.of ℚ x) = scaledFreeGenerator s x :=
  FreeLieAlgebra.lift_of_apply _ _

theorem scaledFreeLieEval_eq (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    scaledFreeLieEval s p = truncatedSeriesMk s (freeScaleSeries (freeLieAssociativeExpansion p)) := by
  have h : FreeAlgebra.lift ℚ (scaledFreeGenerator (X := X) s) =
      (truncatedSeriesMk s).comp freeScaleSeries := by
    apply FreeAlgebra.hom_ext
    funext x
    simp [scaledFreeGenerator]
  change FreeLieAlgebra.lift ℚ (scaledFreeGenerator s) p = _
  rw [← freeLieAssociativeExpansion_eval, h]
  rfl

theorem lie_lift_eq_of_scaledFreeLieEval_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : FreeLieAlgebra ℚ X}
    (h : scaledFreeLieEval s p = scaledFreeLieEval s q) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q := by
  apply lie_lift_eq_of_scaled_series_eq f hnil
  simpa only [scaledFreeLieEval_eq] using h

end Erdos3

end

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
attribute [local instance] LieRing.ofAssociativeRing

theorem scaledFreeGenerator_mem_layer (s : ℕ) {X : Type*} (x : X) :
    scaledFreeGenerator s x ∈ (truncatedSeriesFiltration (A := FreeAlgebra ℚ X) s).layer 1 :=
  truncatedSeriesLayer_one.mpr (scaledFreeGenerator_positive s x)

theorem lieBCH_assoc (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (a b c : L) :
    lieBCH s (lieBCH s a b) c = lieBCH s a (lieBCH s b c) := by
  let x : Fin 3 → FreeLieAlgebra ℚ (Fin 3) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 3)) s
  have hx (i : Fin 3) : scaledFreeGenerator s i ∈ F.layer 1 := scaledFreeGenerator_mem_layer s i
  have h : scaledFreeLieEval s (lieBCH s (lieBCH s (x 0) (x 1)) (x 2)) =
      scaledFreeLieEval s (lieBCH s (x 0) (lieBCH s (x 1) (x 2))) := by
    simp only [map_lieBCH, x, scaledFreeLieEval_of]
    rw [F.lieBCH_eq (hx 0) (hx 1), F.lieBCH_eq (hx 1) (hx 2),
      F.lieBCH_eq (F.bch_mem le_rfl (hx 0) (hx 1)) (hx 2),
      F.lieBCH_eq (hx 0) (F.bch_mem le_rfl (hx 1) (hx 2))]
    exact nilpotentBCH_assoc (F.layerAlgebra 1) F.positive_nilpotent (hx 0) (hx 1) (hx 2)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b, c] hnil h
  simpa only [map_lieBCH, x, FreeLieAlgebra.lift_of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] using he

theorem lieBCH_zero_left (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (a : L) :
    lieBCH s 0 a = a := by
  let x : FreeLieAlgebra ℚ (Fin 1) := FreeLieAlgebra.of ℚ 0
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 1)) s
  have hx : scaledFreeGenerator s (0 : Fin 1) ∈ F.layer 1 := scaledFreeGenerator_mem_layer s 0
  have h : scaledFreeLieEval s (lieBCH s 0 x) = scaledFreeLieEval s x := by
    simp only [map_lieBCH, map_zero, x, scaledFreeLieEval_of]
    rw [F.lieBCH_eq (F.layer 1).zero_mem hx]
    exact nilpotentBCH_zero_left (F.isNilpotent_of_mem le_rfl hx)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq (fun _ : Fin 1 => a) hnil h
  simpa only [map_lieBCH, map_zero, x, FreeLieAlgebra.lift_of_apply] using he

theorem lieBCH_neg_left (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (a : L) :
    lieBCH s (-a) a = 0 := by
  let x : FreeLieAlgebra ℚ (Fin 1) := FreeLieAlgebra.of ℚ 0
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 1)) s
  have hx : scaledFreeGenerator s (0 : Fin 1) ∈ F.layer 1 := scaledFreeGenerator_mem_layer s 0
  have h : scaledFreeLieEval s (lieBCH s (-x) x) = scaledFreeLieEval s 0 := by
    simp only [map_lieBCH, map_neg, map_zero, x, scaledFreeLieEval_of]
    rw [F.lieBCH_eq ((F.layer 1).neg_mem hx) hx]
    exact nilpotentBCH_neg_left (F.isNilpotent_of_mem le_rfl hx)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq (fun _ : Fin 1 => a) hnil h
  simpa only [map_lieBCH, map_neg, map_zero, x, FreeLieAlgebra.lift_of_apply] using he

structure NilpotentLieBCHGroup (L : Type*) [LieRing L] [LieAlgebra ℚ L] (s : ℕ)
    (_hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) where
  coord : L

namespace NilpotentLieBCHGroup
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[ext] theorem ext {a b : NilpotentLieBCHGroup L s hnil} (h : a.coord = b.coord) : a = b := by
  cases a
  cases b
  cases h
  rfl

noncomputable instance : Mul (NilpotentLieBCHGroup L s hnil) where
  mul a b := ⟨lieBCH s a.coord b.coord⟩

instance : One (NilpotentLieBCHGroup L s hnil) where
  one := ⟨0⟩

instance : Inv (NilpotentLieBCHGroup L s hnil) where
  inv a := ⟨-a.coord⟩

@[simp] theorem coord_mul (a b : NilpotentLieBCHGroup L s hnil) :
    (a * b).coord = lieBCH s a.coord b.coord := rfl
@[simp] theorem coord_one : (1 : NilpotentLieBCHGroup L s hnil).coord = 0 := rfl
@[simp] theorem coord_inv (a : NilpotentLieBCHGroup L s hnil) : (a⁻¹).coord = -a.coord := rfl

noncomputable instance : Group (NilpotentLieBCHGroup L s hnil) :=
  Group.ofLeftAxioms
    (fun a b c => ext (lieBCH_assoc hnil a.coord b.coord c.coord))
    (fun a => ext (lieBCH_zero_left hnil a.coord))
    (fun a => ext (lieBCH_neg_left hnil a.coord))

noncomputable def map {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥} (φ : L →ₗ⁅ℚ⁆ M) :
    NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM where
  toFun a := ⟨φ a.coord⟩
  map_one' := ext (map_zero φ)
  map_mul' a b := ext (map_lieBCH φ s a.coord b.coord)

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

noncomputable def lieBCHList (s : ℕ) (f : X → L) : List X → L
  | [] => 0
  | x :: xs => lieBCH s (f x) (lieBCHList s f xs)

theorem map_lieBCHList (φ : L →ₗ⁅ℚ⁆ M) (s : ℕ) (f : X → L) (xs : List X) :
    φ (lieBCHList s f xs) = lieBCHList s (fun x => φ (f x)) xs := by
  induction xs with
  | nil => exact map_zero φ
  | cons x xs ih => simp only [lieBCHList, map_lieBCH, ih]

theorem lieBCHList_group_prod (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (f : X → L) (xs : List X) :
    ((xs.map (fun x => (⟨f x⟩ : NilpotentLieBCHGroup L s hnil))).prod).coord =
      lieBCHList s f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, NilpotentLieBCHGroup.coord_mul, lieBCHList, ih]

noncomputable def bchProductLiePolynomial (s : ℕ) (xs : List X) : FreeLieAlgebra ℚ X :=
  freeLieTruncation s (lieBCHList s (FreeLieAlgebra.of ℚ) xs)

theorem bchProductLiePolynomial_eval (s : ℕ)
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (f : X → L) (xs : List X) :
    FreeLieAlgebra.lift ℚ f (bchProductLiePolynomial s xs) = lieBCHList s f xs := by
  rw [bchProductLiePolynomial, lift_freeLieTruncation f hnil, map_lieBCHList]
  congr 1
  funext x
  exact FreeLieAlgebra.lift_of_apply _ _

theorem bchProductLiePolynomial_support_length (s : ℕ) (xs : List X)
    {w : FreeSemigroup X} (hw : w ∈ (freeLieWordExpansion (bchProductLiePolynomial s xs)).coeff.support) :
    w.length ≤ s := freeLieTruncation_support_length s _ hw

end Erdos3

end

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lieBCH_mem (K : LieSubalgebra ℚ L) (s : ℕ) {a b : L}
    (ha : a ∈ K) (hb : b ∈ K) : lieBCH s a b ∈ K := by
  have h := map_lieBCH K.incl s (⟨a, ha⟩ : K) (⟨b, hb⟩ : K)
  change ((lieBCH s (⟨a, ha⟩ : K) (⟨b, hb⟩ : K) : K) : L) = lieBCH s a b at h
  rw [← h]
  exact (lieBCH s (⟨a, ha⟩ : K) (⟨b, hb⟩ : K)).property

namespace NilpotentLieBCHGroup
variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def subgroup (K : LieSubalgebra ℚ L) : Subgroup (NilpotentLieBCHGroup L s hnil) where
  carrier := {a | a.coord ∈ K}
  one_mem' := K.zero_mem
  mul_mem' ha hb := lieBCH_mem K s ha hb
  inv_mem' ha := K.neg_mem ha

@[simp] theorem mem_subgroup (K : LieSubalgebra ℚ L) (a : NilpotentLieBCHGroup L s hnil) :
    a ∈ subgroup K ↔ a.coord ∈ K := Iff.rfl

end NilpotentLieBCHGroup

def lieQuotientMap (I : LieIdeal ℚ L) : L →ₗ⁅ℚ⁆ L ⧸ I :=
  { I.toSubmodule.mkQ with map_lie' := by intro a b; rfl }

theorem lieQuotientMap_surjective (I : LieIdeal ℚ L) : Function.Surjective (lieQuotientMap I) :=
  Submodule.mkQ_surjective _

@[simp] theorem lieQuotientMap_eq_zero (I : LieIdeal ℚ L) (a : L) :
    lieQuotientMap I a = 0 ↔ a ∈ I := Submodule.Quotient.mk_eq_zero _

theorem lie_quotient_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (I : LieIdeal ℚ L) :
    LieModule.lowerCentralSeries ℚ (L ⧸ I) (L ⧸ I) s = ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq s (lieQuotientMap_surjective I), hnil]
  simp

end Erdos3

end

section

namespace Erdos3

variable {X A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def bchProductPolynomial (s : ℕ) (xs : List X) : FreeAlgebra ℚ X :=
  finiteLog (s + 1)
    ((xs.map (fun x => finiteExp (s + 1) (FreeAlgebra.ι ℚ x))).prod - 1)

theorem bchProductPolynomial_eval (s : ℕ) (f : X → A) (xs : List X) :
    FreeAlgebra.lift ℚ f (bchProductPolynomial s xs) =
      finiteLog (s + 1) ((xs.map (fun x => finiteExp (s + 1) (f x))).prod - 1) := by
  simp only [bchProductPolynomial, map_finiteLog, map_sub, map_one,
    map_list_prod, List.map_map, Function.comp_def, map_finiteExp, FreeAlgebra.lift_ι_apply]

namespace NilpotentAlgebraFiltration

variable {s : ℕ} (F : NilpotentAlgebraFiltration A s) (f : X → A)

theorem lieBCHList_mem (hf : ∀ x, f x ∈ F.layer 1) (xs : List X) :
    lieBCHList s f xs ∈ F.layer 1 := by
  induction xs with
  | nil => exact (F.layer 1).zero_mem
  | cons x xs ih =>
    rw [lieBCHList, F.lieBCH_eq (hf x) ih]
    exact F.bch_mem le_rfl (hf x) ih

theorem exp_lieBCHList (hf : ∀ x, f x ∈ F.layer 1) (xs : List X) :
    IsNilpotent.exp (lieBCHList s f xs) = (xs.map (fun x => IsNilpotent.exp (f x))).prod := by
  induction xs with
  | nil => exact IsNilpotent.exp_zero
  | cons x xs ih =>
    rw [lieBCHList, F.lieBCH_eq (hf x) (F.lieBCHList_mem f hf xs),
      exp_nilpotentBCH (F.layerAlgebra 1) F.positive_nilpotent (hf x) (F.lieBCHList_mem f hf xs),
      ih, List.map_cons, List.prod_cons]

theorem bchProductPolynomial_formula (hf : ∀ x, f x ∈ F.layer 1) (xs : List X) :
    FreeAlgebra.lift ℚ f (bchProductPolynomial s xs) = lieBCHList s f xs := by
  have hx := F.lieBCHList_mem f hf xs
  have hn := F.isNilpotent_of_mem le_rfl hx
  have hprod : (xs.map (fun x => finiteExp (s + 1) (f x))).prod =
      IsNilpotent.exp (lieBCHList s f xs) := by
    rw [F.exp_lieBCHList f hf xs]
    congr 1
    apply List.map_congr_left
    intro x _
    exact finiteExp_eq_exp (F.pow_eq_zero le_rfl (hf x))
  rw [bchProductPolynomial_eval, hprod,
    finiteLog_eq_log (F.pow_eq_zero le_rfl (F.exp_sub_one_mem_layer hx hn)),
    nilpotentLog_exp_sub_one hn]

end NilpotentAlgebraFiltration

theorem bchProductLiePolynomial_associativeExpansion (s : ℕ) (xs : List X) :
    freeLieAssociativeExpansion (bchProductLiePolynomial s xs) =
      freeTruncation s (bchProductPolynomial s xs) := by
  rw [bchProductLiePolynomial, freeLieTruncation_associativeExpansion]
  apply freeTruncation_eq_of_scaled_series_eq
  rw [← scaledFreeLieEval_eq, map_lieBCHList]
  have hf : (fun x : X => scaledFreeLieEval s (FreeLieAlgebra.of ℚ x)) = scaledFreeGenerator s := by
    funext x
    exact scaledFreeLieEval_of s x
  rw [hf]
  have h := (truncatedSeriesFiltration (A := FreeAlgebra ℚ X) s).bchProductPolynomial_formula
    (scaledFreeGenerator s) (scaledFreeGenerator_mem_layer s) xs
  rw [← h]
  have he : FreeAlgebra.lift ℚ (scaledFreeGenerator (X := X) s) =
      (truncatedSeriesMk s).comp freeScaleSeries := by
    apply FreeAlgebra.hom_ext
    funext x
    simp [scaledFreeGenerator]
  rw [he]
  rfl

end Erdos3

end

section

namespace Erdos3

namespace NilpotentAlgebraFiltration
variable {A : Type*} [Ring A] [Algebra ℚ A] {s t : ℕ}

def extend (F : NilpotentAlgebraFiltration A s) (hst : s ≤ t) : NilpotentAlgebraFiltration A t where
  layer := F.layer
  antitone := F.antitone
  zero_eq_top := F.zero_eq_top
  mul_mem := F.mul_mem
  terminal := le_antisymm (by
    rw [← F.terminal]
    exact F.antitone (Nat.add_le_add_right hst 1)) bot_le

end NilpotentAlgebraFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
attribute [local instance] LieRing.ofAssociativeRing

theorem lieBCH_eq_add_of_isLieAbelian [IsLieAbelian L] {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    lieBCH s a b = a + b := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) 1
  have hx (i : Fin 2) : scaledFreeGenerator 1 i ∈ F.layer 1 := scaledFreeGenerator_mem_layer 1 i
  have hmul (i j : Fin 2) : scaledFreeGenerator 1 i * scaledFreeGenerator 1 j = 0 := by
    have h := F.mul_mem (hx i) (hx j)
    simpa only [F.terminal, Submodule.mem_bot] using h
  have hc : Commute (scaledFreeGenerator 1 (0 : Fin 2)) (scaledFreeGenerator 1 (1 : Fin 2)) := by
    change _ * _ = _ * _
    rw [hmul 0 1, hmul 1 0]
  have h : scaledFreeLieEval 1 (lieBCH s (x 0) (x 1)) = scaledFreeLieEval 1 (x 0 + x 1) := by
    simp only [map_lieBCH, map_add, x, scaledFreeLieEval_of]
    rw [(F.extend hs).lieBCH_eq (hx 0) (hx 1)]
    exact nilpotentBCH_eq_add_of_commute (F.isNilpotent_of_mem le_rfl (hx 0))
      (F.isNilpotent_of_mem le_rfl (hx 1)) hc
  have hn : LieModule.lowerCentralSeries ℚ L L 1 = ⊥ := by
    simp [LieModule.lowerCentralSeries_succ]
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hn h
  simpa only [map_lieBCH, map_add, x, FreeLieAlgebra.lift_of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using he

theorem lieBCH_eq_add_of_lie_eq_zero_pos {s : ℕ} (hs : 1 ≤ s) {a b : L}
    (hab : ⁅a, b⁆ = 0) : lieBCH s a b = a + b := by
  let K := LieSubalgebra.lieSpan ℚ L ({a, b} : Set L)
  have ha : a ∈ K := LieSubalgebra.subset_lieSpan (by simp)
  have hb : b ∈ K := LieSubalgebra.subset_lieSpan (by simp)
  have : IsLieAbelian K := by
    apply LieSubalgebra.isLieAbelian_lieSpan_iff.mpr
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact lie_self _
    · exact hab
    · rw [← lie_skew, hab, neg_zero]
    · exact lie_self _
  have h := congrArg K.incl (lieBCH_eq_add_of_isLieAbelian hs (⟨a, ha⟩ : K) (⟨b, hb⟩ : K))
  simp only [map_lieBCH, map_add] at h
  change lieBCH s a b = a + b at h
  exact h

theorem lieBCH_eq_add_of_lie_eq_zero {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {a b : L}
    (hab : ⁅a, b⁆ = 0) : lieBCH s a b = a + b := by
  by_cases hs : 1 ≤ s
  · exact lieBCH_eq_add_of_lie_eq_zero_pos hs hab
  · have hs0 : s = 0 := by omega
    subst s
    have he (z : L) : z = 0 := by
      have hz : z ∈ LieModule.lowerCentralSeries ℚ L L 0 := by simp
      simpa only [hnil, LieSubmodule.mem_bot] using hz
    rw [he a, he b, zero_add, lieBCH_zero_left hnil]

end Erdos3

end

section

namespace Erdos3

open Module MvPolynomial

noncomputable def bchBoxCoordinateBound (s d H : ℕ) (B : ℝ) : ℝ :=
  (((s + 1) * (2 * d + 1) ^ s : ℕ) : ℝ) * bchCoordinateHeight s d H * (2 * d) * s *
    B ^ (s * (2 * d + 1))

theorem bchBoxCoordinateBound_nonneg (s d H : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ bchBoxCoordinateBound s d H B := by
  unfold bchBoxCoordinateBound
  positivity

theorem lieBCH_sub_coordinates_bound {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H s : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (x y : L) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx : ∀ i, |e.repr x i| ≤ B) (hy : ∀ i, |e.repr y i| ≤ B)
    (hxy : ∀ i, |e.repr x i - e.repr y i| ≤ δ) (k : ι) :
    |e.repr (lieBCH s x (-y)) k| ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  classical
  let P := bchCoordinatePolynomial c s k
  let v : Fin 2 × ι → ℝ := fun z => e.repr (![x, -y] z.1) z.2
  let w : Fin 2 × ι → ℝ := fun z => e.repr (![y, -y] z.1) z.2
  have hdegree : P.totalDegree ≤ s := bchCoordinatePolynomial_totalDegree c s k
  have hv (z : Fin 2 × ι) : |v z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hx i
    · simpa [v] using hy i
  have hw (z : Fin 2 × ι) : |w z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hy i
    · simpa [w] using hy i
  have hvw (z : Fin 2 × ι) : |v z - w z| ≤ δ := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hxy i
    · simpa [v, w] using hδ
  have hcoeff (m) : |((P.coeff m : ℚ) : ℝ)| ≤ bchCoordinateHeight s (Fintype.card ι) H :=
    (bchCoordinatePolynomial_height c hc s k m).abs_real_le
  have h := abs_aeval_sub_aeval_box_bound P v w (Nat.cast_nonneg _) hB hδ hcoeff hv hw hvw hdegree
  have hyneg : lieBCH s y (-y) = 0 := by
    have hg := congrArg NilpotentLieBCHGroup.coord
      (mul_inv_cancel (⟨y⟩ : NilpotentLieBCHGroup L s hnil))
    exact hg
  have hevalv : aeval v P = e.repr (lieBCH s x (-y)) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x (-y) k
  have hevalw : aeval w P = e.repr (lieBCH s y (-y)) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s y (-y) k
  rw [hevalv, hevalw, hyneg, map_zero, Finsupp.zero_apply, sub_zero] at h
  have hcard := polynomial_support_card_le P hdegree
  apply h.trans
  dsimp only [bchBoxCoordinateBound]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hcard

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module

variable {X : Type*}

noncomputable def bchProductWordCoefficients (s : ℕ) (xs : List X) : FreeSemigroup X →₀ ℚ :=
  (freeLieWordExpansion (bchProductLiePolynomial s xs)).coeff

noncomputable def bchProductBracketSupport (s : ℕ) (xs : List X) : Finset (FreeSemigroup X) :=
  (bchProductWordCoefficients s xs).support

noncomputable def bchProductBracketCoefficient (s : ℕ) (xs : List X) (w : FreeSemigroup X) : ℚ :=
  bchProductWordCoefficients s xs w / w.length

theorem bchProductBracketSupport_length (s : ℕ) (xs : List X) {w : FreeSemigroup X}
    (hw : w ∈ bchProductBracketSupport s xs) : w.length ≤ s :=
  bchProductLiePolynomial_support_length s xs hw

theorem bchProductWordCoefficients_eq (s : ℕ) (xs : List X) (w : FreeSemigroup X) :
    bchProductWordCoefficients s xs w =
      if w.length ≤ s then freeWordCoefficients (bchProductPolynomial s xs) w.toFreeMonoid else 0 := by
  rw [bchProductWordCoefficients, ← freeWordCoefficients_embedding,
    wordPolynomialEmbedding_freeLieExpansion, bchProductLiePolynomial_associativeExpansion,
    freeWordCoefficients_truncation, freeSemigroup_toFreeMonoid_length]

theorem lieBCHList_bracket_formula {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (f : X → L) (xs : List X) :
    lieBCHList s f xs = ∑ w ∈ bchProductBracketSupport s xs,
      bchProductBracketCoefficient s xs w • dynkinWord f w := by
  rw [← bchProductLiePolynomial_eval s hnil f xs, ← dynkinProjection_lift]
  change (bchProductWordCoefficients s xs).sum
    (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord f w)) = _
  simp only [Finsupp.sum, bchProductBracketSupport, bchProductBracketCoefficient,
    smul_smul, div_eq_mul_inv]

variable {ι : Type*} [Fintype ι]

noncomputable def bchProductCoordinatePolynomial (c : ι → ι → ι → ℚ) (s : ℕ)
    (xs : List X) (k : ι) : MvPolynomial (X × ι) ℚ :=
  ∑ w ∈ bchProductBracketSupport s xs,
    C (bchProductBracketCoefficient s xs w) * dynkinCoordinatePolynomial c w k

theorem bchProductCoordinatePolynomial_totalDegree (c : ι → ι → ι → ℚ) (s : ℕ)
    (xs : List X) (k : ι) :
    (bchProductCoordinatePolynomial c s xs k).totalDegree ≤ s := by
  apply totalDegree_finsetSum_le
  intro w hw
  have h := totalDegree_mul (C (bchProductBracketCoefficient s xs w)) (dynkinCoordinatePolynomial c w k)
  rw [totalDegree_C, zero_add] at h
  exact h.trans ((dynkinCoordinatePolynomial_totalDegree c w k).trans
    (bchProductBracketSupport_length s xs hw))

theorem bchProductCoordinatePolynomial_support_card [Fintype X]
    (c : ι → ι → ι → ℚ) (s : ℕ) (xs : List X) (k : ι) :
    (bchProductCoordinatePolynomial c s xs k).support.card ≤
      (s + 1) * (Fintype.card X * Fintype.card ι + 1) ^ s := by
  simpa only [Fintype.card_prod] using polynomial_support_card_le
    (bchProductCoordinatePolynomial c s xs k) (bchProductCoordinatePolynomial_totalDegree c s xs k)

theorem bchProductCoordinatePolynomial_eval {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (f : X → L) (xs : List X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (bchProductCoordinatePolynomial (lieStructureConstants e) s xs k) =
        e.repr (lieBCHList s f xs) k := by
  rw [lieBCHList_bracket_formula s hnil]
  simp only [bchProductCoordinatePolynomial, map_sum, map_mul, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, dynkinCoordinatePolynomial_eval,
    map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem bchProductCoordinatePolynomial_eval_over {R L : Type*} [CommRing R] [Algebra ℚ R]
    [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
    (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (f : X → L) (xs : List X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (bchProductCoordinatePolynomial c s xs k) = e.repr (lieBCHList s f xs) k := by
  change _ = e.coord k (lieBCHList s f xs)
  rw [lieBCHList_bracket_formula s hnil]
  simp only [bchProductCoordinatePolynomial, map_sum, map_mul, aeval_C,
    dynkinCoordinatePolynomial_eval_over e c hc,
    LinearMap.map_smul_of_tower, Algebra.smul_def, Basis.coord_apply]

end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem lieBCH_sub_right_mem_of_mem_ideal
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (I : LieIdeal ℚ L)
    {a : L} (ha : a ∈ I) (b : L) : lieBCH s a b - b ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_lieBCH, (lieQuotientMap_eq_zero I a).mpr ha,
    lieBCH_zero_left (lie_quotient_lowerCentralSeries_eq_bot hnil I), sub_self]

theorem lieBCH_sub_left_mem_of_mem_ideal
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (I : LieIdeal ℚ L)
    (a : L) {b : L} (hb : b ∈ I) : lieBCH s a b - a ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_lieBCH, (lieQuotientMap_eq_zero I b).mpr hb,
    lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) (lie_zero _),
    add_zero, sub_self]

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dynkinWord_eq_zero_of_abelian [IsLieAbelian L] (f : X → L)
    (w : FreeSemigroup X) (hw : w.tail ≠ []) : dynkinWord f w = 0 := by
  unfold dynkinWord
  cases h : w.tail with
  | nil => exact False.elim (hw h)
  | cons x xs =>
      simp only [rightBracketList_cons, Module.End.mul_apply, rightBracket_apply,
        trivial_lie_zero, map_zero]

theorem bch_linear_words_sum {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    ∑ w ∈ (bchBracketSupport s).filter (fun w => w.tail = []),
      bchBracketCoefficient s w • dynkinWord ![a, b] w = a + b := by
  classical
  let : LieRing (ℚ × ℚ) := LieRing.ofAssociativeRing
  let : IsLieAbelian (ℚ × ℚ) :=
    ⟨fun x y => by rw [LieRing.of_associative_ring_bracket, mul_comm x y, sub_self]⟩
  let φ : (ℚ × ℚ) →ₗ[ℚ] L :=
    (LinearMap.fst ℚ ℚ ℚ).smulRight a + (LinearMap.snd ℚ ℚ ℚ).smulRight b
  let x : ℚ × ℚ := (1, 0)
  let y : ℚ × ℚ := (0, 1)
  have hxy (i : Fin 2) : φ (![x, y] i) = ![a, b] i := by
    fin_cases i <;> simp [φ, x, y]
  have hterm (w : FreeSemigroup (Fin 2)) :
      φ (dynkinWord ![x, y] w) = if w.tail = [] then dynkinWord ![a, b] w else 0 := by
    by_cases hw : w.tail = []
    · simp only [hw, ite_eq_left, dynkinWord, rightBracketList_nil, Module.End.one_apply]
      exact hxy w.head
    · rw [dynkinWord_eq_zero_of_abelian _ _ hw, map_zero, ite_eq_right hw]
  have h := congrArg φ (lieBCH_eq_add_of_isLieAbelian hs x y)
  rw [lieBCH_bracket_formula] at h
  simp only [map_sum, map_smul, hterm, smul_ite, smul_zero] at h
  simpa only [Finset.sum_filter, map_add, hxy 0, hxy 1, φ, x, y,
    LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    one_smul, zero_smul, add_zero, zero_add] using h

theorem lieBCH_eq_add_nonlinear_sum {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    lieBCH s a b = a + b +
      ∑ w ∈ (bchBracketSupport s).filter (fun w => w.tail ≠ []),
        bchBracketCoefficient s w • dynkinWord ![a, b] w := by
  classical
  rw [lieBCH_bracket_formula, ← bch_linear_words_sum hs a b]
  exact (Finset.sum_filter_add_sum_filter_not (bchBracketSupport s)
    (fun w => w.tail = []) (fun w => bchBracketCoefficient s w • dynkinWord ![a, b] w)).symm

end Erdos3

end

end OAI
