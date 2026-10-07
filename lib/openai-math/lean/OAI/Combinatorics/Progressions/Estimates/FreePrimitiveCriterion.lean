/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.MvPolynomial
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.FreeMonoid.FreeSemigroup
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import OAI.Combinatorics.Progressions.Estimates.TensorContraction
import OAI.Combinatorics.Progressions.Linear.DynkinProjection

namespace OAI

section

namespace Erdos3

variable {X : Type*}

noncomputable instance wordPolynomialLieRing : LieRing (WordPolynomial X) where
  bracket p q := p * q - q * p
  add_lie p q r := by change (p + q) * r - r * (p + q) = _; simp [add_mul, mul_add]; abel
  lie_add p q r := by change p * (q + r) - (q + r) * p = _; simp [add_mul, mul_add]; abel
  lie_self p := by change p * p - p * p = 0; exact sub_self _
  leibniz_lie p q r := by
    change p * (q * r - r * q) - (q * r - r * q) * p =
      (p * q - q * p) * r - r * (p * q - q * p) +
        (q * (p * r - r * p) - (p * r - r * p) * q)
    noncomm_ring

noncomputable instance wordPolynomialLieAlgebra : LieAlgebra ℚ (WordPolynomial X) where
  lie_smul c p q := by
    change p * (c • q) - (c • q) * p = c • (p * q - q * p)
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]

@[simp] theorem wordPolynomial_lie (p q : WordPolynomial X) : ⁅p, q⁆ = p * q - q * p := rfl

noncomputable def freeLieWordExpansion : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ WordPolynomial X :=
  FreeLieAlgebra.lift ℚ (fun x => MonoidAlgebra.single (FreeSemigroup.of x) 1)

@[simp] theorem freeLieWordExpansion_of (x : X) :
    freeLieWordExpansion (FreeLieAlgebra.of ℚ x) = MonoidAlgebra.single (FreeSemigroup.of x) 1 :=
  FreeLieAlgebra.lift_of_apply _ _

theorem freeLieWordExpansion_tree (t : FreeMagma X) :
    freeLieWordExpansion (lieTreeEval (FreeLieAlgebra.of ℚ) t) = commutatorTree t := by
  induction t using FreeMagma.rec with
  | of x => exact freeLieWordExpansion_of x
  | mul u v hu hv =>
    change freeLieWordExpansion ⁅lieTreeEval (FreeLieAlgebra.of ℚ) u,
      lieTreeEval (FreeLieAlgebra.of ℚ) v⁆ = _
    rw [LieHom.map_lie, hu, hv]
    rfl

theorem freeLie_mk_single_tree (t : FreeMagma X) :
    (FreeLieAlgebra.mk ℚ (MonoidAlgebra.single t 1) : FreeLieAlgebra ℚ X) =
      lieTreeEval (FreeLieAlgebra.of ℚ) t := by
  induction t using FreeMagma.rec with
  | of x => rfl
  | mul u v hu hv =>
    have hs := MonoidAlgebra.single_mul_single u v (1 : ℚ) 1
    simp only [one_mul] at hs
    change FreeLieAlgebra.mk ℚ (MonoidAlgebra.single (u * v) 1) = _
    rw [← hs, map_mul]
    change ⁅(FreeLieAlgebra.mk ℚ (MonoidAlgebra.single u 1) : FreeLieAlgebra ℚ X),
      (FreeLieAlgebra.mk ℚ (MonoidAlgebra.single v 1) : FreeLieAlgebra ℚ X)⁆ = _
    rw [hu, hv]
    rfl

theorem freeLie_linear_induction (P : FreeLieAlgebra ℚ X → Prop)
    (hz : P 0) (ha : ∀ x y, P x → P y → P (x + y))
    (hs : ∀ (r : ℚ) x, P x → P (r • x))
    (ht : ∀ t : FreeMagma X, P (lieTreeEval (FreeLieAlgebra.of ℚ) t))
    (x : FreeLieAlgebra ℚ X) : P x := by
  refine Quot.inductionOn x ?_
  intro q
  change P (FreeLieAlgebra.mk ℚ q)
  induction q using MonoidAlgebra.induction_linear with
  | zero =>
    change P (0 : FreeLieAlgebra ℚ X)
    exact hz
  | add p q hp hq =>
    change P ((FreeLieAlgebra.mk ℚ p : FreeLieAlgebra ℚ X) +
      (FreeLieAlgebra.mk ℚ q : FreeLieAlgebra ℚ X))
    exact ha _ _ hp hq
  | single t r =>
    have he : MonoidAlgebra.single t r = r • MonoidAlgebra.single t (1 : ℚ) := by simp
    rw [he, map_smul, freeLie_mk_single_tree]
    exact hs r _ (ht t)

theorem dynkinProjection_freeLieWordExpansion (x : FreeLieAlgebra ℚ X) :
    dynkinProjection (FreeLieAlgebra.of ℚ) (freeLieWordExpansion x) = x := by
  apply freeLie_linear_induction (fun x =>
    dynkinProjection (FreeLieAlgebra.of ℚ) (freeLieWordExpansion x) = x)
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    simp only [map_smul, hx]
  · intro t
    rw [freeLieWordExpansion_tree, dynkinProjection_commutatorTree]

theorem freeLieWordExpansion_injective :
    Function.Injective (freeLieWordExpansion (X := X)) :=
  Function.LeftInverse.injective dynkinProjection_freeLieWordExpansion

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def wordPolynomialEmbedding : WordPolynomial X →ₙₐ[ℚ] FreeAlgebra ℚ X :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toAlgHom.toNonUnitalAlgHom).comp
    (MonoidAlgebra.mapDomainNonUnitalAlgHom ℚ ℚ FreeSemigroup.toFreeMonoid)

theorem wordPolynomialEmbedding_injective : Function.Injective (wordPolynomialEmbedding (X := X)) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.injective.comp
    (MonoidAlgebra.mapDomain_injective FreeSemigroup.toFreeMonoid_injective)

@[simp] theorem wordPolynomialEmbedding_generator (x : X) :
    wordPolynomialEmbedding (MonoidAlgebra.single (FreeSemigroup.of x) 1) = FreeAlgebra.ι ℚ x := by
  let e : FreeAlgebra ℚ X ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid X) :=
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
  change e.symm (MonoidAlgebra.mapDomain FreeSemigroup.toFreeMonoid
    (MonoidAlgebra.single (FreeSemigroup.of x) 1)) = _
  rw [MonoidAlgebra.mapDomain_single, FreeSemigroup.toFreeMonoid_of]
  apply e.injective
  rw [e.apply_symm_apply]
  change MonoidAlgebra.single (FreeMonoid.of x) 1 =
    FreeAlgebra.lift ℚ (fun x => MonoidAlgebra.of ℚ (FreeMonoid X) (FreeMonoid.of x))
      (FreeAlgebra.ι ℚ x)
  rw [FreeAlgebra.lift_ι_apply]
  rfl

noncomputable def wordPolynomialEmbeddingLie : WordPolynomial X →ₗ⁅ℚ⁆ FreeAlgebra ℚ X where
  toFun := wordPolynomialEmbedding
  map_add' := map_add wordPolynomialEmbedding
  map_smul' := map_smul wordPolynomialEmbedding
  map_lie' {p q} := by
    change wordPolynomialEmbedding (p * q - q * p) =
      wordPolynomialEmbedding p * wordPolynomialEmbedding q -
        wordPolynomialEmbedding q * wordPolynomialEmbedding p
    rw [map_sub, map_mul, map_mul]

noncomputable def freeLieAssociativeExpansion : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ FreeAlgebra ℚ X :=
  FreeLieAlgebra.lift ℚ (FreeAlgebra.ι ℚ)

theorem wordPolynomialEmbedding_comp_freeLie :
    wordPolynomialEmbeddingLie.comp freeLieWordExpansion =
      (freeLieAssociativeExpansion : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ FreeAlgebra ℚ X) := by
  apply FreeLieAlgebra.hom_ext
  intro x
  change wordPolynomialEmbedding (freeLieWordExpansion (FreeLieAlgebra.of ℚ x)) =
    freeLieAssociativeExpansion (FreeLieAlgebra.of ℚ x)
  rw [freeLieWordExpansion_of, wordPolynomialEmbedding_generator]
  exact (FreeLieAlgebra.lift_of_apply _ _).symm

theorem freeLieAssociativeExpansion_injective :
    Function.Injective (freeLieAssociativeExpansion (X := X)) := by
  rw [← wordPolynomialEmbedding_comp_freeLie]
  exact wordPolynomialEmbedding_injective.comp freeLieWordExpansion_injective

theorem freeLie_eq_of_associative_eq {p q : FreeLieAlgebra ℚ X}
    (h : freeLieAssociativeExpansion p = freeLieAssociativeExpansion q) : p = q :=
  freeLieAssociativeExpansion_injective h

theorem freeLie_universalEnveloping_injective :
    Function.Injective (UniversalEnvelopingAlgebra.ι ℚ (L := FreeLieAlgebra ℚ X)) := by
  intro p q hpq
  apply freeLieAssociativeExpansion_injective
  have h := congrArg (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℚ X) hpq
  change UniversalEnvelopingAlgebra.lift ℚ freeLieAssociativeExpansion
      (UniversalEnvelopingAlgebra.ι ℚ p) =
    UniversalEnvelopingAlgebra.lift ℚ freeLieAssociativeExpansion
      (UniversalEnvelopingAlgebra.ι ℚ q) at h
  simpa only [UniversalEnvelopingAlgebra.lift_ι_apply] using h

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}

noncomputable def freeWord : FreeMonoid X →* FreeAlgebra ℚ X :=
  FreeMonoid.lift (FreeAlgebra.ι ℚ)

@[simp] theorem freeWord_of (x : X) : freeWord (FreeMonoid.of x) = FreeAlgebra.ι ℚ x :=
  FreeMonoid.lift_eval_of _ _

theorem freeWord_coeff (w : FreeMonoid X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (freeWord w) = MonoidAlgebra.single w 1 := by
  have h : FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom.toMonoidHom.comp freeWord =
      MonoidAlgebra.of ℚ (FreeMonoid X) := by
    apply FreeMonoid.hom_eq
    intro x
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  exact DFunLike.congr_fun h w

theorem freeWord_single_symm (w : FreeMonoid X) (r : ℚ) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single w r) = r • freeWord w := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  simp only [AlgEquiv.apply_symm_apply, map_smul, freeWord_coeff]
  simp

noncomputable def freeWordLinearMap {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeMonoid X → M) : FreeAlgebra ℚ X →ₗ[ℚ] M :=
  (Finsupp.linearCombination ℚ v).comp
    ((MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap.comp
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap)

@[simp] theorem freeWordLinearMap_word {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeMonoid X → M) (w : FreeMonoid X) : freeWordLinearMap v (freeWord w) = v w := by
  simp [freeWordLinearMap, freeWord_coeff]

theorem freeAlgebra_linear_induction (P : FreeAlgebra ℚ X → Prop)
    (hz : P 0) (ha : ∀ p q, P p → P q → P (p + q))
    (hs : ∀ (r : ℚ) p, P p → P (r • p)) (hw : ∀ w, P (freeWord w))
    (p : FreeAlgebra ℚ X) : P p := by
  obtain ⟨q, rfl⟩ := FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.surjective p
  induction q using MonoidAlgebra.induction_linear with
  | zero => simpa only [map_zero] using hz
  | add p q hp hq => simpa only [map_add] using ha _ _ hp hq
  | single w r => rw [freeWord_single_symm]; exact hs r _ (hw w)

theorem freeMonoid_induction_right (P : FreeMonoid X → Prop) (h1 : P 1)
    (hstep : ∀ w x, P w → P (w * FreeMonoid.of x)) (w : FreeMonoid X) : P w := by
  have h : ∀ xs : List X, P (FreeMonoid.ofList xs) := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil => exact h1
    | append_singleton xs x ih =>
      rw [FreeMonoid.ofList_append, FreeMonoid.ofList_singleton]
      exact hstep _ _ ih
  exact h w.toList

noncomputable def freeDegree : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  freeWordLinearMap (fun w => (w.length : ℚ) • freeWord w)

@[simp] theorem freeDegree_word (w : FreeMonoid X) :
    freeDegree (freeWord w) = (w.length : ℚ) • freeWord w := freeWordLinearMap_word _ _

@[simp] theorem freeDegree_one : freeDegree (1 : FreeAlgebra ℚ X) = 0 := by
  have h := freeDegree_word (1 : FreeMonoid X)
  simpa using h

@[simp] theorem freeDegree_generator (x : X) : freeDegree (FreeAlgebra.ι ℚ x) = FreeAlgebra.ι ℚ x := by
  have h := freeDegree_word (FreeMonoid.of x)
  simpa using h

theorem freeDegree_mul (p q : FreeAlgebra ℚ X) :
    freeDegree (p * q) = freeDegree p * q + p * freeDegree q := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDegree (p * q) = freeDegree p * q + p * freeDegree q)
  · simp
  · intro p₁ p₂ h₁ h₂
    simp only [add_mul, map_add, h₁, h₂]
    abel
  · intro r p hp
    simp only [smul_mul_assoc, map_smul, hp, smul_add]
  · intro u
    apply freeAlgebra_linear_induction (fun q =>
      freeDegree (freeWord u * q) = freeDegree (freeWord u) * q + freeWord u * freeDegree q)
    · simp
    · intro q₁ q₂ h₁ h₂
      simp only [mul_add, map_add, h₁, h₂]
      abel
    · intro r q hq
      simp only [mul_smul_comm, map_smul, hq, smul_add]
    · intro v
      rw [← map_mul, freeDegree_word, FreeMonoid.length_mul, Nat.cast_add, add_smul,
        map_mul, freeDegree_word, freeDegree_word, smul_mul_assoc, mul_smul_comm]

end Erdos3

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem map_lieTreeEval (φ : L →ₗ⁅ℚ⁆ M) (f : X → L) (t : FreeMagma X) :
    φ (lieTreeEval f t) = lieTreeEval (fun x => φ (f x)) t := by
  induction t using FreeMagma.rec with
  | of x => rfl
  | mul u v hu hv => simp only [lieTreeEval, LieHom.map_lie, hu, hv]

theorem lift_lieTreeEval (f : X → L) (t : FreeMagma X) :
    FreeLieAlgebra.lift ℚ f (lieTreeEval (FreeLieAlgebra.of ℚ) t) = lieTreeEval f t := by
  rw [map_lieTreeEval]
  simp only [FreeLieAlgebra.lift_of_apply]

theorem dynkinProjection_lift (f : X → L) (x : FreeLieAlgebra ℚ X) :
    dynkinProjection f (freeLieWordExpansion x) = FreeLieAlgebra.lift ℚ f x := by
  apply freeLie_linear_induction (fun x =>
    dynkinProjection f (freeLieWordExpansion x) = FreeLieAlgebra.lift ℚ f x)
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    simp only [map_smul, hx]
  · intro t
    rw [freeLieWordExpansion_tree, dynkinProjection_commutatorTree, lift_lieTreeEval]

theorem rightBracketList_mem_lowerCentralSeries (f : X → L) (xs : List X)
    {n : ℕ} {z : L} (hz : z ∈ LieModule.lowerCentralSeries ℚ L L n) :
    rightBracketList f xs z ∈ LieModule.lowerCentralSeries ℚ L L (n + xs.length) := by
  induction xs generalizing n z with
  | nil => simpa only [rightBracketList_nil, Module.End.one_apply, List.length_nil, Nat.add_zero] using hz
  | cons x xs ih =>
    have hleft : ⁅f x, z⁆ ∈ LieModule.lowerCentralSeries ℚ L L (n + 1) := by
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hz
    have hright : ⁅z, f x⁆ ∈ LieModule.lowerCentralSeries ℚ L L (n + 1) := by
      rw [← lie_skew z (f x)]
      exact (LieModule.lowerCentralSeries ℚ L L (n + 1)).neg_mem hleft
    have h := ih hright
    simpa only [rightBracketList_cons, Module.End.mul_apply, rightBracket_apply,
      List.length_cons, Nat.add_assoc, Nat.add_comm 1 xs.length] using h

theorem dynkinWord_mem_lowerCentralSeries (f : X → L) (w : FreeSemigroup X) :
    dynkinWord f w ∈ LieModule.lowerCentralSeries ℚ L L w.tail.length := by
  have h : f w.head ∈ LieModule.lowerCentralSeries ℚ L L 0 := by
    rw [LieModule.lowerCentralSeries_zero]
    exact LieSubmodule.mem_top _
  simpa only [dynkinWord, Nat.zero_add] using rightBracketList_mem_lowerCentralSeries f w.tail h

theorem dynkinWord_eq_zero_of_length_gt (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {w : FreeSemigroup X}
    (hw : s < w.length) : dynkinWord f w = 0 := by
  have hle : s ≤ w.tail.length := by change s < w.tail.length + 1 at hw; omega
  have h := LieModule.antitone_lowerCentralSeries ℚ L L hle
    (dynkinWord_mem_lowerCentralSeries f w)
  simpa only [hnil, LieSubmodule.mem_bot] using h

theorem dynkinProjection_eq_zero_of_low_coeff_zero (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p : WordPolynomial X}
    (hp : ∀ w, w.length ≤ s → p.coeff w = 0) : dynkinProjection f p = 0 := by
  classical
  change p.coeff.sum (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord f w)) = 0
  apply Finset.sum_eq_zero
  intro w hw
  have hgt : s < w.length := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hw) (hp w (Nat.le_of_not_gt hn))
  dsimp only
  rw [dynkinWord_eq_zero_of_length_gt f hnil hgt, smul_zero, smul_zero]

theorem dynkinProjection_eq_of_low_coeff_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : WordPolynomial X}
    (hpq : ∀ w, w.length ≤ s → p.coeff w = q.coeff w) :
    dynkinProjection f p = dynkinProjection f q := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply dynkinProjection_eq_zero_of_low_coeff_zero f hnil
  intro w hw
  change p.coeff w - q.coeff w = 0
  rw [hpq w hw, sub_self]

theorem lie_lift_eq_of_low_word_coeff_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : FreeLieAlgebra ℚ X}
    (hpq : ∀ w, w.length ≤ s →
      (freeLieWordExpansion p).coeff w = (freeLieWordExpansion q).coeff w) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q := by
  rw [← dynkinProjection_lift f p, ← dynkinProjection_lift f q]
  exact dynkinProjection_eq_of_low_coeff_eq f hnil hpq

end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}

noncomputable def freeCoproduct : FreeAlgebra ℚ X →ₐ[ℚ]
    FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X :=
  FreeAlgebra.lift ℚ (fun x => FreeAlgebra.ι ℚ x ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] FreeAlgebra.ι ℚ x)

@[simp] theorem freeCoproduct_generator (x : X) :
    freeCoproduct (FreeAlgebra.ι ℚ x) =
      FreeAlgebra.ι ℚ x ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] FreeAlgebra.ι ℚ x :=
  FreeAlgebra.lift_ι_apply _ _

noncomputable def freeAugmentation : FreeAlgebra ℚ X →ₐ[ℚ] ℚ :=
  FreeAlgebra.lift ℚ (fun _ => 0)

@[simp] theorem freeAugmentation_generator (x : X) : freeAugmentation (FreeAlgebra.ι ℚ x) = 0 :=
  FreeAlgebra.lift_ι_apply _ _

noncomputable def freeAntipodeOp : FreeAlgebra ℚ X →ₐ[ℚ] (FreeAlgebra ℚ X)ᵐᵒᵖ :=
  FreeAlgebra.lift ℚ (fun x => MulOpposite.op (-FreeAlgebra.ι ℚ x))

noncomputable def freeAntipode : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  (MulOpposite.opLinearEquiv ℚ).symm.toLinearMap.comp freeAntipodeOp.toLinearMap

@[simp] theorem freeAntipode_generator (x : X) : freeAntipode (FreeAlgebra.ι ℚ x) = -FreeAlgebra.ι ℚ x := by
  change MulOpposite.unop (freeAntipodeOp (FreeAlgebra.ι ℚ x)) = _
  rw [freeAntipodeOp, FreeAlgebra.lift_ι_apply]
  rfl

@[simp] theorem freeAntipode_one : freeAntipode (1 : FreeAlgebra ℚ X) = 1 := by
  change MulOpposite.unop (freeAntipodeOp 1) = 1
  rw [map_one, MulOpposite.unop_one]

theorem freeAntipode_mul (p q : FreeAlgebra ℚ X) :
    freeAntipode (p * q) = freeAntipode q * freeAntipode p := by
  change MulOpposite.unop (freeAntipodeOp (p * q)) = _
  rw [map_mul, MulOpposite.unop_mul]
  rfl

def FreePrimitive (p : FreeAlgebra ℚ X) : Prop :=
  freeCoproduct p = p ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] p

theorem freePrimitive_generator (x : X) : FreePrimitive (FreeAlgebra.ι ℚ x) :=
  freeCoproduct_generator x

theorem FreePrimitive.add {p q : FreeAlgebra ℚ X} (hp : FreePrimitive p) (hq : FreePrimitive q) :
    FreePrimitive (p + q) := by
  unfold FreePrimitive at hp hq ⊢
  simp only [map_add, hp, hq, add_tmul, tmul_add]
  abel

theorem FreePrimitive.smul {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) (r : ℚ) :
    FreePrimitive (r • p) := by
  unfold FreePrimitive at hp ⊢
  simp only [map_smul, hp, smul_add, smul_tmul', tmul_smul]

theorem FreePrimitive.commutator {p q : FreeAlgebra ℚ X}
    (hp : FreePrimitive p) (hq : FreePrimitive q) : FreePrimitive (p * q - q * p) := by
  unfold FreePrimitive at hp hq ⊢
  simp only [map_sub, map_mul, hp, hq, add_mul, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, sub_tmul, tmul_sub]
  abel

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}

noncomputable def freeScaleSeries : FreeAlgebra ℚ X →ₐ[ℚ] PowerSeries (FreeAlgebra ℚ X) :=
  FreeAlgebra.lift ℚ (fun x => PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x))

@[simp] theorem freeScaleSeries_generator (x : X) :
    freeScaleSeries (FreeAlgebra.ι ℚ x) = PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x) :=
  FreeAlgebra.lift_ι_apply _ _

theorem freeScaleSeries_word (w : FreeMonoid X) :
    freeScaleSeries (freeWord w) = PowerSeries.monomial w.length (freeWord w) := by
  induction w using freeMonoid_induction_right with
  | h1 => simp
  | hstep w x hw =>
    rw [map_mul, map_mul, freeWord_of, hw, freeScaleSeries_generator,
      PowerSeries.monomial_mul_monomial]
    simp only [FreeMonoid.length_mul, FreeMonoid.length_of]

noncomputable def freeHomogeneousPart (n : ℕ) : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  ((PowerSeries.coeff n).restrictScalars ℚ).comp freeScaleSeries.toLinearMap

theorem freeHomogeneousPart_apply (n : ℕ) (p : FreeAlgebra ℚ X) :
    freeHomogeneousPart n p = PowerSeries.coeff n (freeScaleSeries p) := rfl

@[simp] theorem freeHomogeneousPart_word (n : ℕ) (w : FreeMonoid X) :
    freeHomogeneousPart n (freeWord w) = if n = w.length then freeWord w else 0 := by
  rw [freeHomogeneousPart_apply, freeScaleSeries_word, PowerSeries.coeff_monomial]

theorem freeDegree_homogeneousPart (n : ℕ) (p : FreeAlgebra ℚ X) :
    freeDegree (freeHomogeneousPart n p) = (n : ℚ) • freeHomogeneousPart n p := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDegree (freeHomogeneousPart n p) = (n : ℚ) • freeHomogeneousPart n p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq, smul_add]
  · intro r p hp
    simp only [map_smul, hp, smul_comm r (n : ℚ)]
  · intro w
    by_cases h : n = w.length
    · simp [h]
    · simp [h]

theorem freeHomogeneousPart_comp (n m : ℕ) (p : FreeAlgebra ℚ X) :
    freeHomogeneousPart n (freeHomogeneousPart m p) =
      if n = m then freeHomogeneousPart m p else 0 := by
  apply freeAlgebra_linear_induction (fun p =>
    freeHomogeneousPart n (freeHomogeneousPart m p) =
      if n = m then freeHomogeneousPart m p else 0)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
    split_ifs <;> simp
  · intro r p hp
    simp only [map_smul, hp]
    split_ifs <;> simp
  · intro w
    by_cases hm : m = w.length
    · simp [hm]
    · simp [hm]

noncomputable def freeTruncation (s : ℕ) : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  ∑ n ∈ Finset.range (s + 1), freeHomogeneousPart n

theorem freeTruncation_apply (s : ℕ) (p : FreeAlgebra ℚ X) :
    freeTruncation s p = ∑ n ∈ Finset.range (s + 1), freeHomogeneousPart n p := by
  simp [freeTruncation]

@[simp] theorem freeTruncation_word (s : ℕ) (w : FreeMonoid X) :
    freeTruncation s (freeWord w) = if w.length ≤ s then freeWord w else 0 := by
  rw [freeTruncation_apply]
  simp only [freeHomogeneousPart_word]
  simp [Finset.sum_ite_eq']

theorem freeTruncation_idempotent (s : ℕ) (p : FreeAlgebra ℚ X) :
    freeTruncation s (freeTruncation s p) = freeTruncation s p := by
  apply freeAlgebra_linear_induction (fun p =>
    freeTruncation s (freeTruncation s p) = freeTruncation s p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro r p hp
    simp only [map_smul, hp]
  · intro w
    rw [freeTruncation_word]
    split_ifs with hw <;> simp [hw]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

noncomputable def wordTruncation (s : ℕ) : WordPolynomial X →ₗ[ℚ] WordPolynomial X :=
  wordLinearMap (fun w => if w.length ≤ s then MonoidAlgebra.single w 1 else 0)

@[simp] theorem wordTruncation_single (s : ℕ) (w : FreeSemigroup X) (r : ℚ) :
    wordTruncation s (MonoidAlgebra.single w r) =
      if w.length ≤ s then MonoidAlgebra.single w r else 0 := by
  simp only [wordTruncation, wordLinearMap_single]
  split_ifs <;> simp

theorem wordTruncation_coeff (s : ℕ) (p : WordPolynomial X) (w : FreeSemigroup X) :
    (wordTruncation s p).coeff w = if w.length ≤ s then p.coeff w else 0 := by
  classical
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  | single u r =>
    rw [wordTruncation_single]
    by_cases he : u = w
    · subst u
      split_ifs <;> simp
    · split_ifs <;> simp [he]

theorem wordTruncation_idempotent (s : ℕ) (p : WordPolynomial X) :
    wordTruncation s (wordTruncation s p) = wordTruncation s p := by
  ext w
  simp only [wordTruncation_coeff]
  split_ifs <;> rfl

theorem wordTruncation_mul (s : ℕ) (p q : WordPolynomial X) :
    wordTruncation s (p * q) = wordTruncation s (wordTruncation s p * wordTruncation s q) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p₁ p₂ hp₁ hp₂ => simp only [add_mul, map_add, hp₁, hp₂]
  | single u r =>
    induction q using MonoidAlgebra.induction_linear with
    | zero => simp
    | add q₁ q₂ hq₁ hq₂ => simp only [mul_add, map_add, hq₁, hq₂]
    | single v t =>
      by_cases hu : u.length ≤ s
      · by_cases hv : v.length ≤ s
        · simp only [wordTruncation_single, hu, hv, ite_true]
        · have huv : ¬ u.length + v.length ≤ s := by omega
          simp [wordTruncation_single, MonoidAlgebra.single_mul_single, hu, hv, huv]
      · have huv : ¬ u.length + v.length ≤ s := by omega
        simp [wordTruncation_single, MonoidAlgebra.single_mul_single, hu, huv]

theorem wordTruncation_eq_iff (s : ℕ) (p q : WordPolynomial X) :
    wordTruncation s p = wordTruncation s q ↔
      ∀ w, w.length ≤ s → p.coeff w = q.coeff w := by
  constructor
  · intro h w hw
    have he := congrArg (fun p : WordPolynomial X => p.coeff w) h
    simpa only [wordTruncation_coeff, hw, ite_true] using he
  · intro h
    ext w
    simp only [wordTruncation_coeff]
    split_ifs with hw
    · exact h w hw
    · rfl

section Lie
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dynkinProjection_wordTruncation (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (p : WordPolynomial X) :
    dynkinProjection f (wordTruncation s p) = dynkinProjection f p := by
  apply dynkinProjection_eq_of_low_coeff_eq f hnil
  intro w hw
  simp only [wordTruncation_coeff, hw, ite_true]

theorem lie_lift_eq_of_wordTruncation_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : FreeLieAlgebra ℚ X}
    (h : wordTruncation s (freeLieWordExpansion p) = wordTruncation s (freeLieWordExpansion q)) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q :=
  lie_lift_eq_of_low_word_coeff_eq f hnil ((wordTruncation_eq_iff _ _ _).mp h)

end Lie
end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def freeAssociativeLieSubalgebra : LieSubalgebra ℚ (FreeAlgebra ℚ X) :=
  freeLieAssociativeExpansion.range

theorem freeAssociativeLieSubalgebra_generator (x : X) :
    FreeAlgebra.ι ℚ x ∈ freeAssociativeLieSubalgebra := by
  exact ⟨FreeLieAlgebra.of ℚ x, FreeLieAlgebra.lift_of_apply _ _⟩

noncomputable def freeAntipodeConvolution : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  (tensorContract freeAntipode LinearMap.id).comp freeCoproduct.toLinearMap

noncomputable def freeDynkinConvolution : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  (tensorContract freeAntipode freeDegree).comp freeCoproduct.toLinearMap

@[simp] theorem freeAntipodeConvolution_one :
    freeAntipodeConvolution (1 : FreeAlgebra ℚ X) = 1 := by
  simp [freeAntipodeConvolution, Algebra.TensorProduct.one_def]

@[simp] theorem freeDynkinConvolution_one :
    freeDynkinConvolution (1 : FreeAlgebra ℚ X) = 0 := by
  simp [freeDynkinConvolution, Algebra.TensorProduct.one_def]

theorem freeAntipodeConvolution_mul_generator (p : FreeAlgebra ℚ X) (x : X) :
    freeAntipodeConvolution (p * FreeAlgebra.ι ℚ x) =
      -FreeAlgebra.ι ℚ x * freeAntipodeConvolution p +
        freeAntipodeConvolution p * FreeAlgebra.ι ℚ x := by
  change tensorContract freeAntipode LinearMap.id (freeCoproduct (p * FreeAlgebra.ι ℚ x)) = _
  rw [map_mul, freeCoproduct_generator, mul_add, map_add,
    tensorContract_mul_left _ _ freeAntipode_mul, tensorContract_id_mul_right,
    freeAntipode_generator]
  rfl

theorem freeDynkinConvolution_mul_generator (p : FreeAlgebra ℚ X) (x : X) :
    freeDynkinConvolution (p * FreeAlgebra.ι ℚ x) =
      -FreeAlgebra.ι ℚ x * freeDynkinConvolution p +
        (freeDynkinConvolution p * FreeAlgebra.ι ℚ x +
          freeAntipodeConvolution p * FreeAlgebra.ι ℚ x) := by
  change tensorContract freeAntipode freeDegree (freeCoproduct (p * FreeAlgebra.ι ℚ x)) = _
  rw [map_mul, freeCoproduct_generator, mul_add, map_add,
    tensorContract_mul_left _ _ freeAntipode_mul,
    tensorContract_derivation_mul_right _ _ freeDegree_mul,
    freeAntipode_generator, freeDegree_generator]
  rfl

theorem freeAntipodeConvolution_eq_augmentation (p : FreeAlgebra ℚ X) :
    freeAntipodeConvolution p = freeAugmentation p • 1 := by
  apply freeAlgebra_linear_induction (fun p =>
    freeAntipodeConvolution p = freeAugmentation p • 1)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq, add_smul]
  · intro r p hp
    simp only [map_smul, hp, smul_smul, smul_eq_mul]
  · intro w
    induction w using freeMonoid_induction_right with
    | h1 => simp
    | hstep w x hw =>
      rw [map_mul, freeWord_of, freeAntipodeConvolution_mul_generator, hw]
      simp

theorem freeDynkinConvolution_mem (p : FreeAlgebra ℚ X) :
    freeDynkinConvolution p ∈ freeAssociativeLieSubalgebra := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDynkinConvolution p ∈ freeAssociativeLieSubalgebra)
  · simpa only [map_zero] using freeAssociativeLieSubalgebra.zero_mem
  · intro p q hp hq
    simpa only [map_add] using freeAssociativeLieSubalgebra.add_mem hp hq
  · intro r p hp
    simpa only [map_smul] using freeAssociativeLieSubalgebra.smul_mem r hp
  · intro w
    induction w using freeMonoid_induction_right with
    | h1 => simp [freeAssociativeLieSubalgebra.zero_mem]
    | hstep w x hw =>
      rw [map_mul, freeWord_of, freeDynkinConvolution_mul_generator,
        freeAntipodeConvolution_eq_augmentation]
      have hbr := freeAssociativeLieSubalgebra.lie_mem hw
        (freeAssociativeLieSubalgebra_generator x)
      have hsm := freeAssociativeLieSubalgebra.smul_mem (freeAugmentation (freeWord w))
        (freeAssociativeLieSubalgebra_generator x)
      convert freeAssociativeLieSubalgebra.add_mem hbr hsm using 1
      change -FreeAlgebra.ι ℚ x * freeDynkinConvolution (freeWord w) +
          (freeDynkinConvolution (freeWord w) * FreeAlgebra.ι ℚ x +
            (freeAugmentation (freeWord w) • 1) * FreeAlgebra.ι ℚ x) =
        (freeDynkinConvolution (freeWord w) * FreeAlgebra.ι ℚ x -
          FreeAlgebra.ι ℚ x * freeDynkinConvolution (freeWord w)) +
            freeAugmentation (freeWord w) • FreeAlgebra.ι ℚ x
      rw [smul_mul_assoc, one_mul, neg_mul]
      abel

theorem FreePrimitive.dynkin_eq_degree {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) :
    freeDynkinConvolution p = freeDegree p := by
  change tensorContract freeAntipode freeDegree (freeCoproduct p) = _
  rw [hp, map_add]
  simp

theorem FreePrimitive.mem_of_degree {p : FreeAlgebra ℚ X} (hp : FreePrimitive p)
    {r : ℚ} (hr : r ≠ 0) (hd : freeDegree p = r • p) :
    p ∈ freeAssociativeLieSubalgebra := by
  have hm := freeDynkinConvolution_mem p
  rw [hp.dynkin_eq_degree, hd] at hm
  have h := freeAssociativeLieSubalgebra.smul_mem r⁻¹ hm
  simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using h

end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem freeAugmentation_antipode (p : FreeAlgebra ℚ X) :
    freeAugmentation (freeAntipode p) = freeAugmentation p := by
  apply freeAlgebra_linear_induction (fun p =>
    freeAugmentation (freeAntipode p) = freeAugmentation p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro r p hp
    simp only [map_smul, hp]
  · intro w
    induction w using freeMonoid_induction_right with
    | h1 => simp
    | hstep w x _ => simp [freeAntipode_mul]

theorem FreePrimitive.augmentation_eq_zero {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) :
    freeAugmentation p = 0 := by
  have hc : freeAntipode p + p = freeAugmentation p • 1 := by
    rw [← freeAntipodeConvolution_eq_augmentation]
    change _ = tensorContract freeAntipode LinearMap.id (freeCoproduct p)
    rw [hp, map_add]
    simp
  have h := congrArg freeAugmentation hc
  simp only [map_add, freeAugmentation_antipode, map_smul, map_one, smul_eq_mul, mul_one] at h
  linarith

noncomputable def freeDegreeInverse : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  freeWordLinearMap (fun w => (w.length : ℚ)⁻¹ • freeWord w)

@[simp] theorem freeDegreeInverse_word (w : FreeMonoid X) :
    freeDegreeInverse (freeWord w) = (w.length : ℚ)⁻¹ • freeWord w :=
  freeWordLinearMap_word _ _

theorem freeAugmentation_word_of_ne_one {w : FreeMonoid X} (hw : w ≠ 1) :
    freeAugmentation (freeWord w) = 0 := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact (hw rfl).elim
  | of_mul x w _ => simp

theorem freeDegreeInverse_degree (p : FreeAlgebra ℚ X) :
    freeDegreeInverse (freeDegree p) = p - freeAugmentation p • 1 := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDegreeInverse (freeDegree p) = p - freeAugmentation p • 1)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq, add_smul]
    abel
  · intro r p hp
    simp only [map_smul, hp, smul_sub, smul_smul, smul_eq_mul]
  · intro w
    by_cases hw : w = 1
    · subst w
      simp
    · rw [freeDegree_word, map_smul, freeDegreeInverse_word, smul_smul,
        mul_inv_cancel₀ (show (w.length : ℚ) ≠ 0 by
          exact_mod_cast (FreeMonoid.length_eq_zero.not.mpr hw)), one_smul,
        freeAugmentation_word_of_ne_one hw, zero_smul, sub_zero]

theorem freeDegree_lieTree (t : FreeMagma X) :
    freeDegree (lieTreeEval (FreeAlgebra.ι ℚ) t) =
      (t.length : ℚ) • lieTreeEval (FreeAlgebra.ι ℚ) t := by
  induction t using FreeMagma.rec with
  | of x => simp [lieTreeEval]
  | mul u v hu hv =>
    change freeDegree (lieTreeEval (FreeAlgebra.ι ℚ) u * lieTreeEval (FreeAlgebra.ι ℚ) v -
        lieTreeEval (FreeAlgebra.ι ℚ) v * lieTreeEval (FreeAlgebra.ι ℚ) u) = _
    rw [map_sub, freeDegree_mul, freeDegree_mul, hu, hv]
    change _ = ((u.length + v.length : ℕ) : ℚ) •
      (lieTreeEval (FreeAlgebra.ι ℚ) u * lieTreeEval (FreeAlgebra.ι ℚ) v -
        lieTreeEval (FreeAlgebra.ι ℚ) v * lieTreeEval (FreeAlgebra.ι ℚ) u)
    simp only [Nat.cast_add, add_smul, smul_sub, smul_mul_assoc, mul_smul_comm]
    abel

theorem freePrimitive_lieTree (t : FreeMagma X) :
    FreePrimitive (lieTreeEval (FreeAlgebra.ι ℚ) t) := by
  induction t using FreeMagma.rec with
  | of x => exact freePrimitive_generator x
  | mul u v hu hv => exact hu.commutator hv

theorem freeDegreeInverse_lieTree (t : FreeMagma X) :
    freeDegreeInverse (lieTreeEval (FreeAlgebra.ι ℚ) t) =
      (t.length : ℚ)⁻¹ • lieTreeEval (FreeAlgebra.ι ℚ) t := by
  have h := freeDegreeInverse_degree (lieTreeEval (FreeAlgebra.ι ℚ) t)
  rw [freeDegree_lieTree, map_smul, (freePrimitive_lieTree t).augmentation_eq_zero,
    zero_smul, sub_zero] at h
  have hlen : (t.length : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt t.length_pos)
  have hs := congrArg (fun z : FreeAlgebra ℚ X => (t.length : ℚ)⁻¹ • z) h
  simpa only [smul_smul, inv_mul_cancel₀ hlen, one_smul] using hs

theorem freeDegreeInverse_mem {p : FreeAlgebra ℚ X} (hp : p ∈ freeAssociativeLieSubalgebra) :
    freeDegreeInverse p ∈ freeAssociativeLieSubalgebra := by
  obtain ⟨l, rfl⟩ := hp
  apply freeLie_linear_induction (fun l =>
    freeDegreeInverse (freeLieAssociativeExpansion l) ∈ freeAssociativeLieSubalgebra)
  · simpa only [map_zero] using freeAssociativeLieSubalgebra.zero_mem
  · intro l m hl hm
    simpa only [map_add] using freeAssociativeLieSubalgebra.add_mem hl hm
  · intro r l hl
    simpa only [map_smul] using freeAssociativeLieSubalgebra.smul_mem r hl
  · intro t
    change freeDegreeInverse (FreeLieAlgebra.lift ℚ (FreeAlgebra.ι ℚ)
      (lieTreeEval (FreeLieAlgebra.of ℚ) t)) ∈ _
    rw [lift_lieTreeEval, freeDegreeInverse_lieTree]
    apply freeAssociativeLieSubalgebra.smul_mem
    exact ⟨lieTreeEval (FreeLieAlgebra.of ℚ) t, lift_lieTreeEval _ _⟩

theorem FreePrimitive.mem {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) :
    p ∈ freeAssociativeLieSubalgebra := by
  have hm := freeDegreeInverse_mem (freeDynkinConvolution_mem p)
  rw [hp.dynkin_eq_degree, freeDegreeInverse_degree, hp.augmentation_eq_zero,
    zero_smul, sub_zero] at hm
  exact hm

theorem freePrimitive_of_mem {p : FreeAlgebra ℚ X} (hp : p ∈ freeAssociativeLieSubalgebra) :
    FreePrimitive p := by
  obtain ⟨l, rfl⟩ := hp
  apply freeLie_linear_induction (fun l => FreePrimitive (freeLieAssociativeExpansion l))
  · simp [FreePrimitive]
  · intro l m hl hm
    simpa only [map_add] using hl.add hm
  · intro r l hl
    simpa only [map_smul] using hl.smul r
  · intro t
    change FreePrimitive (FreeLieAlgebra.lift ℚ (FreeAlgebra.ι ℚ)
      (lieTreeEval (FreeLieAlgebra.of ℚ) t))
    rw [lift_lieTreeEval]
    exact freePrimitive_lieTree t

theorem freePrimitive_iff_mem (p : FreeAlgebra ℚ X) :
    FreePrimitive p ↔ p ∈ freeAssociativeLieSubalgebra :=
  ⟨FreePrimitive.mem, freePrimitive_of_mem⟩

end Erdos3

end

end OAI
