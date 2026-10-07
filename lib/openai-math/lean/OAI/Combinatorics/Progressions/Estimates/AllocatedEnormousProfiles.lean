import OAI.Combinatorics.Progressions.Estimates.AllocatedShortDependence
import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialAffineLaw
import OAI.Combinatorics.Progressions.Polynomial.MonomialCoefficientControl
import OAI.Combinatorics.Progressions.Probability.ContainedProgressionCubeLaw
import OAI.Combinatorics.Progressions.Probability.PrincipalMixedMassBound

namespace OAI

section

namespace Erdos3

theorem canonicalPrincipal_normalization {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (extra : G → Option α → Z) (zi : Z → ℤ) (zr : Z → ℝ) (T : G → ℝ)
    (hfixed : ∀ g a, (zi (extra g a) : ℝ)/T g = zr (extra g a))
    (L : PrincipalTupleIndex B h → ℕ) (y : PrincipalIntegerTuples B h α L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    ((Sum.elim zi (principalTupleIntegers y) (canonicalTupleInput extra k a) : ℤ) : ℝ) /
        Sum.elim T (fun j => (L j : ℝ)) k =
      Sum.elim zr (principalTupleNormalized L y) (canonicalTupleInput extra k a) := by
  cases k with
  | inl g => exact hfixed g a
  | inr j =>
    rcases j with ⟨d, b, v⟩
    rfl

theorem canonicalFrozenPrincipal_normalization {D G α : Type*} {B : D → Type*} {h : D → ℕ}
    (zi : G × Option α → ℤ) (T : G → ℝ)
    (L : PrincipalTupleIndex B h → ℕ) (y : PrincipalIntegerTuples B h α L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    ((Sum.elim zi (principalTupleIntegers y) (canonicalTupleInput (fun g a => (g,a)) k a) : ℤ) : ℝ) /
        Sum.elim T (fun j => (L j : ℝ)) k =
      Sum.elim (fun z => (zi z : ℝ)/T z.1) (principalTupleNormalized L y)
        (canonicalTupleInput (fun g a => (g,a)) k a) :=
  canonicalPrincipal_normalization (fun g a => (g,a)) zi (fun z => (zi z : ℝ)/T z.1) T
    (fun _ _ => rfl) L y k a

theorem principalTupleResidues_has_lift {D α : Type*} {B : D → Type*} {h : D → ℕ}
    (m : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod m) :
    ∃ ref : JointBlockParameter B h α → ℤ, integerResidueMap _ m ref = principalTupleResidues r :=
  integerResidueMap_surjective _ m (principalTupleResidues r)

end Erdos3

end

section

namespace Erdos3

theorem principalTupleNormalized_norm_le {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (y : PrincipalIntegerTuples B h α L) : ‖principalTupleNormalized L y‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro a
  exact (norm_le_pi_norm (fun i => (y ⟨a.1, a.2.1, a.2.2.1⟩ i : ℝ)/L ⟨a.1, a.2.1, a.2.2.1⟩) a.2.2.2).trans
    (integerScalarCubeBox_normalized_norm_le (hL _) (y _))

theorem mappedPrincipal_normalized_bound {Z K D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1) (T : K → ℝ)
    (y : PrincipalIntegerTuples B h α L)
    (hn : ∀ k a, ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
      Sum.elim zr (principalTupleNormalized L y) (input k a)) :
    ∀ k a, |((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k| ≤ 1 := by
  intro k a
  rw [hn]
  cases input k a with
  | inl j => exact hz j
  | inr j =>
    exact (norm_le_pi_norm (principalTupleNormalized L y) j).trans
      (principalTupleNormalized_norm_le B h L hL y)

theorem goodScalarKernelTuple_mapped_control {α K O N V Z X : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    {ℓ B : ℕ} {κ : ℝ} (hℓ : 0 < ℓ) (selection : α → K) (hκ : 0 < κ)
    (x : K → IntegerScalarCubeBox α ℓ) (hx : GoodScalarKernelTuple selection κ B x)
    (degree : ℕ) (rows : O → Finset α) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ degree) :
    ∃ s : O ↪ BoundedIntegerExponent K degree, ∀ H : ℝ, 0 < H →
      ∀ (e : N → V →₀ ℕ) (input : V → Option α → Z ⊕ X) (z : Z → ℤ) (y : X → ℤ) (T : V → ℝ),
      (∀ v, 0 < T v) → (∀ v, T v ≤ (ℓ : ℝ)) →
      (∀ n, (e n).sum (fun _ d => d) ≤ degree) →
      (∀ v a, |((Sum.elim z y (input v a) : ℤ) : ℝ)/T v| ≤ 1) →
      CoefficientFiberControl
        (Matrix.fromCols (scalarKernelIntegerJet x degree rows) (integerMappedJetMatrix e input z rows y))
        (s.trans Function.Embedding.inl)
        (Sum.elim (kernelJetCoefficientScale K degree ℓ H) (fun n => H/monomialScale T (e n)))
        H ℓ degree (kernelJetEntryAllowance (Fintype.card α) degree)
        (kernelJetInverseAllowance (Fintype.card α) (Fintype.card K) (Fintype.card O) degree κ)
        (((B^degree)^Fintype.card O : ℕ) : ℝ) := by
  obtain ⟨s, hs⟩ := goodScalarKernelTuple_monomial_control (N := N) (V := V)
    hℓ selection hκ x hx degree rows hr hrows
  refine ⟨s, fun H hH e input z y T hT hTℓ he hn => ?_⟩
  exact hs H hH (fun v => Sum.elim z y (input v none))
    (fun i v => Sum.elim z y (input v (some i))) e T hT hTℓ he
    (fun v => hn v none) (fun i v => hn v (some i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.scaled_condition_complexMean {X : Type*}
    [Fintype X] [DecidableEq X] (p : FiniteProbabilityWeights X) (G : Finset X)
    (hG : 0 < p.mass G) (f : X → ℂ) :
    (p.mass G : ℂ) * (p.condition G hG).complexMean f =
      p.complexMean (fun x => if x ∈ G then f x else 0) := by
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hM : (p.mass G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  by_cases hx : x ∈ G
  · simp only [FiniteProbabilityWeights.condition, hx, ite_true, Complex.ofReal_div]
    field_simp
  · simp [FiniteProbabilityWeights.condition, hx]

theorem FiniteProbabilityWeights.complexMean_disintegrate {X R : Type*}
    [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R)
    (hp : ∀ r, 0 < p.mass (Finset.univ.filter (fun x => F x = r))) (f : R → X → ℂ) :
    p.complexMean (fun x => f (F x) x) =
      (p.fiberLaw F).complexMean (fun r =>
        (p.condition (Finset.univ.filter (fun x => F x = r)) (hp r)).complexMean (f r)) := by
  change _ = ∑ r, ((p.fiberLaw F).weight r : ℂ) * _
  simp_rw [p.fiberLaw_weight_eq_mass, p.scaled_condition_complexMean]
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  simp

theorem principalTuple_complex_disintegrate {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (f : (PrincipalTupleIndex B h → Option α → ZMod m) → PrincipalIntegerTuples B h α L → ℂ) :
    (principalTupleWeights (α := α) B h L hL).complexMean (fun y => f (principalResidueLabel m y) y) =
      ((principalTupleWeights (α := α) B h L hL).fiberLaw (principalResidueLabel m)).complexMean
        (fun r => (principalResidueWeights B h L hL m hm r hsize).complexMean (f r)) := by
  classical
  simpa only [principalResidueWeights_eq_condition] using
    (principalTupleWeights (α := α) B h L hL).complexMean_disintegrate
      (principalResidueLabel m) (fun r => principalResidueCell_mass_pos B h L hL m hm r hsize) f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

def principalAxisLength (P : D → Prop) (L : PrincipalTupleIndex B h → ℕ) :
    PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val) → ℕ :=
  fun j => L ⟨j.1.val, j.2⟩

abbrev PrincipalAxisTuples (P : D → Prop) (L : PrincipalTupleIndex B h → ℕ) :=
  PrincipalIntegerTuples (fun d : {d // P d} => B d.val) (fun d => h d.val) α
    (principalAxisLength P L)

def principalAxisRestrict (P : D → Prop) {L : PrincipalTupleIndex B h → ℕ}
    (y : PrincipalIntegerTuples B h α L) : PrincipalAxisTuples (α := α) P L :=
  fun j => y ⟨j.1.val, j.2⟩

def principalAxisJoin (P : D → Prop) [DecidablePred P] {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    PrincipalIntegerTuples B h α L :=
  fun j => if hp : P j.1 then u ⟨⟨j.1, hp⟩, j.2⟩ else v ⟨⟨j.1, hp⟩, j.2⟩

theorem principalAxisRestrict_join_left (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    principalAxisRestrict P (principalAxisJoin P u v) = u := by
  funext j
  rcases j with ⟨⟨d, hd⟩, bv⟩
  simp only [principalAxisRestrict, principalAxisJoin, hd, ↓reduceDIte]

theorem principalAxisRestrict_join_right (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    principalAxisRestrict (fun d => ¬P d) (principalAxisJoin P u v) = v := by
  funext j
  rcases j with ⟨⟨d, hd⟩, bv⟩
  simp only [principalAxisRestrict, principalAxisJoin, hd, ↓reduceDIte]

theorem principalAxisJoin_restrict (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ} (y : PrincipalIntegerTuples B h α L) :
    principalAxisJoin P (principalAxisRestrict P y) (principalAxisRestrict (fun d => ¬P d) y) = y := by
  funext j
  simp only [principalAxisJoin, principalAxisRestrict]
  split <;> rfl

def principalAxisPartitionEquiv (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) :
    PrincipalIntegerTuples B h α L ≃
      PrincipalAxisTuples (α := α) P L × PrincipalAxisTuples (α := α) (fun d => ¬P d) L where
  toFun y := (principalAxisRestrict P y, principalAxisRestrict (fun d => ¬P d) y)
  invFun y := principalAxisJoin P y.1 y.2
  left_inv := principalAxisJoin_restrict P
  right_inv y := Prod.ext (principalAxisRestrict_join_left P y.1 y.2)
    (principalAxisRestrict_join_right P y.1 y.2)

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

theorem principalTupleWeights_partition_weight (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (y : PrincipalIntegerTuples B h α L) :
    (principalTupleWeights B h L hL).weight y =
      (principalTupleWeights (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun j => hL ⟨j.1.val, j.2⟩)).weight (principalAxisRestrict P y) *
      (principalTupleWeights (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (fun j => hL ⟨j.1.val, j.2⟩)).weight
          (principalAxisRestrict (fun d => ¬P d) y) := by
  simp only [principalTupleWeights, FiniteProbabilityWeights.pi, principalAxisRestrict,
    principalAxisLength, Fintype.prod_sigma]
  exact (Fintype.prod_subtype_mul_prod_subtype P
    (fun d => ∏ j : B d × Fin (h d),
      (integerScalarCubeWeights α (L ⟨d, j⟩) (hL ⟨d, j⟩)).weight (y ⟨d, j⟩))).symm

theorem principalTupleWeights_partition (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (f : PrincipalIntegerTuples B h α L → ℂ) :
    (principalTupleWeights B h L hL).complexMean f =
      (principalTupleWeights (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun j => hL ⟨j.1.val, j.2⟩)).complexMean (fun u =>
      (principalTupleWeights (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (fun j => hL ⟨j.1.val, j.2⟩)).complexMean
          (fun v => f (principalAxisJoin P u v))) := by
  let p := principalTupleWeights (α := α) (fun d : {d // P d} => B d.val) (fun d => h d.val)
    (principalAxisLength P L) (fun j => hL ⟨j.1.val, j.2⟩)
  let q := principalTupleWeights (α := α) (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
    (principalAxisLength (fun d => ¬P d) L) (fun j => hL ⟨j.1.val, j.2⟩)
  calc
    _ = ∑ z : PrincipalAxisTuples (α := α) P L × PrincipalAxisTuples (α := α) (fun d => ¬P d) L,
        ((p.weight z.1 * q.weight z.2 : ℝ) : ℂ) * f (principalAxisJoin P z.1 z.2) := by
      apply Fintype.sum_equiv (principalAxisPartitionEquiv P L)
      intro y
      simp only [principalAxisPartitionEquiv, Equiv.coe_fn_mk, principalAxisJoin_restrict]
      rw [principalTupleWeights_partition_weight P L hL y]
    _ = _ := by
      simp only [FiniteProbabilityWeights.complexMean, Fintype.sum_prod_type,
        Complex.ofReal_mul, Finset.mul_sum, mul_assoc, p, q]

theorem principalTupleWeights_partition_residues (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val),
      (Fintype.card α+1)*m ≤ principalAxisLength (fun d => ¬P d) L j)
    (f : PrincipalIntegerTuples B h α L → ℂ) :
    (principalTupleWeights B h L hL).complexMean f =
      (principalTupleWeights (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun j => hL ⟨j.1.val, j.2⟩)).complexMean (fun u =>
      ((principalTupleWeights (α := α) (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (fun j => hL ⟨j.1.val, j.2⟩)).fiberLaw
          (principalResidueLabel m)).complexMean (fun r =>
      (principalResidueWeights (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (fun j => hL ⟨j.1.val, j.2⟩) m hm r hsize).complexMean
          (fun v => f (principalAxisJoin P u v)))) := by
  rw [principalTupleWeights_partition P L hL f]
  congr 1
  funext u
  exact principalTuple_complex_disintegrate _ _ _ _ m hm hsize
    (fun _ v => f (principalAxisJoin P u v))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem principalResidue_positive_witness {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (r : PrincipalTupleIndex B h → Option α → ZMod m) :
    ∃ y : PrincipalIntegerTuples B h α L, principalResidueLabel m y = r ∧
      (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hz : (principalTupleWeights (α := α) B h L hL).mass
      (Finset.univ.filter (fun y => principalResidueLabel m y = r)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    exact hn y (Finset.mem_filter.mp hy).2
  have hp := principalResidueCell_mass_pos B h L hL m hm r hsize
  linarith

theorem principalRetained_test_comparison {D α V W : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (tv : Finset V) (tw : Finset W)
    (spatial : PrincipalIntegerTuples B h α L → PMF V)
    (site : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℂ)
    (c : PrincipalIntegerTuples B h α L → W → ℝ)
    (T : (PrincipalTupleIndex B h → Option α → ZMod m) → (W → ℂ) → ℂ)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hc : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 → ∀ w ∈ tw, 0 ≤ c y w)
    (hmass : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 → (∑ w ∈ tw, c y w) ≤ 1)
    (hspatial : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      ∀ v ∈ tv, ‖((spatial y v).toReal : ℂ) - site (principalResidueLabel m y) v‖ ≤ δ)
    (hcoeff : ∀ r ψ, (∀ w ∈ tw, ‖ψ w‖ ≤ 1) →
      ‖(principalResidueWeights B h L hL m hm r hsize).complexMean
        (fun y => ∑ w ∈ tw, (c y w : ℂ) * ψ w) - T r ψ‖ ≤ ε)
    (φ : V → W → ℂ) (hφ : ∀ v ∈ tv, ∀ w ∈ tw, ‖φ v w‖ ≤ 1) :
    let p := principalTupleWeights (α := α) B h L hL
    let q := p.fiberLaw (principalResidueLabel m)
    ‖p.complexMean (fun y => ∑ v ∈ tv, ((spatial y v).toReal : ℂ) *
        (∑ w ∈ tw, (c y w : ℂ) * φ v w)) -
      q.complexMean (fun r => ∑ v ∈ tv, site r v * T r (φ v))‖ ≤
      δ * tv.card + (1 + δ * tv.card) * ε := by
  dsimp only
  let p := principalTupleWeights (α := α) B h L hL
  let q := p.fiberLaw (principalResidueLabel m)
  let C := fun y v => ∑ w ∈ tw, (c y w : ℂ) * φ v w
  have hC (y) (hy : p.weight y ≠ 0) (v) (hv : v ∈ tv) : ‖C y v‖ ≤ 1 :=
    (norm_nonneg_finite_test_le_mass tw (c y) (φ v) (hc y hy) (hφ v hv)).trans (hmass y hy)
  have hsite (r) : (∑ v ∈ tv, ‖site r v‖) ≤ 1 + δ * tv.card := by
    obtain ⟨y, hyr, hy⟩ := principalResidue_positive_witness B h L hL m hm hsize r
    apply pmf_proxy_norm_mass (spatial y) tv (site r)
    intro v hv
    simpa only [hyr] using hspatial y hy v hv
  have hfirst : ‖p.complexMean (fun y => ∑ v ∈ tv, ((spatial y v).toReal : ℂ) * C y v) -
      p.complexMean (fun y => ∑ v ∈ tv, site (principalResidueLabel m y) v * C y v)‖ ≤ δ * tv.card := by
    apply (p.norm_complexMean_sub_le _ _ (fun _ => δ * tv.card) ?_).trans_eq (p.mean_const _)
    intro y hy
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _v ∈ tv, δ := by
        apply Finset.sum_le_sum
        intro v hv
        rw [← sub_mul, norm_mul]
        exact (mul_le_mul (hspatial y hy v hv) (hC y hy v hv) (norm_nonneg _) hδ).trans_eq (mul_one _)
      _ = δ * tv.card := by simp [mul_comm]
  have hmid : p.complexMean (fun y => ∑ v ∈ tv, site (principalResidueLabel m y) v * C y v) =
      q.complexMean (fun r => ∑ v ∈ tv, site r v *
        (principalResidueWeights B h L hL m hm r hsize).complexMean (fun y => C y v)) := by
    rw [principalTuple_complex_disintegrate B h L hL m hm hsize
      (fun r y => ∑ v ∈ tv, site r v * C y v)]
    simp_rw [FiniteProbabilityWeights.complexMean_finset_sum,
      FiniteProbabilityWeights.complexMean_mul_left]
    rfl
  have hsecond : ‖q.complexMean (fun r => ∑ v ∈ tv, site r v *
        (principalResidueWeights B h L hL m hm r hsize).complexMean (fun y => C y v)) -
      q.complexMean (fun r => ∑ v ∈ tv, site r v * T r (φ v))‖ ≤ (1 + δ * tv.card) * ε := by
    apply (q.norm_complexMean_sub_le _ _ (fun _ => (1 + δ * tv.card) * ε) ?_).trans_eq (q.mean_const _)
    intro r _
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ v ∈ tv, ‖site r v‖ * ε := by
        apply Finset.sum_le_sum
        intro v hv
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_left (hcoeff r (φ v) (hφ v hv)) (norm_nonneg _)
      _ = (∑ v ∈ tv, ‖site r v‖) * ε := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + δ * tv.card) * ε := mul_le_mul_of_nonneg_right (hsite r) hε
  rw [hmid] at hfirst
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfirst hsecond)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

theorem containedProgressionTupleMap_axisJoin (P : D → Prop) [DecidablePred P]
    (u : PrincipalAxisTuples (α := α) P H)
    (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) H) :
    containedProgressionTupleMap B h L H step c hL hsubset (principalAxisJoin P u v) =
      principalAxisJoin P
        (containedProgressionTupleMap (fun d : {d // P d} => B d.val) (fun d => h d.val)
          (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
          (fun j => c ⟨j.1.val, j.2⟩) (fun j => hL ⟨j.1.val, j.2⟩)
          (fun j => hsubset ⟨j.1.val, j.2⟩) u)
        (containedProgressionTupleMap (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
          (principalAxisLength (fun d => ¬P d) L)
          (principalAxisLength (fun d => ¬P d) H)
          (principalAxisLength (fun d => ¬P d) step)
          (fun j => c ⟨j.1.val, j.2⟩) (fun j => hL ⟨j.1.val, j.2⟩)
          (fun j => hsubset ⟨j.1.val, j.2⟩) v) := by
  funext j
  by_cases hp : P j.1 <;>
    simp only [containedProgressionTupleMap, principalAxisJoin, principalAxisLength,
      hp, ↓reduceDIte]

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

abbrev PrincipalAxisParameter (P : D → Prop) :=
  JointBlockParameter (fun d : {d // P d} => B d.val) (fun d => h d.val) α

def partitionedPrincipalInput (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) :
    SamplerTupleIndex G B h → Option α →
      (Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) ⊕
        PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d)
  | .inl g, a => .inl (.inl (extra g a))
  | .inr ⟨d, b, v⟩, a =>
      if hp : P d then .inl (.inr ⟨⟨d, hp⟩, b, v, a⟩) else .inr ⟨⟨d, hp⟩, b, v, a⟩

theorem partitionedPrincipalInput_value (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (z : Z → ℤ) {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    Sum.elim (Sum.elim z (principalTupleIntegers u)) (principalTupleIntegers v)
        (partitionedPrincipalInput P extra k a) =
      Sum.elim z (principalTupleIntegers (principalAxisJoin P u v)) (canonicalTupleInput extra k a) := by
  rcases k with g | ⟨d, b, r⟩
  · rfl
  · by_cases hp : P d <;>
      simp [partitionedPrincipalInput, canonicalTupleInput, principalTupleIntegers, principalAxisJoin, hp]

theorem partitionedPrincipalInput_cube (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (z : Z → ℤ) {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    integerMappedCubeTuple (partitionedPrincipalInput P extra)
        (Sum.elim z (principalTupleIntegers u)) (principalTupleIntegers v) =
      integerMappedCubeTuple (canonicalTupleInput extra) z (principalTupleIntegers (principalAxisJoin P u v)) := by
  unfold integerMappedCubeTuple
  congr 1
  · funext k
    exact partitionedPrincipalInput_value P extra z u v k none
  · funext a k
    exact partitionedPrincipalInput_value P extra z u v k (some a)

theorem partitionedPrincipalInput_normalized (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (zi : Z → ℤ) (zr : Z → ℝ) (T : G → ℝ)
    (hfixed : ∀ g a, (zi (extra g a) : ℝ)/T g = zr (extra g a))
    (L : PrincipalTupleIndex B h → ℕ)
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    ((Sum.elim (Sum.elim zi (principalTupleIntegers u)) (principalTupleIntegers v)
        (partitionedPrincipalInput P extra k a) : ℤ) : ℝ) /
        Sum.elim T (fun j => (L j : ℝ)) k =
      Sum.elim (Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u))
        (principalTupleNormalized (principalAxisLength (fun d => ¬P d) L) v)
        (partitionedPrincipalInput P extra k a) := by
  rcases k with g | ⟨d, b, r⟩
  · exact hfixed g a
  · by_cases hp : P d <;>
      simp [partitionedPrincipalInput, principalTupleNormalized, principalAxisLength, hp]

theorem partitionedPrincipalInput_frozen_bound [Fintype D] [∀ d, Fintype (B d)]
    [Fintype α] [DecidableEq α] (P : D → Prop) [DecidablePred P]
    (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (u : PrincipalAxisTuples (α := α) P L)
    (j : Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) :
    |Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u) j| ≤ 1 := by
  cases j with
  | inl j => exact hz j
  | inr j =>
    have hb : ‖principalTupleNormalized (principalAxisLength P L) u‖ ≤ 1 :=
      principalTupleNormalized_norm_le
        (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun k => hL ⟨k.1.val, k.2⟩) u
    exact (norm_le_pi_norm (principalTupleNormalized (principalAxisLength P L) u) j).trans hb

theorem partitionedPrincipalInput_frozen_cube (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    (z : Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P → ℤ)
    (x y : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℤ)
    (t : Finset α) (d : D) (hd : P d) (b : B d) (v : Fin (h d)) :
    integerMappedCubeTuple (partitionedPrincipalInput P extra) z x t (.inr ⟨d, b, v⟩) =
      integerMappedCubeTuple (partitionedPrincipalInput P extra) z y t (.inr ⟨d, b, v⟩) := by
  simp only [integerMappedCubeTuple, integerAffineCube, partitionedPrincipalInput, hd, ↓reduceDIte,
    Sum.elim_inl]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

def allocatedGridAxis (L : ℕ) : LayerSamplerAxis I n → Prop
  | ⟨_, .inl _⟩ => False
  | ⟨j, .inr i⟩ => basisAxisScale (basis j) i ≤ L^(layerTailDegree m+1)

noncomputable instance allocatedGridAxisDecidable (L : ℕ) :
    DecidablePred (allocatedGridAxis (I := I) U basis L) := Classical.decPred _

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedPrincipalSides : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ :=
  fun j => layerSamplerSides (G := G) B U basis R S.value (.inr j)

theorem allocatedPrincipalSides_pos (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    0 < allocatedPrincipalSides B U basis S j :=
  layerSamplerSides_pos B U basis R S.positive (.inr j)

theorem allocatedPrincipalSides_long (d : LayerSamplerAxis I n)
    (hd : ¬allocatedGridAxis U basis S.value d) (b : B d) (v : Fin (layerSamplerDegree I n d)) :
    allocatedPrincipalSides B U basis S ⟨d, b, v⟩ = S.value := by
  rcases d with ⟨j, d⟩
  cases d with
  | inl i => rfl
  | inr i =>
    change ¬basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1) at hd
    have hactive : S.value^(j.val+1) < basisAxisScale (basis j) i :=
      (Nat.pow_le_pow_right S.positive
        ((layerDegree_le_tailDegree j).trans (Nat.le_succ _))).trans_lt (Nat.lt_of_not_ge hd)
    simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
      layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
      integerAxisSideLength, hactive, ↓reduceIte]

local notation "gridAxes" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "degree" => layerSamplerDegree I n

theorem allocatedPrincipalSides_long_restricted
    (j : PrincipalTupleIndex (fun d : {d // ¬gridAxes d} => B d.val) (fun d => degree d.val)) :
    principalAxisLength (fun d => ¬gridAxes d) sides j = S.value :=
  allocatedPrincipalSides_long B U basis S j.1.val j.1.property j.2.1 j.2.2

section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem allocatedPrincipal_partition_residues (M : ℕ) [NeZero M] (hM : 0 < M)
    (hsize : (Fintype.card α+1)*M ≤ S.value)
    (f : PrincipalIntegerTuples B degree α sides → ℂ) :
    (principalTupleWeights B degree sides (allocatedPrincipalSides_pos B U basis S)).complexMean f =
      (principalTupleWeights (fun d : {d // gridAxes d} => B d.val) (fun d => degree d.val)
        (principalAxisLength gridAxes sides)
        (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)).complexMean (fun u =>
      ((principalTupleWeights (α := α) (fun d : {d // ¬gridAxes d} => B d.val) (fun d => degree d.val)
        (principalAxisLength (fun d => ¬gridAxes d) sides)
        (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)).fiberLaw
          (principalResidueLabel M)).complexMean (fun r =>
      (principalResidueWeights (fun d : {d // ¬gridAxes d} => B d.val) (fun d => degree d.val)
        (principalAxisLength (fun d => ¬gridAxes d) sides)
        (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩) M hM r
        (fun j => by rw [allocatedPrincipalSides_long_restricted B U basis S j]; exact hsize)).complexMean
          (fun v => f (principalAxisJoin gridAxes u v)))) := by
  exact principalTupleWeights_partition_residues gridAxes sides
    (allocatedPrincipalSides_pos B U basis S) M hM
    (fun j => by rw [allocatedPrincipalSides_long_restricted B U basis S j]; exact hsize) f

end Law

theorem allocatedGridAxis_jet_frozen
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (hgrid : gridAxes ⟨j, Sum.inr i⟩)
    (a : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {Z α O : Type*} [DecidableEq α] (extra : G → Option α → Z)
    (z : Z ⊕ PrincipalAxisParameter (B := B) (h := degree) (α := α) gridAxes → ℤ)
    (x y : PrincipalAxisParameter (B := B) (h := degree) (α := α) (fun d => ¬gridAxes d) → ℤ)
    (rows : O → Finset α) :
    integerMappedJetMatrix Subtype.val (partitionedPrincipalInput gridAxes extra) z rows x *ᵥ a =
      integerMappedJetMatrix Subtype.val (partitionedPrincipalInput gridAxes extra) z rows y *ᵥ a := by
  apply allocatedLayerInteger_moderateJet_congr B U basis hR hσ S j i hgrid
    a a ha ha rfl (fun _ => rfl)
    (integerMappedCubeTuple (partitionedPrincipalInput gridAxes extra) z x)
    (integerMappedCubeTuple (partitionedPrincipalInput gridAxes extra) z y) rows
  intro o t _ b v
  exact partitionedPrincipalInput_frozen_cube gridAxes extra z x y t ⟨j, Sum.inr i⟩ hgrid b v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem principalIntervalLength_mul_scale_bounds {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    2 * γ * K ≤ (principalIntervalLength K T γ : ℝ) * T ∧
      (principalIntervalLength K T γ : ℝ) * T ≤ 4 * γ * K := by
  have hb := principalIntervalLength_bounds hK hT hγ hlarge
  constructor
  · calc
      2 * γ * K = (2 * γ * (K / T)) * T := by field_simp
      _ ≤ (principalIntervalLength K T γ : ℝ) * T := mul_le_mul_of_nonneg_right hb.1 hT.le
  · calc
      (principalIntervalLength K T γ : ℝ) * T ≤ (4 * γ * (K / T)) * T :=
        mul_le_mul_of_nonneg_right hb.2 hT.le
      _ = 4 * γ * K := by field_simp

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalSides_active (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
    allocatedPrincipalSides B U basis S ⟨⟨j, Sum.inr i⟩, b, v⟩ = S.value := by
  simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
    layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
    integerAxisSideLength, hactive, ↓reduceIte]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

abbrev AllocatedFrozenCoefficients := ∀ a : {a // grid a}, CoefficientAxisRow vars a.val

abbrev AllocatedLongCoefficients := ∀ a : {a // ¬grid a}, CoefficientAxisRow vars a.val

noncomputable def allocatedCoefficientSplit :
    CoefficientSamplerArrays (K := vars) I n ≃ᵐ
      AllocatedFrozenCoefficients B U basis S × AllocatedLongCoefficients B U basis S :=
  coefficientAxisSplitEquiv vars I n grid

noncomputable def allocatedCoefficientAxisLaw :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientAxisRow vars a) :=
  coefficientAxisLaw (allocatedLayerCenters B U basis S) (allocatedLayerWidths B U basis S)
    (allocatedLayerIntegerPMFs B U basis hR hσ S)

noncomputable def allocatedFrozenCoefficientSource : Measure (AllocatedFrozenCoefficients B U basis S) :=
  Measure.pi (fun a => allocatedCoefficientAxisLaw B U basis hR hσ S a.val)

noncomputable def allocatedLongCoefficientSource : Measure (AllocatedLongCoefficients B U basis S) :=
  Measure.pi (fun a => allocatedCoefficientAxisLaw B U basis hR hσ S a.val)

theorem allocatedCoefficientAxisLaw_probability (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
  coefficientAxisLaw_probability _ _ _ (allocatedLayerWidths_pos B U basis hR hσ S) a

theorem allocatedFrozenCoefficientSource_probability :
    IsProbabilityMeasure (allocatedFrozenCoefficientSource B U basis hR hσ S) := by
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U basis hR hσ S
  exact Measure.pi.instIsProbabilityMeasure _

theorem allocatedLongCoefficientSource_probability :
    IsProbabilityMeasure (allocatedLongCoefficientSource B U basis hR hσ S) := by
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U basis hR hσ S
  exact Measure.pi.instIsProbabilityMeasure _

theorem allocatedCoefficientSplit_measurePreserving :
    MeasurePreserving (allocatedCoefficientSplit B U basis S)
      (allocatedCoefficientSource B U basis hR hσ S)
      ((allocatedFrozenCoefficientSource B U basis hR hσ S).prod
        (allocatedLongCoefficientSource B U basis hR hσ S)) :=
  coefficientAxisSplitEquiv_measurePreserving _ _ _
    (allocatedLayerWidths_pos B U basis hR hσ S) grid

theorem allocatedCoefficientReconstruct_measurePreserving :
    MeasurePreserving (allocatedCoefficientSplit B U basis S).symm
      ((allocatedFrozenCoefficientSource B U basis hR hσ S).prod
        (allocatedLongCoefficientSource B U basis hR hσ S))
      (allocatedCoefficientSource B U basis hR hσ S) :=
  (allocatedCoefficientSplit_measurePreserving B U basis hR hσ S).symm
    (allocatedCoefficientSplit B U basis S)

theorem allocatedCoefficientReconstruct_grid
    (u : AllocatedFrozenCoefficients B U basis S) (v : AllocatedLongCoefficients B U basis S)
    (j : Fin m) (i : Fin (n j)) (hi : grid ⟨j, Sum.inr i⟩) :
    ((allocatedCoefficientSplit B U basis S).symm (u, v) j).2 i = u ⟨⟨j, Sum.inr i⟩, hi⟩ :=
  coefficientAxisSplitEquiv_symm_left grid u v ⟨⟨j, Sum.inr i⟩, hi⟩

theorem allocatedCoefficientReconstruct_long
    (u : AllocatedFrozenCoefficients B U basis S) (v : AllocatedLongCoefficients B U basis S)
    (a : {a // ¬grid a}) :
    coefficientAxisEquiv vars I n ((allocatedCoefficientSplit B U basis S).symm (u, v)) a.val = v a :=
  coefficientAxisSplitEquiv_symm_right grid u v a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedIntegerProfileCenters (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileCenter (layerIntegerPrincipalSlots B j i)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)

noncomputable def allocatedIntegerProfileWidths (R σ : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileWidth (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (R j/4) (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedIntegerProfileScales (j : Fin m) (i : Fin (n j)) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  fun d => (basisAxisScale (basis j) i : ℝ)/monomialScale (layerSamplerBox B U basis S) d.val

theorem allocatedIntegerProfileScales_pos (j : Fin m) (i : Fin (n j)) (d) :
    0 < allocatedIntegerProfileScales B U basis S j i d :=
  div_pos (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (monomialScale_pos _ (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v)) d.val)

include hR hσ in
theorem allocatedIntegerProfileWidths_pos (j : Fin m) (i : Fin (n j)) (d) :
    0 < allocatedIntegerProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num)) (principalProfileSize_pos (hR j) _)
    (tailProfileSize_pos (hR j) (hσ j) _) d

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

include henormous in
theorem allocatedEnormous_active : S.value^(j.val+1) < basisAxisScale (basis j) i :=
  (Nat.pow_le_pow_right S.positive ((layerDegree_le_tailDegree j).trans (Nat.le_succ _))).trans_lt henormous

include henormous in
theorem allocatedEnormous_principalScale (d) (hd : d ∈ layerIntegerPrincipalSlots (G := G) B j i) :
    monomialScale (layerSamplerBox B U basis S) d.val = (S.value : ℝ)^(j.val+1) := by
  rw [show monomialScale (layerSamplerBox B U basis S) d.val =
      (integerAxisSideLength (j.val+1) (basisAxisScale (basis j) i) S.value
        (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) : ℝ)^(j.val+1) from
      layerSamplerSides_integer_principal B U basis R S.value j i d hd]
  simp only [integerAxisSideLength, allocatedEnormous_active B U basis S j i henormous, ↓reduceIte]

include hR hσ1 henormous in
theorem allocatedEnormous_constant_width :
    8*(probabilityProfileLipschitz : ℝ) ≤ (R j/4)*(basisAxisScale (basis j) i : ℝ) := by
  have ht : tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))) ≤ R j/4 := by
    unfold tailProfileSize
    apply (div_le_iff₀ (by positivity)).mpr
    have hn := Nat.cast_nonneg (α := ℝ)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
    have hp := mul_nonneg (hR j).le hn
    nlinarith [mul_le_mul_of_nonneg_right hσ1 (hR j).le]
  have hLK : (S.value : ℝ) ≤ basisAxisScale (basis j) i := by
    have hpow : S.value ≤ S.value^(layerTailDegree m+1) := by
      calc
        _ = S.value^1 := by simp
        _ ≤ _ := Nat.pow_le_pow_right S.positive (by omega)
    exact_mod_cast hpow.trans henormous.le
  exact (S.width j).trans (mul_le_mul ht hLK (Nat.cast_nonneg _)
    (div_pos (hR j) (by norm_num)).le)

include hR hσ hσ1 henormous in
theorem allocatedEnormous_profile_width_large (d) :
    8*(probabilityProfileLipschitz : ℝ) ≤
      allocatedIntegerProfileWidths (G := G) B R σ j i d * allocatedIntegerProfileScales B U basis S j i d := by
  exact integerPolynomialProfile_width_large
    (P := layerIntegerPrincipalSlots B j i) (j₀ := constantCoefficientSlot _ _)
    (h := j.val+1) (K := basisAxisScale (basis j) i) (L := S.value) (s := layerTailDegree m)
    (hh := Nat.zero_lt_succ _) (hL := S.positive)
    (T := layerSamplerBox B U basis S)
    (hT := fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (hTL := layerSamplerBox_le B U basis S) (e := Subtype.val)
    (he := fun d => d.property.trans (layerDegree_le_tailDegree j))
    (ρ := R j/4) (γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (ε := tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))
    (hγ := principalProfileSize_pos (hR j) _) (hε := tailProfileSize_pos (hR j) (hσ j) _)
    (hgap := S.gap j i) (hεL := S.width j)
    (ha := allocatedEnormous_active B U basis S j i henormous) (henormous := henormous)
    (hconst := allocatedEnormous_constant_width B U basis hR S j i hσ1 henormous)
    (he₀ := rfl) (hprincipal := allocatedEnormous_principalScale B U basis S j i henormous) d

include hR hσ hσ1 in
theorem allocatedIntegerProfile_support :
    ∀ x, R j < ‖x‖ → affineProductProfile (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths B R σ j i) x = 0 := by
  apply affineProductProfile_zero_outside _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i) (hR j).le
  intro d
  exact (allocatedProfile_term_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerIntegerPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

include hR hσ hσ1 henormous in
theorem allocatedEnormous_profile_sum_pos :
    0 < coefficientWeightSum (affineProductProfile (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths B R σ j i)) (allocatedIntegerProfileScales B U basis S j i) :=
  affineProductProfile_sample_sum_pos _ _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i)
    (allocatedIntegerProfileScales_pos B U basis S j i)
    (allocatedEnormous_profile_width_large B U basis hR hσ S j i hσ1 henormous)

include hR hσ in
theorem allocatedIntegerProfile_normalizer :
    coefficientWeightSum (affineProductProfile (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths B R σ j i)) (allocatedIntegerProfileScales B U basis S j i) =
      profileWidthFactor (allocatedIntegerProfileWidths (G := G) B R σ j i) *
        ∏ d, shiftedSmoothSampleSum
          (allocatedIntegerProfileCenters B R j i d * allocatedIntegerProfileScales B U basis S j i d)
          (allocatedIntegerProfileWidths B R σ j i d * allocatedIntegerProfileScales B U basis S j i d) :=
  affineProductProfile_sample_sum _ _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i)
    (allocatedIntegerProfileScales_pos B U basis S j i)

noncomputable def allocatedEnormousProfilePMF :
    PMF (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ) :=
  coefficientPMF (affineProductProfile (allocatedIntegerProfileCenters B R j i)
    (allocatedIntegerProfileWidths B R σ j i))
    (affineProductProfile_nonneg _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i))
    (allocatedIntegerProfileScales B U basis S j i) (allocatedIntegerProfileScales_pos B U basis S j i)
    (allocatedIntegerProfile_support B hR hσ j i hσ1)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)

theorem allocatedEnormous_coefficient_law :
    allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩ =
      (allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous).toMeasure := by
  exact integerPolynomial_affineMeasure
    (P := layerIntegerPrincipalSlots B j i) (j₀ := constantCoefficientSlot _ _)
    (h := j.val+1) (K := basisAxisScale (basis j) i) (L := S.value) (s := layerTailDegree m)
    (hh := Nat.zero_lt_succ _) (hK := basisAxisScale_pos (basis j) i) (hL := S.positive)
    (T := layerSamplerBox B U basis S)
    (hT := fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (hTL := layerSamplerBox_le B U basis S) (e := Subtype.val)
    (he := fun d => d.property.trans (layerDegree_le_tailDegree j))
    (ρ := R j/4) (γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (ε := tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))
    (hρ := div_pos (hR j) (by norm_num)) (hγ := principalProfileSize_pos (hR j) _)
    (hε := tailProfileSize_pos (hR j) (hσ j) _)
    (hgap := S.gap j i) (hεL := S.width j)
    (ha := allocatedEnormous_active B U basis S j i henormous) (henormous := henormous)
    (hj₀ := layerIntegerPrincipalSlots_not_constant B j i) (he₀ := rfl)
    (hprincipal := allocatedEnormous_principalScale B U basis S j i henormous)
    (hwidth := allocatedEnormous_profile_width_large B U basis hR hσ S j i hσ1 henormous)
    (hsupport := allocatedIntegerProfile_support B hR hσ j i hσ1)
    (hZ := allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)

theorem allocatedEnormous_image_law {O : Type*} [Fintype O]
    (A : Matrix O (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) ℤ) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩).map (fun a => A *ᵥ a) =
      (coefficientImagePMF A (affineProductProfile (allocatedIntegerProfileCenters B R j i)
        (allocatedIntegerProfileWidths B R σ j i))
        (affineProductProfile_nonneg _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i))
        (allocatedIntegerProfileScales B U basis S j i) (allocatedIntegerProfileScales_pos B U basis S j i)
        (allocatedIntegerProfile_support B hR hσ j i hσ1)
        (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)).toMeasure := by
  rw [allocatedEnormous_coefficient_law B U basis hR hσ S j i hσ1 henormous]
  have hlaw := PMF.toMeasure_map
    (fun a : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ => A *ᵥ a)
    (allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous) (measurable_of_countable _)
  exact hlaw

end Erdos3.VectorPolynomial

end

end OAI
