/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Linear.DualAdjointFiltration

namespace OAI

section

namespace Erdos3

namespace NilpotentAlgebraFiltration

variable {A : Type*} [Ring A] [Algebra ℚ A] (F : NilpotentAlgebraFiltration A 2)

theorem mul_eq_zero_of_degrees {i j : ℕ} {a b : A}
    (ha : a ∈ F.layer i) (hb : b ∈ F.layer j) (hij : 3 ≤ i + j) : a * b = 0 := by
  have h := F.antitone hij (F.mul_mem ha hb)
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem exp_eq_quadratic {a : A} (ha : a ∈ F.layer 1) :
    IsNilpotent.exp a = 1 + a + (1 / 2 : ℚ) • a ^ 2 := by
  rw [IsNilpotent.exp_eq_sum (F.pow_eq_zero le_rfl ha)]
  norm_num [Finset.sum_range_succ]

theorem nilpotentBCH_eq_quadratic {a b : A} (ha : a ∈ F.layer 1)
    (hb : b ∈ F.layer 1) :
    nilpotentBCH a b = a + b + (1 / 2 : ℚ) • (a * b - b * a) := by
  have ha2 : a ^ 2 ∈ F.layer 2 := by simpa using F.pow_mem ha 2
  have hb2 : b ^ 2 ∈ F.layer 2 := by simpa using F.pow_mem hb 2
  have hab2 := F.mul_eq_zero_of_degrees ha hb2 (by decide)
  have ha2b := F.mul_eq_zero_of_degrees ha2 hb (by decide)
  have ha2b2 := F.mul_eq_zero_of_degrees ha2 hb2 (by decide)
  let q := (1 / 2 : ℚ) • a ^ 2 + a * b + (1 / 2 : ℚ) • b ^ 2
  have hq : q ∈ F.layer 2 :=
    (F.layer 2).add_mem ((F.layer 2).add_mem ((F.layer 2).smul_mem _ ha2)
      (F.mul_mem ha hb)) ((F.layer 2).smul_mem _ hb2)
  have hab : a + b ∈ F.layer 1 := (F.layer 1).add_mem ha hb
  have hp : IsNilpotent.exp a * IsNilpotent.exp b - 1 = a + b + q := by
    rw [F.exp_eq_quadratic ha, F.exp_eq_quadratic hb]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      hab2, ha2b, ha2b2, smul_zero]
    dsimp [q]
    module
  have hq1 : q ∈ F.layer 1 := F.antitone (by decide) hq
  have hp2 : (a + b + q) ^ 2 = (a + b) ^ 2 := by
    rw [pow_two, add_mul (a + b) q (a + b + q),
      mul_add (a + b) (a + b) q, mul_add q (a + b) q,
      F.mul_eq_zero_of_degrees hab hq (by decide),
      F.mul_eq_zero_of_degrees hq hab (by decide),
      F.mul_eq_zero_of_degrees hq hq (by decide)]
    simp only [add_zero, pow_two]
  rw [nilpotentBCH, hp,
    nilpotentLog_eq_sum (F.pow_eq_zero le_rfl ((F.layer 1).add_mem hab hq1))]
  norm_num [Finset.sum_range_succ, hp2]
  dsimp [q]
  simp only [pow_two, add_mul, mul_add, smul_add, smul_sub]
  module

end NilpotentAlgebraFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
attribute [local instance] LieRing.ofAssociativeRing

theorem lieBCH_eq_quadratic_of_step_two {s : ℕ} (hs : 2 ≤ s)
    (hnil : LieModule.lowerCentralSeries ℚ L L 2 = ⊥) (a b : L) :
    lieBCH s a b = a + b + (1 / 2 : ℚ) • ⁅a, b⁆ := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) 2
  have hx (i : Fin 2) : scaledFreeGenerator 2 i ∈ F.layer 1 :=
    scaledFreeGenerator_mem_layer 2 i
  have h : scaledFreeLieEval 2 (lieBCH s (x 0) (x 1)) =
      scaledFreeLieEval 2 (x 0 + x 1 + (1 / 2 : ℚ) • ⁅x 0, x 1⁆) := by
    simp only [map_lieBCH, map_add, map_smul, LieHom.map_lie, x, scaledFreeLieEval_of]
    rw [(F.extend hs).lieBCH_eq (hx 0) (hx 1)]
    exact F.nilpotentBCH_eq_quadratic (hx 0) (hx 1)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hnil h
  simpa only [map_lieBCH, map_add, map_smul, LieHom.map_lie, x,
    FreeLieAlgebra.lift_of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using he

end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def centralPairSpan (a b : L) : Submodule ℚ L :=
  Submodule.span ℚ {a, b, ⁅a, b⁆}

theorem centralPairSpan_lie_mem (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) {x y : L}
    (hx : x ∈ centralPairSpan a b) (hy : y ∈ centralPairSpan a b) :
    ⁅x, y⁆ ∈ Submodule.span ℚ {⁅a, b⁆} := by
  let W := Submodule.span ℚ {⁅a, b⁆}
  have hc : ⁅a, b⁆ ∈ W := Submodule.subset_span (by simp)
  have hba : ⁅b, a⁆ = -⁅a, b⁆ := (lie_skew b a).symm
  have hca : ⁅⁅a, b⁆, a⁆ = 0 := by rw [← lie_skew ⁅a, b⁆ a, ha, neg_zero]
  have hcb : ⁅⁅a, b⁆, b⁆ = 0 := by rw [← lie_skew ⁅a, b⁆ b, hb, neg_zero]
  change x ∈ Submodule.span ℚ {a, b, ⁅a, b⁆} at hx
  change y ∈ Submodule.span ℚ {a, b, ⁅a, b⁆} at hy
  change ⁅x, y⁆ ∈ W
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        try simp only [lie_self, ha, hb, hba, hca, hcb]
      all_goals first | exact W.zero_mem | exact hc | exact W.neg_mem hc
    | zero => simpa only [lie_zero] using W.zero_mem
    | add y z _ _ hy hz => simpa only [lie_add] using W.add_mem hy hz
    | smul r y _ hy => simpa only [lie_smul] using W.smul_mem r hy
  | zero => simpa only [zero_lie] using W.zero_mem
  | add x z _ _ hx hz => simpa only [add_lie] using W.add_mem (hx hy) (hz hy)
  | smul r x _ hx => simpa only [smul_lie] using W.smul_mem r (hx hy)

theorem centralPairSpan_lie_eq_zero (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) {x y : L}
    (hx : x ∈ centralPairSpan a b) (hy : y ∈ Submodule.span ℚ {⁅a, b⁆}) :
    ⁅x, y⁆ = 0 := by
  have hc : ⁅x, ⁅a, b⁆⁆ = 0 := by
    change x ∈ Submodule.span ℚ {a, b, ⁅a, b⁆} at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact lie_self _
    | zero => exact zero_lie _
    | add x y _ _ hx hy => rw [add_lie, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_lie, hx, smul_zero]
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [lie_smul, hc, smul_zero]

def centralPairSubalgebra (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) : LieSubalgebra ℚ L :=
  { centralPairSpan a b with
    lie_mem' := fun hx hy =>
      (Submodule.span_mono (by simp)) (centralPairSpan_lie_mem a b ha hb hx hy) }

theorem centralPairSubalgebra_step_two (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) :
    let K := centralPairSubalgebra a b ha hb
    LieModule.lowerCentralSeries ℚ K K 2 = ⊥ := by
  intro K
  have hcenter : LieModule.lowerCentralSeries ℚ K K 1 ≤ LieAlgebra.center ℚ K := by
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
    intro x _ y _
    rw [LieModule.mem_maxTrivSubmodule]
    intro z
    apply Subtype.ext
    exact centralPairSpan_lie_eq_zero a b ha hb z.property
      (centralPairSpan_lie_mem a b ha hb x.property y.property)
  apply bot_unique
  rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
  intro x _ y hy
  exact (LieSubmodule.mem_bot _).mpr ((hcenter hy) x)

theorem lieBCH_eq_quadratic_of_central_commutator {s : ℕ} (hs : 2 ≤ s)
    (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0) (hb : ⁅b, ⁅a, b⁆⁆ = 0) :
    lieBCH s a b = a + b + (1 / 2 : ℚ) • ⁅a, b⁆ := by
  let K := centralPairSubalgebra a b ha hb
  have haK : a ∈ K := Submodule.subset_span (by simp)
  have hbK : b ∈ K := Submodule.subset_span (by simp)
  have h := congrArg K.incl (lieBCH_eq_quadratic_of_step_two hs
    (centralPairSubalgebra_step_two a b ha hb) (⟨a, haK⟩ : K) (⟨b, hbK⟩ : K))
  simp only [map_lieBCH, map_add, map_smul, LieHom.map_lie] at h
  exact h

theorem lieBCH_conjugation_of_central_commutator {s : ℕ} (hs : 2 ≤ s)
    (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0) (hb : ⁅b, ⁅a, b⁆⁆ = 0) :
    lieBCH s (lieBCH s a b) (-a) = b + ⁅a, b⁆ := by
  have hba : ⁅b, a⁆ = -⁅a, b⁆ := (lie_skew b a).symm
  have hca : ⁅⁅a, b⁆, a⁆ = 0 := by rw [← lie_skew ⁅a, b⁆ a, ha, neg_zero]
  have hc : ⁅a + b + (1 / 2 : ℚ) • ⁅a, b⁆, -a⁆ = ⁅a, b⁆ := by
    simp only [add_lie, lie_neg, lie_self, smul_lie, hca,
      smul_zero, hba, neg_neg, zero_add, add_zero]
  have hu : ⁅a + b + (1 / 2 : ℚ) • ⁅a, b⁆, ⁅a, b⁆⁆ = 0 := by
    simp only [add_lie, ha, hb, smul_lie, lie_self, smul_zero, add_zero]
  rw [lieBCH_eq_quadratic_of_central_commutator hs a b ha hb,
    lieBCH_eq_quadratic_of_central_commutator hs _ _
      (by rw [hc, hu]) (by rw [hc, neg_lie, ha, neg_zero]), hc]
  module

theorem lieBCH_conjugation_sub_mem {s : ℕ} (hs : 2 ≤ s) (I : LieIdeal ℚ L)
    (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ ∈ I) (hb : ⁅b, ⁅a, b⁆⁆ ∈ I) :
    lieBCH s (lieBCH s a b) (-a) - (b + ⁅a, b⁆) ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_add, map_lieBCH, map_lieBCH, map_neg, LieHom.map_lie]
  apply sub_eq_zero.mpr
  apply lieBCH_conjugation_of_central_commutator hs
  · rw [← LieHom.map_lie, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr ha
  · rw [← LieHom.map_lie, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hb

end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualBaseSubalgebra (U : LieSubalgebra ℚ L) :
    LieSubalgebra ℚ (DualLieAlgebra L) :=
  dualInvariantSubalgebra U ⊤ (fun _ _ _ _ => trivial)

noncomputable def dualInvariantTangentIdeal (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) : LieIdeal ℚ (dualBaseSubalgebra U) :=
  { (dualBaseLinear.comp (dualBaseSubalgebra U).incl.toLinearMap).ker ⊓
      V.comap (dualTangentLinear.comp (dualBaseSubalgebra U).incl.toLinearMap) with
    lie_mem := by
      intro x y hy
      change dualBaseLinear ⁅x.val, y.val⁆ = 0 ∧ dualTangentLinear ⁅x.val, y.val⁆ ∈ V
      change dualBaseLinear y.val = 0 ∧ dualTangentLinear y.val ∈ V at hy
      simp only [dualBaseLinear_lie, dualTangentLinear_lie, hy.1, lie_zero, add_zero]
      exact ⟨trivial, hUV _ x.property.1 _ hy.2⟩ }

@[simp] theorem mem_dualInvariantTangentIdeal (U : LieSubalgebra ℚ L)
    (V : Submodule ℚ L) (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (z : dualBaseSubalgebra U) :
    z ∈ dualInvariantTangentIdeal U V hUV ↔
      dualBaseLinear z.val = 0 ∧ dualTangentLinear z.val ∈ V := Iff.rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_eq_add_lie (hs : 2 ≤ s)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hgx : ⁅g.coord, ⁅g.coord, x⁆⁆ = 0) :
    dualAdjoint g x = x + ⁅g.coord, x⁆ := by
  change dualTangentLinear
    (lieBCH s (lieBCH s (dualConstantLie g.coord) (dualInfinitesimal x))
      (-dualConstantLie g.coord)) = _
  rw [lieBCH_conjugation_of_central_commutator hs _ _
    (by rw [dualConstant_infinitesimal_lie, dualConstant_infinitesimal_lie, hgx, map_zero])
    (by rw [dualConstant_infinitesimal_lie, dualInfinitesimal_lie]),
    dualConstant_infinitesimal_lie, map_add, dualTangentLinear_infinitesimal,
    dualTangentLinear_infinitesimal]

theorem dualAdjoint_sub_first_bracket_mem (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : L)
    (hgx : ⁅g.coord, ⁅g.coord, x⁆⁆ ∈ V) :
    dualAdjoint g x - (x + ⁅g.coord, x⁆) ∈ V := by
  let S := dualBaseSubalgebra U
  let I := dualInvariantTangentIdeal U V hUV
  let a : S := ⟨dualConstantLie g.coord, by
    change dualBaseLinear (dualConstantLie g.coord) ∈ U ∧ _
    exact ⟨by simpa only [dualBaseLinear_constant] using hg, by trivial⟩⟩
  let b : S := ⟨dualInfinitesimal x, by
    change dualBaseLinear (dualInfinitesimal x) ∈ U ∧ _
    exact ⟨by simpa only [dualBaseLinear_infinitesimal] using U.zero_mem, by trivial⟩⟩
  have ha : ⁅a, ⁅a, b⁆⁆ ∈ I := by
    change dualBaseLinear ⁅dualConstantLie g.coord,
        ⁅dualConstantLie g.coord, dualInfinitesimal x⁆⁆ = 0 ∧
      dualTangentLinear ⁅dualConstantLie g.coord,
        ⁅dualConstantLie g.coord, dualInfinitesimal x⁆⁆ ∈ V
    rw [dualConstant_infinitesimal_lie, dualConstant_infinitesimal_lie,
      dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal]
    exact ⟨rfl, hgx⟩
  have hb : ⁅b, ⁅a, b⁆⁆ ∈ I := by
    have he : ⁅b, ⁅a, b⁆⁆ = 0 := by
      apply Subtype.ext
      change ⁅dualInfinitesimal x, ⁅dualConstantLie g.coord, dualInfinitesimal x⁆⁆ = 0
      rw [dualConstant_infinitesimal_lie, dualInfinitesimal_lie]
    rw [he]
    exact I.zero_mem
  have h := (lieBCH_conjugation_sub_mem hs I a b ha hb).2
  change dualTangentLinear (S.incl
    (lieBCH s (lieBCH s a b) (-a) - (b + ⁅a, b⁆))) ∈ V at h
  simp only [map_sub, map_add, map_lieBCH, map_neg, LieHom.map_lie] at h
  change dualTangentLinear
      (lieBCH s (lieBCH s (dualConstantLie g.coord) (dualInfinitesimal x))
        (-dualConstantLie g.coord)) -
    (dualTangentLinear (dualInfinitesimal x) +
      dualTangentLinear ⁅dualConstantLie g.coord, dualInfinitesimal x⁆) ∈ V at h
  simp only [dualConstant_infinitesimal_lie, dualTangentLinear_infinitesimal] at h
  exact h

theorem dualAdjoint_current_bracket_relation (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (r k p : L)
    (hr : ⁅g.coord, r - k⁆ ∈ V) (hp : ⁅g.coord - p, k⁆ ∈ V)
    (hk : ⁅g.coord, ⁅g.coord, k⁆⁆ ∈ V) :
    ⁅p, k⁆ - (dualAdjoint g r - r) ∈ V := by
  have hdouble : ⁅g.coord, ⁅g.coord, r⁆⁆ ∈ V := by
    have h := V.add_mem (hUV _ hg _ hr) hk
    simp only [lie_sub] at h
    simpa only [sub_add_cancel] using h
  have hmain := dualAdjoint_sub_first_bracket_mem hs U V hUV g hg r hdouble
  have hdelta : ⁅g.coord, r⁆ - ⁅p, k⁆ ∈ V := by
    have h := V.add_mem hr hp
    simp only [lie_sub, sub_lie] at h
    convert h using 1; abel
  convert V.neg_mem (V.add_mem hmain hdelta) using 1; abel

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dualAdjoint_sub_first_bracket_mem_layer (hs : 2 ≤ s) {i j : ℕ}
    (g : F.Group) (hg : g.coord ∈ F.layer i) (x : L) (hx : x ∈ F.layer j) :
    dualAdjoint g x - (x + ⁅g.coord, x⁆) ∈ F.layer (2 * i + j) := by
  apply dualAdjoint_sub_first_bracket_mem hs ⊤ (F.layerIdeal (2 * i + j)).toSubmodule
    (fun _ _ _ hv => (F.layerIdeal _).lie_mem hv) g (by trivial) x
  change ⁅g.coord, ⁅g.coord, x⁆⁆ ∈ F.layer (2 * i + j)
  simpa only [two_mul, Nat.add_assoc] using F.lie_mem hg (F.lie_mem hg hx)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def polynomialDualEval : VectorPolynomial Unit ℚ L →ₗ⁅ℚ⁆ DualLieAlgebra L where
  toLinearMap := (MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))).toLinearMap.rTensor L
  map_lie' {p q} := by
    let e : VectorPolynomial Unit ℚ L →ₗ[ℚ] DualLieAlgebra L :=
      (MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))).toLinearMap.rTensor L
    change e ⁅p, q⁆ = ⁅e p, e q⁆
    induction p using TensorProduct.inductionOn with
    | tmul a x =>
      induction q using TensorProduct.inductionOn with
      | tmul b y =>
        simp only [e, LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, map_mul]
      | add q q' hq hq' =>
        simp only [LieRing.lie_add, map_add, hq, hq']
        exact (LieRing.lie_add (e (a ⊗ₜ[ℚ] x)) (e q) (e q')).symm
    | add p p' hp hp' =>
      simp only [LieRing.add_lie, map_add, hp, hp']
      exact (LieRing.add_lie (e p) (e p') (e q)).symm

theorem polynomialDualEval_constant (x : L) :
    polynomialDualEval (monomial (0 : Unit →₀ ℕ) x) = dualConstantLie x := by
  change MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))
    (1 : MvPolynomial Unit ℚ) ⊗ₜ[ℚ] x = _
  rw [map_one]
  rfl

theorem polynomialDualEval_linear (x : L) :
    polynomialDualEval (monomial (Finsupp.single () 1) x) = dualInfinitesimal x := by
  change MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))
    (MvPolynomial.X ()) ⊗ₜ[ℚ] x = _
  rw [MvPolynomial.aeval_X]
  rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem conjugation_polynomial (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    lieBCH s (lieBCH s (monomial (R := ℚ) (0 : Unit →₀ ℕ) g.coord)
      (monomial (Finsupp.single () 1) x)) (-monomial 0 g.coord) =
        monomial (Finsupp.single () 1) (conjugationCoord g x) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero
  intro a
  simp only [map_sub, eval_lieBCH, map_neg, eval_monomial,
    Finsupp.prod_zero_index, one_smul, Finsupp.prod_single_index, pow_zero, pow_one]
  exact sub_eq_zero.mpr (conjugationCoord_rat_smul g (a ()) x)

theorem dualAdjoint_eq_conjugationCoord (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g x = conjugationCoord g x := by
  have he := congrArg (polynomialDualEval (L := L)) (conjugation_polynomial g x)
  rw [map_lieBCH, map_lieBCH, map_neg, polynomialDualEval_constant,
    polynomialDualEval_linear, polynomialDualEval_linear] at he
  have ht := congrArg (dualTangentLinear (L := L)) he
  exact ht.trans (dualTangentLinear_infinitesimal _)

theorem conjugationCoord_eq_add_lie (hs : 2 ≤ s)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hx : ⁅g.coord, ⁅g.coord, x⁆⁆ = 0) :
    conjugationCoord g x = x + ⁅g.coord, x⁆ := by
  rw [← dualAdjoint_eq_conjugationCoord]
  exact dualAdjoint_eq_add_lie hs g x hx

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
  (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)

include hUV

theorem invariant_sup_layer (j : ℕ) :
    ∀ u ∈ U, ∀ v ∈ V ⊔ F.layer j, ⁅u, v⁆ ∈ V ⊔ F.layer j := by
  intro u hu v hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [lie_add]
  exact (V ⊔ F.layer j).add_mem (Submodule.mem_sup_left (hUV _ hu _ hx))
    (Submodule.mem_sup_right ((F.layerIdeal j).lie_mem hy))

theorem lie_mem_invariant_sup_next_layer (j : ℕ) {u v : L} (hu : u ∈ U)
    (hv : v ∈ V ⊔ F.layer j) : ⁅u, v⁆ ∈ V ⊔ F.layer (j + 1) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [lie_add]
  apply (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_left (hUV _ hu _ hx))
  apply Submodule.mem_sup_right
  have hu1 : u ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  simpa only [Nat.add_comm 1 j] using F.lie_mem hu1 hy

theorem adjoint_current_layer_relation (hs : 2 ≤ s) {j : ℕ} (hj : 1 ≤ j)
    (g : F.Group) (hg : g.coord ∈ U) (r k p : L)
    (hp : p ∈ F.layer (j - 1)) (hk : k ∈ F.layer 1)
    (hr : r - k ∈ V ⊔ F.layer j)
    (hlower : ⁅g.coord - p, k⁆ ∈ V ⊔ F.layer (j + 1)) :
    ⁅p, k⁆ - (dualAdjoint g r - r) ∈ V ⊔ F.layer (j + 1) := by
  have hW := F.invariant_sup_layer U V hUV (j + 1)
  apply dualAdjoint_current_bracket_relation hs U (V ⊔ F.layer (j + 1)) hW g hg r k p
    (F.lie_mem_invariant_sup_next_layer U V hUV j hg hr) hlower
  have hpk : ⁅p, k⁆ ∈ F.layer j := by
    simpa only [Nat.sub_add_cancel hj] using F.lie_mem hp hk
  have hg1 : g.coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hhigh : ⁅g.coord, ⁅p, k⁆⁆ ∈ F.layer (j + 1) := by
    simpa only [Nat.add_comm 1 j] using F.lie_mem hg1 hpk
  have h := (V ⊔ F.layer (j + 1)).add_mem (hW _ hg _ hlower) (Submodule.mem_sup_right hhigh)
  simpa only [sub_lie, lie_sub, sub_add_cancel] using h

theorem adjoint_current_layer_quotient (hs : 2 ≤ s) {j : ℕ} (hj : 1 ≤ j)
    (g : F.Group) (hg : g.coord ∈ U) (r k p : L)
    (hp : p ∈ F.layer (j - 1)) (hk : k ∈ F.layer 1)
    (hr : r - k ∈ V ⊔ F.layer j)
    (hlower : ⁅g.coord - p, k⁆ ∈ V ⊔ F.layer (j + 1))
    (t : L) (ht : t = dualAdjoint g r) :
    (V ⊔ F.layer (j + 1)).mkQ ⁅p, k⁆ = (V ⊔ F.layer (j + 1)).mkQ (t - r) := by
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, ht]
  exact F.adjoint_current_layer_relation U V hUV hs hj g hg r k p hp hk hr hlower

end Erdos3.NilpotentLieFiltration

end

end OAI
