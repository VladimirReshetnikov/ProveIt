/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
import OAI.Combinatorics.Progressions.Linear.NativeDilationPairProjections
import OAI.Combinatorics.Progressions.Polynomial.FinitePhaseCancellation

namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators NNReal

noncomputable def signedTensorProduct (m : ℤ) (v : Fin m.natAbs → ℂ) : ℂ :=
  if m < 0 then star (∏ i, v i) else ∏ i, v i

theorem signedTensorProduct_norm (m : ℤ) (v : Fin m.natAbs → ℂ) :
    ‖signedTensorProduct m v‖ = ∏ i, ‖v i‖ := by
  unfold signedTensorProduct
  split_ifs <;> simp only [norm_star, norm_prod]

theorem signedTensorProduct_norm_le (m : ℤ) (v : Fin m.natAbs → ℂ)
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖signedTensorProduct m v‖ ≤ 1 := by
  rw [signedTensorProduct_norm]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)

theorem signedTensorProduct_phase (m : ℤ) (v : Fin m.natAbs → ℂ)
    (θ : CircleFourier.Circle) :
    signedTensorProduct m (fun i => character θ * v i) =
      character (m • θ) * signedTensorProduct m v := by
  cases m with
  | ofNat n =>
    have hn : ¬Int.ofNat n < 0 := not_lt.mpr (Int.natCast_nonneg n)
    simp only [signedTensorProduct, ite_eq_right hn, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change character θ ^ n * (∏ i, v i) = character ((n : ℤ) • θ) * (∏ i, v i)
    rw [natCast_zsmul, character_nsmul]
  | negSucc n =>
    have hn : Int.negSucc n < 0 := by omega
    simp only [signedTensorProduct, ite_eq_left hn, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change star (character θ ^ (n + 1) * (∏ i, v i)) =
      character (-((n + 1 : ℕ) : ℤ) • θ) * star (∏ i, v i)
    rw [neg_smul, character_neg, natCast_zsmul, character_nsmul, star_mul]
    exact mul_comm _ _

theorem signed_power_phase_cancellation (m : ℤ) (v : ℂ) (w : Fin m.natAbs → ℂ)
    (θ₀ θ₁ : CircleFourier.Circle) (hθ : θ₀ = m • θ₁) :
    (character θ₀ * v) * star (signedTensorProduct m (fun i => character θ₁ * w i)) =
      v * star (signedTensorProduct m w) := by
  rw [signedTensorProduct_phase, hθ, star_mul]
  calc
    _ = (character (m • θ₁) * star (character (m • θ₁))) *
        (v * star (signedTensorProduct m w)) := by ring
    _ = _ := by rw [circle_character_mul_star, one_mul]

theorem signedTensorProduct_lipschitz {X : Type*} [PseudoMetricSpace X]
    (m : ℤ) (f : Fin m.natAbs → X → ℂ) {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, ‖f i x‖ ≤ 1) :
    LipschitzWith (m.natAbs * K) (fun x => signedTensorProduct m (fun i => f i x)) := by
  have h := bounded_lipschitz_fintype_prod f (B := 1) le_rfl hf hn
  have hp : LipschitzWith (m.natAbs * K) (fun x => ∏ i, f i x) := by
    simpa only [Fintype.card_fin, one_pow, mul_one] using h.2
  unfold signedTensorProduct
  split_ifs
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using hp.dist_le_mul x y
  · exact hp

end Erdos3

end

section

namespace Erdos3

variable {σ I : Type*}

noncomputable def integerDilationVector (f : I → (σ → ℤ) → ℂ)
    (q : ℤ) (a : I) (x : σ → ℤ) : ℂ := f a (fun i => q * x i)

noncomputable def signedTensorVector (f : I → (σ → ℤ) → ℂ)
    (m : ℤ) (a : Fin m.natAbs → I) (x : σ → ℤ) : ℂ :=
  signedTensorProduct m (fun j => f (a j) x)

noncomputable def dilationTensorCrossProduct (f : I → (σ → ℤ) → ℂ)
    (q : ℤ) (t : ℕ) (a : I × (Fin (q ^ t).natAbs → I)) (x : σ → ℤ) : ℂ :=
  integerDilationVector f q a.1 x * star (signedTensorVector f (q ^ t) a.2 x)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realDilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairFiltration (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).realification.subgroup s) :
    F.realDilationPairProjection (q : ℚ) 0 g =
      (F.realDilationPairProjection (q : ℚ) 1 g) ^ (q ^ s) := by
  let h : (F.realification.dilationPairFiltration (q : ℚ)).Group :=
    ⟨F.realifiedDilationPairEquiv (q : ℚ) g.coord⟩
  have hh : h ∈ (F.realification.dilationPairFiltration (q : ℚ)).subgroup s :=
    (F.realifiedDilationPairEquiv_mem_layer (q : ℚ) s g.coord).mp hg
  have he (j : Fin 2) : F.realDilationPairProjection (q : ℚ) j g =
      (NilpotentLieBCHGroup.map (F.realification.dilationPairProjection (q : ℚ) j) h :
        F.realification.Group) := by
    apply NilpotentLieBCHGroup.ext
    exact F.realDilationPairProjection_coord (q : ℚ) j g
  rw [he 0, he 1]
  exact F.realification.dilationPair_top_group_relation q h hh

end NilpotentLieFiltration

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realDilationPairProjection_mem (q : ℚ) (j : Fin 2) (a : σ → ℕ)
    {g : (F.dilationPairMultidegree q).realification.Group}
    (hg : g ∈ (F.dilationPairMultidegree q).realification.subgroup a) :
    F.ordinary.realDilationPairProjection q j g ∈ F.realification.subgroup a := by
  have hm := (F.realifiedDilationPairEquiv_mem_multidegree q a g.coord).mp hg
  change (F.ordinary.realDilationPairProjection q j g).coord ∈ F.realification.layer a
  rw [F.ordinary.realDilationPairProjection_coord]
  fin_cases j
  · exact hm.1
  · exact hm.2.1

theorem realDilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairMultidegree (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairMultidegree (q : ℚ)).realification.subgroup bound) :
    F.ordinary.realDilationPairProjection (q : ℚ) 0 g =
      (F.ordinary.realDilationPairProjection (q : ℚ) 1 g) ^ (q ^ ∑ i, bound i) := by
  let h : (F.realification.dilationPairMultidegree (q : ℚ)).Group :=
    ⟨F.ordinary.realifiedDilationPairEquiv (q : ℚ) g.coord⟩
  have hh : h ∈ (F.realification.dilationPairMultidegree (q : ℚ)).subgroup bound :=
    (F.realifiedDilationPairEquiv_mem_multidegree (q : ℚ) bound g.coord).mp hg
  have he (j : Fin 2) : F.ordinary.realDilationPairProjection (q : ℚ) j g =
      (NilpotentLieBCHGroup.map (F.ordinary.realification.dilationPairProjection (q : ℚ) j) h :
        F.realification.Group) := by
    apply NilpotentLieBCHGroup.ext
    exact F.ordinary.realDilationPairProjection_coord (q : ℚ) j g
  rw [he 0, he 1]
  exact F.realification.dilationPair_top_group_relation q h hh

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem of_dilation_family {σ I : Type*} [Fintype I]
    {s : ℕ} {p b r : ℝ} (f : I → (σ → ℤ) → ℂ) (q : ℤ) (t : ℕ)
    (R : NativeIntegerModelFamily (fun _ : σ => 1) s b (dilationTensorCrossProduct f q t))
    (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hpr : p ≤ r) (htr : ((q ^ t).natAbs : ℝ) * p ≤ r) (hbr : b ≤ r) :
    NativeIntegerVectorEquivalence s r (integerDilationVector f q) (signedTensorVector f (q ^ t)) := by
  refine {
    left_dimension := hcard.trans (Real.exp_le_exp.mpr hpr)
    right_dimension := ?_
    expansion := ?_ }
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp p ^ (q ^ t).natAbs := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _
      _ = Real.exp (((q ^ t).natAbs : ℝ) * p) := (Real.exp_nat_mul p _).symm
      _ ≤ Real.exp r := Real.exp_le_exp.mpr htr
  · intro a b
    exact ⟨(NativeIntegerExpansion.ofModelFamily R (a, b)).mono hbr⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (q : ℚ)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
  (hEL : E.lattice = M.dilationPairLattice q)

noncomputable def dilationObservable (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ) (x : E.Space) : ℂ :=
  u₀ (ε • M.dilationSpaceProjection q E hEL 0 x) *
    star (signedTensorProduct m (fun a => u a (ε • M.dilationSpaceProjection q E hEL 1 x)))

theorem dilationObservable_mk (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ) (g : E.RealGroup) :
    M.dilationObservable q E hEL m ε u₀ u (QuotientGroup.mk g) =
      u₀ (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection q 0 g)) *
        star (signedTensorProduct m (fun a => u a
          (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection q 1 g)))) := rfl

theorem dilationObservable_norm_le (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ)
    (h₀ : ∀ x, ‖u₀ x‖ ≤ 1) (hu : ∀ a x, ‖u a x‖ ≤ 1) (x : E.Space) :
    ‖M.dilationObservable q E hEL m ε u₀ u x‖ ≤ 1 := by
  simp only [dilationObservable, norm_mul, norm_star]
  simpa only [mul_one] using mul_le_mul (h₀ _)
    (signedTensorProduct_norm_le m _ (fun a => hu a _))
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem dilationSpaceProjection_top_smul (ε : D.RealGroup) (j : Fin 2) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration q).realification.subgroup s)
    (x : E.Space) :
    ε • M.dilationSpaceProjection q E hEL j (k • x) =
      M.filtration.ordinary.realDilationPairProjection q j k •
        (ε • M.dilationSpaceProjection q E hEL j x) := by
  have hz := M.filtration.ordinary.realDilationPairProjection_mem q j hk
  rw [M.dilationSpaceProjection_smul, ← mul_smul, ← mul_smul,
    (M.filtration.realification.ordinary.top_commutes _ hz ε).eq]

theorem dilationObservable_component_top (ε : D.RealGroup) (u : D.Space → ℂ)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hu : ∀ z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u (z • x) = character (χ z) * u x)
    (j : Fin 2) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration q).realification.subgroup s)
    (x : E.Space) :
    u (ε • M.dilationSpaceProjection q E hEL j (k • x)) =
      character (χ (M.filtration.ordinary.realDilationPairProjection q j k)) *
        u (ε • M.dilationSpaceProjection q E hEL j x) := by
  rw [M.dilationSpaceProjection_top_smul q E hEL ε j k hk x]
  exact hu _ (M.filtration.ordinary.realDilationPairProjection_mem q j hk) _

theorem dilationObservable_top_invariant (m : ℤ) (ε : D.RealGroup)
    (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ)
    (χ : D.RealGroup → CircleFourier.Circle)
    (h₀ : ∀ z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u₀ (z • x) = character (χ z) * u₀ x)
    (hu : ∀ a z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u a (z • x) = character (χ z) * u a x)
    (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration q).realification.subgroup s)
    (hphase : χ (M.filtration.ordinary.realDilationPairProjection q 0 k) =
      m • χ (M.filtration.ordinary.realDilationPairProjection q 1 k))
    (x : E.Space) :
    M.dilationObservable q E hEL m ε u₀ u (k • x) =
      M.dilationObservable q E hEL m ε u₀ u x := by
  have hvalue₀ := M.dilationObservable_component_top q E hEL ε u₀ χ h₀ 0 k hk x
  have hvalue (a) := M.dilationObservable_component_top q E hEL ε (u a) χ (hu a) 1 k hk x
  unfold dilationObservable
  rw [hvalue₀]
  simp_rw [hvalue]
  exact signed_power_phase_cancellation m _ _ _ _ hphase

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
