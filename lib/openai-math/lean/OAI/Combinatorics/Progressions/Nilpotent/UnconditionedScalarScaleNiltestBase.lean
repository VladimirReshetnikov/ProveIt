/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
import OAI.Combinatorics.Progressions.Lattices.ScalarLatePrimeCutoffPowerBudget
import OAI.Combinatorics.Progressions.Lattices.UnconditionedLatePrimeBudget

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct
namespace BooleanCubeKernel

theorem exists_unconditioned_latePrime_niltest_base (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∃ H : ℕ, 2 ≤ H ∧
      ∀ (n₀ : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
        (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)] (_i : X)
        {p a Λ σ : ℝ}, 0 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
        0 < σ → σ ≤ 1 →
        ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
        (∀ k, (P k).Prime) → Function.Injective P →
        (∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j) →
        (∀ k, Real.exp p ≤ (P k : ℝ)) →
        ∀ (N : X → ℕ),
          (∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
            (unconditionedSpatialTrimFraction (Fintype.card X) σ)
            (unconditionedCollisionWidth P σ) ≤ (N j : ℝ)) →
        ∀ (f : (X → ℤ) → ℝ), (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
          IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
          a + σ ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
      let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
      let R := spatialTrimMargin τ N
      let q := p + (n₀ : ℝ) + 2
      let D := min d₀ ⌊p⌋₊
      ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
        (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
      let law := selectedJointReference (trimmedIntegerBox N R)
        (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
      ∃ (productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        σ / 4 ≤ law.mass productive ∧
        (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
        (∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u : ∀ k, ZMod (P k),
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N) ∧
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots (Fin n₀) d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots (Fin n₀) d w)
        (localLaw : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          FiniteProbabilityWeights (integerBox P))
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1))
        (hpos : ∀ j, 1 ≤ w j) (hs : ∀ j, w j ≤ s),
        d ≤ d₀ ∧ d ≤ D ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, ∃ m, 0 < m ∧ ∃ (S : ResidueBoxSlice P m)
          (hlen : ∀ j, 0 < S.length j),
          (∀ j, Real.exp (-p) * (P j : ℝ) ≤ (S.length j : ℝ)) ∧
          localLaw z = S.fullSliceLaw hlen) ∧
        (∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
          (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue Ψ)) ∧
        (letI := polynomialShearIndexFintype w (fun i => hpos i)
         letI := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
         letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
         letI := realification_moduleTopology_t2 (polynomialShearOrderedBasis w)
         ∃ (F : (polynomialShearNilmanifold w s hs).Space → ℂ)
           (tests : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
             (polynomialShearNilmanifold w s hs).Niltest (fun _ : Fin n₀ => 1)),
           (∀ z, (tests z).observable = F ∧ (tests z).UnitIntervalValued ∧
             (tests z).ComplexityLE (((q + 2) ^ E + 2) ^ H)) ∧
           (∀ z t, (tests z).eval t =
             ((B.shearTransformedSlots hw
               ((localForm z).loweringAt (fun i => (t i : ℝ)))).patchValue Ψ : ℂ)) ∧
           ∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
             (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
               ((tests z).eval x.val).re)) := by
  obtain ⟨E, hE, hbase⟩ := exists_unconditioned_arbitrary_fixed_patch_family s
  obtain ⟨H, hH, hconvert⟩ := exists_fixed_local_patch_ordinary_niltest_family s
  refine ⟨E, hE, H, hH, ?_⟩
  intro n₀ X _ _ P _ i p a Λ σ hp ha hΛ hσ hσ1 d₀ habsolute
    hprime hinj hcompare hcutoff N hN f hf hfree hmean
  obtain ⟨hW, hR, hZ, productive, hprod, hinjective, hinside,
    d, w, hw, Ψ, B, localForm, localLaw, retained, hd₀, hdD, hpos, hs,
    hΨ, hB, hretained, hmass, hmass', hslice, hcorrelation⟩ :=
    hbase n₀ P i hp ha hΛ hσ hσ1 d₀ habsolute hprime hinj hcompare hcutoff
      N hN f hf hfree hmean
  refine ⟨hW, hR, hZ, productive, hprod, hinjective, hinside,
    d, w, hw, Ψ, B, localForm, localLaw, retained, hpos, hs, hd₀, hdD,
    hΨ, hB, hretained, hmass, hmass', hslice, hcorrelation, ?_⟩
  let := polynomialShearIndexFintype w (fun i => hpos i)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
  let := realification_moduleTopology_t2 (polynomialShearOrderedBasis w)
  let q := p + (n₀ : ℝ) + 2
  have hd : (d : ℝ) ≤ p :=
    (Nat.cast_le.mpr (hdD.trans (Nat.min_le_right _ _))).trans (Nat.floor_le hp)
  have hq : 1 ≤ q + 2 := by
    dsimp [q]
    linarith [Nat.cast_nonneg (α := ℝ) n₀]
  have hpq : p ≤ (q + 2) ^ E := by
    have hself : q + 2 ≤ (q + 2) ^ E := le_self_pow₀ hq (by omega)
    dsimp [q] at hself
    linarith [Nat.cast_nonneg (α := ℝ) n₀]
  obtain ⟨F, tests, htests, heval⟩ :=
    hconvert Ψ B localForm hw hpos hs ((q + 2) ^ E)
      (by positivity) (hd.trans hpq) hB hΨ
  refine ⟨F, tests, htests, heval, ?_⟩
  intro z hz
  simpa only [heval, Complex.ofReal_re] using hcorrelation z hz

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct
namespace BooleanCubeKernel

theorem exists_unconditioned_chosenLatePrime_niltest_base (s n₀ : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ E : ℕ, 2 ≤ E ∧ ∃ H : ℕ, 2 ≤ H ∧
      ∀ {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
        {p t a Λ : ℝ}, 2 ≤ p → p ≤ t → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
        ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
        (Fintype.card X : ℝ) ≤ p → ∀ (N : X → ℕ),
        (∀ j, Real.exp ((t + 2) ^ C) ≤ (N j : ℝ)) →
        ∀ (f : (X → ℤ) → ℝ), (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        ∀ (A : PolynomialPatch X s 0), Real.exp (-p) ≤ relativePatchBoxScore N f a A →
      ∃ (P : Fin n₀ → ℕ) (hprime : ∀ k, (P k).Prime),
        Function.Injective P ∧ (∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j) ∧
        (∀ k, Real.exp t ≤ (P k : ℝ) ∧ (P k : ℝ) ≤ Real.exp (t + (n₀ : ℝ) + 2)) ∧
      let : ∀ k, NeZero (P k) := fun k => ⟨(hprime k).ne_zero⟩
      let σ := Real.exp (-p)
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
      let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
      let R := spatialTrimMargin τ N
      let q := p + (n₀ : ℝ) + 2
      let D := min d₀ ⌊p⌋₊
      ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
        (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
      let law := selectedJointReference (trimmedIntegerBox N R)
        (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
      ∃ (productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        σ / 4 ≤ law.mass productive ∧
        (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
        (∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u : ∀ k, ZMod (P k),
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N) ∧
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots (Fin n₀) d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots (Fin n₀) d w)
        (localLaw : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          FiniteProbabilityWeights (integerBox P))
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1))
        (hpos : ∀ j, 1 ≤ w j) (hs : ∀ j, w j ≤ s),
        d ≤ d₀ ∧ d ≤ D ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, ∃ m, 0 < m ∧ ∃ (S : ResidueBoxSlice P m)
          (hlen : ∀ j, 0 < S.length j),
          (∀ j, Real.exp (-p) * (P j : ℝ) ≤ (S.length j : ℝ)) ∧
          localLaw z = S.fullSliceLaw hlen) ∧
        (∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
          (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue Ψ)) ∧
        (letI := polynomialShearIndexFintype w (fun i => hpos i)
         letI := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
         letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
         letI := realification_moduleTopology_t2 (polynomialShearOrderedBasis w)
         ∃ (F : (polynomialShearNilmanifold w s hs).Space → ℂ)
           (tests : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
             (polynomialShearNilmanifold w s hs).Niltest (fun _ : Fin n₀ => 1)),
           (∀ z, (tests z).observable = F ∧ (tests z).UnitIntervalValued ∧
             (tests z).ComplexityLE (((q + 2) ^ E + 2) ^ H)) ∧
           (∀ z t, (tests z).eval t =
             ((B.shearTransformedSlots hw
               ((localForm z).loweringAt (fun i => (t i : ℝ)))).patchValue Ψ : ℂ)) ∧
           ∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
             (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
               ((tests z).eval x.val).re)) := by
  obtain ⟨C, hC, hchoose⟩ := exists_unconditioned_late_prime_side_budget n₀
  obtain ⟨E, hE, H, hH, hfamily⟩ := exists_unconditioned_latePrime_niltest_base s
  refine ⟨C, hC, E, hE, H, hH, ?_⟩
  intro X _ _ _ p t a Λ hp hpt ha haΛ hΛ d₀ habsolute hX N hN f hf hfree A hscore
  obtain ⟨P, hprime, hinj, hcompare, hrange, hcutoff, hwidth⟩ := hchoose p t hp hpt
  let : ∀ k, NeZero (P k) := fun k => ⟨(hprime k).ne_zero⟩
  have hNpos (i : X) : 0 < N i := by
    exact_mod_cast (Real.exp_pos ((t + 2) ^ C)).trans_le (hN i)
  have hbox : (integerBox N).Nonempty := by
    refine ⟨fun _ => 0, (mem_integerBox N _).mpr ?_⟩
    intro i
    exact ⟨le_refl _, by exact_mod_cast hNpos i⟩
  have hmean : a + Real.exp (-p) ≤ 𝔼 x ∈ integerBox N, f x :=
    zero_slot_score_mean_lower_bound A N hbox f (Real.exp_pos _) hscore
  have ha0 : 0 ≤ a := (Real.exp_pos (-p)).le.trans ha
  have hΛ0 : 0 ≤ Λ := ha0.trans haΛ
  have hσ1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hspatial : ∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p)))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N j : ℝ) :=
    fun j => (hwidth (Fintype.card X) hX).trans (hN j)
  refine ⟨P, hprime, hinj, hcompare, hrange, ?_⟩
  exact hfamily n₀ P (Classical.choice inferInstance) (by linarith) ha0 ⟨hΛ0, hΛ⟩
    (Real.exp_pos _) hσ1 d₀ habsolute hprime hinj hcompare hcutoff N hspatial f hf hfree hmean

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct

noncomputable def unconditionedScalarPrimeRatio (n : ℕ) : ℕ :=
  ⌈Real.exp ((n : ℝ) + 2)⌉₊ + 2

theorem unconditionedScalarPrimeRatio_two_le (n : ℕ) :
    2 ≤ unconditionedScalarPrimeRatio n := by
  unfold unconditionedScalarPrimeRatio
  omega

theorem unconditionedScalarPrimeRatio_exp_bound (n : ℕ) (t : ℝ) :
    Real.exp (t + (n : ℝ) + 2) ≤ (unconditionedScalarPrimeRatio n : ℝ) * Real.exp t := by
  have hratio : Real.exp ((n : ℝ) + 2) ≤ (unconditionedScalarPrimeRatio n : ℝ) := by
    have hceil := Nat.le_ceil (Real.exp ((n : ℝ) + 2))
    unfold unconditionedScalarPrimeRatio
    push_cast
    linarith
  calc
    _ = Real.exp ((n : ℝ) + 2) * Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg t)

private theorem lateScalarScale_ge_input (n r e a c : ℕ)
    (he : 1 ≤ e) (ha : 2 ≤ a) (hc : 2 ≤ c) {p : ℝ} (hp : 2 ≤ p) :
    p ≤ (8 * (((r * n + 1 : ℕ) : ℝ)) * (((p + 2) ^ e + 2) ^ a + 1) + 2) ^ c := by
  have hb : p + 2 ≤ (p + 2) ^ e := le_self_pow₀ (by linarith) (by omega)
  have hs : (p + 2) ^ e + 2 ≤ ((p + 2) ^ e + 2) ^ a :=
    le_self_pow₀ (by linarith) (by omega)
  have hn : (1 : ℝ) ≤ ((r * n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 (r * n)
  have ht : p ≤ 8 * (((r * n + 1 : ℕ) : ℝ)) * (((p + 2) ^ e + 2) ^ a + 1) := by
    nlinarith
  have hpw := le_self_pow₀ (by linarith : (1 : ℝ) ≤
    8 * (((r * n + 1 : ℕ) : ℝ)) * (((p + 2) ^ e + 2) ^ a + 1) + 2) (by omega : c ≠ 0)
  linarith

namespace BooleanCubeKernel

theorem exists_unconditioned_scalarScale_niltest_base (s n₀ : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∃ H : ℕ, 2 ≤ H ∧
    ∀ scalarE scalarC scalarF inputPower : ℕ,
      2 ≤ scalarE → 2 ≤ scalarC → 2 ≤ scalarF → 1 ≤ inputPower →
    ∃ U : ℕ, 2 ≤ U ∧
      ∀ {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
        {p a Λ : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
        ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
        (Fintype.card X : ℝ) ≤ p → ∀ (N : X → ℕ),
        (∀ j, Real.exp ((p + 2) ^ U) ≤ (N j : ℝ)) →
        ∀ (f : (X → ℤ) → ℝ), (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        ∀ (A : PolynomialPatch X s 0), Real.exp (-p) ≤ relativePatchBoxScore N f a A →
      let b := (p + 2) ^ inputPower
      let scalarInput := (b + 2) ^ scalarE
      let ratio := unconditionedScalarPrimeRatio n₀
      let target := 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) * (scalarInput + 1)
      let t := (target + 2) ^ scalarC
      (∀ j, Real.exp ((scalarInput + scalarF) ^ scalarF) ≤ (N j : ℝ)) ∧
      ∃ (P : Fin n₀ → ℕ) (hprime : ∀ k, (P k).Prime),
        Function.Injective P ∧ (∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j) ∧
        (∀ k, Real.exp t ≤ (P k : ℝ) ∧ (P k : ℝ) ≤ (ratio : ℝ) * Real.exp t) ∧
      let : ∀ k, NeZero (P k) := fun k => ⟨(hprime k).ne_zero⟩
      let σ := Real.exp (-p)
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
      let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
      let R := spatialTrimMargin τ N
      let q := p + (n₀ : ℝ) + 2
      let D := min d₀ ⌊p⌋₊
      ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
        (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
      let law := selectedJointReference (trimmedIntegerBox N R)
        (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
      ∃ (productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        σ / 4 ≤ law.mass productive ∧
        (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
        (∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u : ∀ k, ZMod (P k),
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N) ∧
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots (Fin n₀) d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots (Fin n₀) d w)
        (localLaw : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          FiniteProbabilityWeights (integerBox P))
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1))
        (hpos : ∀ j, 1 ≤ w j) (hs : ∀ j, w j ≤ s),
        d ≤ d₀ ∧ d ≤ D ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, ∃ m, 0 < m ∧ ∃ (S : ResidueBoxSlice P m)
          (hlen : ∀ j, 0 < S.length j),
          (∀ j, Real.exp (-p) * (P j : ℝ) ≤ (S.length j : ℝ)) ∧
          localLaw z = S.fullSliceLaw hlen) ∧
        (∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
          (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue Ψ)) ∧
        (letI := polynomialShearIndexFintype w (fun i => hpos i)
         letI := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
         letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
         letI := realification_moduleTopology_t2 (polynomialShearOrderedBasis w)
         ∃ (F : (polynomialShearNilmanifold w s hs).Space → ℂ)
           (tests : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
             (polynomialShearNilmanifold w s hs).Niltest (fun _ : Fin n₀ => 1)),
           (∀ z, (tests z).observable = F ∧ (tests z).UnitIntervalValued ∧
             (tests z).ComplexityLE (((q + 2) ^ E + 2) ^ H)) ∧
           (∀ z t, (tests z).eval t =
             ((B.shearTransformedSlots hw
               ((localForm z).loweringAt (fun i => (t i : ℝ)))).patchValue Ψ : ℂ)) ∧
           ∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
             (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
               ((tests z).eval x.val).re)) := by
  obtain ⟨baseC, _, E, hE, H, hH, hbase⟩ := exists_unconditioned_chosenLatePrime_niltest_base s n₀
  refine ⟨E, hE, H, hH, ?_⟩
  intro scalarE scalarC scalarF inputPower hscalarE hscalarC _hscalarF hinputPower
  obtain ⟨U, hU, hcutoff⟩ := exists_scalarLatePrimeCutoff_composite_power_budget
    n₀ (unconditionedScalarPrimeRatio n₀) scalarE scalarC scalarF baseC inputPower
  refine ⟨U, hU, ?_⟩
  intro X _ _ _ p a Λ hp ha haΛ hΛ d₀ habsolute hX N hN f hf hfree A hscore
    b scalarInput ratio target t
  obtain ⟨hscalarN, hbaseN⟩ := hcutoff p hp
  have hpt : p ≤ t := by
    simpa only [t, target, ratio, scalarInput, b, Nat.cast_add, Nat.cast_one] using
      lateScalarScale_ge_input n₀ (unconditionedScalarPrimeRatio n₀) inputPower scalarE scalarC
        hinputPower hscalarE hscalarC hp
  obtain ⟨P, hprime, hinj, hcompare, hrange, hfamily⟩ :=
    hbase hp hpt ha haΛ hΛ d₀ habsolute hX N
      (fun j => (Real.exp_le_exp.mpr hbaseN).trans (hN j)) f hf hfree A hscore
  refine ⟨fun j => (Real.exp_le_exp.mpr hscalarN).trans (hN j),
    P, hprime, hinj, hcompare, ?_, hfamily⟩
  intro k
  exact ⟨(hrange k).1, (hrange k).2.trans (unconditionedScalarPrimeRatio_exp_bound n₀ t)⟩

end BooleanCubeKernel
end Erdos3

end

end OAI
