/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Lie.Prod
import OAI.Combinatorics.Progressions.Estimates.RefilteredPointwiseSplitting
import OAI.Combinatorics.Progressions.Linear.TopSubspaceAdaptedBasis
import OAI.Combinatorics.Progressions.Nilpotent.NiltestProbabilityProjection

namespace OAI

section

namespace Erdos3

open Module

theorem RationalHeightLE.inv {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) (hne : q ≠ 0) :
    RationalHeightLE q⁻¹ H := by
  have hn : q.num ≠ 0 := by
    intro hn
    apply hne
    rw [← q.num_div_den, hn, Int.cast_zero, zero_div]
  have h := rationalHeightLE_fraction (q.den : ℤ) q.num hn
    (by simpa only [Int.natAbs_natCast] using hq.2) hq.1
  have he : q⁻¹ = (q.den : ℚ) / q.num := by
    calc
      q⁻¹ = ((q.num : ℚ) / q.den)⁻¹ := congrArg Inv.inv q.num_div_den.symm
      _ = _ := inv_div _ _
  simpa only [he, Int.cast_natCast] using h

theorem exists_bounded_frequency_direction {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (hη : η ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H) :
    ∃ (v : V) (m : ℕ), 0 < m ∧ m ≤ H ∧ η v = 1 ∧
      (∀ i, RationalHeightLE (b.repr v i) H) ∧
      (fun i => b.repr v i) ∈ denominatorGrid m := by
  classical
  have hex : ∃ i, η (b i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hη
    apply b.ext
    intro i
    exact h i
  obtain ⟨i, hi⟩ := hex
  let c := (η (b i))⁻¹
  let v := c • b i
  have hc : RationalHeightLE c H := (hheight i).inv hi
  have hcoord (j : ι) : b.repr v j = if i = j then c else 0 := by
    simp only [v, map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  refine ⟨v, c.den, c.den_pos, hc.2, ?_, ?_, ?_⟩
  · change η (c • b i) = 1
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hi
  · intro j
    rw [hcoord]
    split_ifs
    · exact hc
    · exact rationalHeightLE_zero hH
  · refine ⟨fun j => if i = j then c.num else 0, ?_⟩
    intro j
    change (c.den : ℚ) * b.repr v j = ((if i = j then c.num else 0 : ℤ) : ℚ)
    rw [hcoord]
    by_cases hj : i = j
    · simp only [hj, ite_true]
      have hcden := (div_eq_iff (show (c.den : ℚ) ≠ 0 from Nat.cast_ne_zero.mpr c.den_ne_zero)).mp c.num_div_den
      simpa only [mul_comm] using hcden.symm
    · simp only [hj, ite_false, mul_zero, Int.cast_zero]

end Erdos3

end

section

namespace Erdos3

theorem rationalLogHeight_nat_inv_mul (n : ℕ) (hn : 0 < n) {x : ℚ} {p : ℝ}
    (hx : rationalLogHeight x ≤ p) : rationalLogHeight ((n : ℚ)⁻¹ * x) ≤ p + n + 1 := by
  have hp : 0 ≤ p := (rationalLogHeight_nonneg x).trans hx
  have hnheight : RationalHeightLE (n : ℚ) (n + 1) := by simp [RationalHeightLE]
  have hinv := hnheight.inv (by exact_mod_cast hn.ne')
  apply rationalLogHeight_le_of_height (hinv.mul (rationalHeightLE_ceil_exp hx))
  calc
    (((n + 1) * ⌈Real.exp p⌉₊ : ℕ) : ℝ) = ((n : ℝ) + 1) * (⌈Real.exp p⌉₊ : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp (p + 1) :=
      mul_le_mul (Real.add_one_le_exp _) (ceil_exp_le_exp_add_one hp)
        (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + n + 1) := by rw [← Real.exp_add]; congr 1; ring

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def dividedFrequency (n : ℕ) (η : L →ₗ[ℚ] ℚ) : L →ₗ[ℚ] ℚ := (n : ℚ)⁻¹ • η

theorem dividedFrequency_compensate (n : ℕ) (hn : 0 < n) (η : L →ₗ[ℚ] ℚ) :
    n • dividedFrequency n η = η := by
  ext x
  simp only [dividedFrequency, LinearMap.smul_apply, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn.ne' : (n : ℚ) ≠ 0), one_mul]

theorem dividedFrequency_height (n : ℕ) (hn : 0 < n) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (x : L) (hx : rationalLogHeight (η x) ≤ p) :
    rationalLogHeight (dividedFrequency n η x) ≤ p + n + 1 :=
  rationalLogHeight_nat_inv_mul n hn hx

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def frequencyKernelProjection (η : V →ₗ[ℚ] ℚ) (v : V) : V →ₗ[ℚ] V :=
  LinearMap.id - η.smulRight v

@[simp] theorem frequencyKernelProjection_apply (η : V →ₗ[ℚ] ℚ) (v x : V) :
    frequencyKernelProjection η v x = x - η x • v := rfl

theorem frequencyKernelProjection_range (η : V →ₗ[ℚ] ℚ) (v : V) (hv : η v = 1) :
    LinearMap.range (frequencyKernelProjection η v) = LinearMap.ker η := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change η (y - η y • v) = 0
    simp only [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
  · intro hx
    refine ⟨x, ?_⟩
    change x - η x • v = x
    rw [show η x = 0 from hx, zero_smul, sub_zero]

theorem frequencyKernel_spanning (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (v : V) (hv : η v = 1) :
    Submodule.span ℚ (Set.range (fun i => b i - η (b i) • v)) = LinearMap.ker η := by
  change Submodule.span ℚ (Set.range (frequencyKernelProjection η v ∘ b)) = _
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
    frequencyKernelProjection_range η v hv]

theorem frequencyKernel_spanning_height (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (v : V)
    {H : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) H)
    (hv : ∀ i, RationalHeightLE (b.repr v i) H) :
    ∀ i j, RationalHeightLE (b.repr (b i - η (b i) • v) j) (2 * H ^ 2) := by
  classical
  intro i j
  rw [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hbase : RationalHeightLE (b.repr (b i) j) 1 := by
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact rationalHeightLE_one le_rfl
    · exact rationalHeightLE_zero le_rfl
  have h := hbase.sub ((hη i).mul (hv j))
  convert h using 1
  ring

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realifyFunctional_eq_rid (η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional η x = TensorProduct.rid ℚ ℝ (η.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    simp only [realifyFunctional_tmul, LinearMap.baseChange_tmul, TensorProduct.rid_tmul,
      Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_realified_frequency_kernel_iff (η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker η).baseChange ℝ ↔ realifyFunctional η x = 0 := by
  rw [realification_ker, LinearMap.mem_ker, realifyFunctional_eq_rid]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (TensorProduct.rid ℚ ℝ).injective
    simpa only [map_zero] using h

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

def finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) :
    List J → Submodule ℚ V
  | [] => P
  | j :: js => LinearMap.ker (eta j) ⊓ finiteFrequencyKernel P eta js

theorem mem_finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    (js : List J) (v : V) :
    v ∈ finiteFrequencyKernel P eta js ↔ v ∈ P ∧ ∀ j ∈ js, eta j v = 0 := by
  induction js with
  | nil => simp [finiteFrequencyKernel]
  | cons j js ih =>
    simp only [finiteFrequencyKernel, Submodule.mem_inf, LinearMap.mem_ker, ih,
      List.forall_mem_cons]
    tauto

theorem finiteFrequencyKernel_le (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    finiteFrequencyKernel P eta js ≤ P := fun v hv => (mem_finiteFrequencyKernel P eta js v).mp hv |>.1

theorem mem_real_finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    (js : List J) (v : ℝ ⊗[ℚ] V) :
    v ∈ (finiteFrequencyKernel P eta js).baseChange ℝ ↔
      v ∈ P.baseChange ℝ ∧ ∀ j ∈ js, realifyFunctional (eta j) v = 0 := by
  induction js with
  | nil => simp [finiteFrequencyKernel]
  | cons j js ih =>
    simp only [finiteFrequencyKernel, realification_inf, Submodule.mem_inf,
      mem_realified_frequency_kernel_iff, ih, List.forall_mem_cons]
    tauto

def restrictedFrequencySpan (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    Submodule ℚ (Module.Dual ℚ P) :=
  Submodule.span ℚ ((fun j => (eta j).comp P.subtype) '' {j | j ∈ js})

theorem mem_restrictedFrequencySpan_coannihilator (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) (v : P) :
    v ∈ (restrictedFrequencySpan P eta js).dualCoannihilator ↔
      (v : V) ∈ finiteFrequencyKernel P eta js := by
  change v ∈ ((Submodule.span ℚ ((fun j => (eta j).comp P.subtype) '' {j | j ∈ js})).dualCoannihilator : Set P) ↔ _
  rw [Submodule.coe_dualCoannihilator_span, mem_finiteFrequencyKernel]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_image, LinearMap.comp_apply,
    Submodule.subtype_apply, v.property, true_and]

theorem mem_restrictedFrequencySpan_iff [FiniteDimensional ℚ V] (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) (xi : V →ₗ[ℚ] ℚ) :
    xi.comp P.subtype ∈ restrictedFrequencySpan P eta js ↔
      ∀ v ∈ finiteFrequencyKernel P eta js, xi v = 0 := by
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := restrictedFrequencySpan P eta js),
    Submodule.mem_dualAnnihilator]
  constructor
  · intro h v hv
    let x : P := ⟨v, finiteFrequencyKernel_le P eta js hv⟩
    exact h x ((mem_restrictedFrequencySpan_coannihilator P eta js x).mpr hv)
  · intro h v hv
    exact h v ((mem_restrictedFrequencySpan_coannihilator P eta js v).mp hv)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_comp {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (eta : W →ₗ[ℚ] ℚ) (f : V →ₗ[ℚ] W) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (eta.comp f) x = realifyFunctional eta (f.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp only [realifyFunctional_tmul, LinearMap.baseChange_tmul, LinearMap.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem projected_frequency_zero_on_kernel {V W Z J : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup Z] [Module ℚ Z]
    (P : Submodule ℚ V) (f : V →ₗ[ℚ] W) (g : V →ₗ[ℚ] Z)
    (eta : J → W →ₗ[ℚ] ℚ) (xi : J → Z →ₗ[ℚ] ℚ)
    (hzero : ∀ j x, x ∈ P → eta j (f x) + xi j (g x) = 0) :
    ∀ x ∈ P ⊓ LinearMap.ker g, ∀ j, eta j (f x) = 0 := by
  intro x hx j
  have h := hzero j x hx.1
  simpa only [show g x = 0 from hx.2, map_zero, add_zero] using h

theorem projected_real_frequency_zero_on_kernel {V W Z J : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup Z] [Module ℚ Z]
    (P : Submodule ℚ V) (f : V →ₗ[ℚ] W) (g : V →ₗ[ℚ] Z)
    (eta : J → W →ₗ[ℚ] ℚ) (xi : J → Z →ₗ[ℚ] ℚ)
    (hzero : ∀ j x, x ∈ P → eta j (f x) + xi j (g x) = 0) :
    ∀ x ∈ (P ⊓ LinearMap.ker g).baseChange ℝ, ∀ j,
      realifyFunctional (eta j) (f.baseChange ℝ x) = 0 := by
  intro x hx j
  have hle : P ⊓ LinearMap.ker g ≤ LinearMap.ker ((eta j).comp f) := by
    intro v hv
    exact projected_frequency_zero_on_kernel P f g eta xi hzero v hv j
  have h := (mem_realified_frequency_kernel_iff ((eta j).comp f) x).mp
    (Submodule.baseChange_mono ℝ hle hx)
  rwa [realifyFunctional_comp] at h

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem basisGradedSubmodule_iInf {ι J V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (w : ι → ℕ) (U : J → Submodule ℚ V)
    (hU : ∀ j, BasisGradedSubmodule b w (U j)) : BasisGradedSubmodule b w (⨅ j, U j) := by
  intro k x hx
  simp only [Submodule.mem_iInf] at hx ⊢
  exact fun j => hU j k x (hx j)

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem associatedGradedPieceMap_grade_fixed (j : ℕ) (x : F.layer j) :
    basisGradeProjection (F.associatedGradedBasis b w hF) w j (F.associatedGradedPieceMap j x) =
      F.associatedGradedPieceMap j x := by
  rw [← F.gradedPieceProjection_eq_pieceMap b w hF j x]
  apply (F.associatedGradedBasis b w hF).repr.injective
  ext i
  simp only [basisGradeProjection_repr, F.gradedPieceProjection_coordinate]
  split_ifs <;> rfl

theorem frequency_zero_on_refiltered_top (U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hzero : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b w hF) w s x = x →
      F.gradedFrequency b w hF eta x = 0) :
    ∀ x ∈ F.gradedRefiltrationLayer U s, eta x = 0 := by
  intro x hx
  obtain ⟨hxs, hxU⟩ := (F.mem_gradedRefiltrationLayer U s x).mp hx
  rw [← F.gradedFrequency_top_piece b w hF eta ⟨x, hxs⟩]
  exact hzero _ hxU (F.associatedGradedPieceMap_grade_fixed b w hF s ⟨x, hxs⟩)

theorem real_frequency_zero_on_refiltered_top (U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hzero : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b w hF) w s x = x →
      F.gradedFrequency b w hF eta x = 0) :
    ∀ x ∈ F.realGradedRefiltrationLayer U s, realifyFunctional eta x = 0 := by
  have hle : F.gradedRefiltrationLayer U s ≤ LinearMap.ker eta :=
    F.frequency_zero_on_refiltered_top b w hF U eta hzero
  intro x hx
  exact (mem_realified_frequency_kernel_iff eta x).mp (Submodule.baseChange_mono ℝ hle hx)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem exists_positive_frequency_projection_of_decomposition
    (T : D.Niltest (fun _ : Unit => 1)) (hT : T.UnitIntervalValued)
    {p : ℝ} (hTc : T.ComplexityLE p) {J : Type*} [Fintype J]
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest (fun _ : Unit => 1))
    (horbit : ∀ j, (U j).orbit = T.orbit)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    {N : ℕ} [NeZero N] (weight : ZMod N → ℂ) {B rho tau : ℝ}
    (hB : 0 ≤ B) (htau : 0 ≤ tau) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho) :
    ∃ S : D.Niltest (fun _ : Unit => 1), S.UnitIntervalValued ∧ S.ComplexityLE p ∧
      S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
        (∀ j, tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖ →
          realifyFunctional (eta j) z.coord = 0) →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ‖(𝔼 n, weight n * T.evalCyclic N (fun _ => n)) -
        (𝔼 n, weight n * S.evalCyclic N (fun _ => n))‖ ≤
          2 * B * rho + Fintype.card J * tau := by
  classical
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let active : Finset J := Finset.univ.filter
    (fun j => tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖)
  let js := active.toList
  let K := finiteFrequencyKernel (D.filtration.layer s) eta js
  have hK : K ≤ D.filtration.layer s := finiteFrequencyKernel_le _ _ _
  let b := Module.finBasis ℚ K
  let v : Fin (finrank ℚ K) → L := fun i => b i
  have hv (i : Fin (finrank ℚ K)) : v i ∈ D.filtration.layer s := hK (b i).property
  let A : Fin (finrank ℚ K) → IsometricCircleAction D.Space :=
    fun i => D.centralRationalCircle (v i) (hv i)
  have hfreq (j : J) (i : Fin (finrank ℚ K)) : ∃ n : ℤ,
      (∀ t x, (U j).observable ((A i).act t x) = character (n • t) * (U j).observable x) ∧
      (eta j (v i) = 0 → n = 0) :=
    D.exists_centralRationalCircle_frequency (v i) (hv i) (eta j) (U j).observable (hvertical j)
  choose n heigen hzero using hfreq
  let is := List.finRange (finrank ℚ K)
  have hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j) :=
    fun i _ j _ => D.centralRationalCircle_commutes (v i) (v j) (hv i) (hv j)
  have hsignificant (j : J)
      (hj : tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖) :
      ∀ i ∈ is, n j i = 0 := by
    intro i _
    apply hzero j i
    have hj' : j ∈ js := by simpa only [js, active, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj
    exact ((mem_finiteFrequencyKernel _ _ _ (v i)).mp (b i).property).2 j hj'
  obtain ⟨S, hS, hSc, hSo, hSinv, herror⟩ := T.exists_positive_circle_projection hT hTc A is hcomm
    U n horbit weight hB htau hweight happrox (fun j i _ => heigen j i) hsignificant
  refine ⟨S, hS, hSc, hSo, ?_, herror⟩
  intro z hz hzeta x
  have hzK : z.coord ∈ K.baseChange ℝ := by
    apply (mem_real_finiteFrequencyKernel (D.filtration.layer s) eta js z.coord).mpr
    refine ⟨hz, ?_⟩
    intro j hj
    apply hzeta j
    simpa only [js, active, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  exact D.invariant_of_kernel_circles K hK b S.observable
    (fun i t y => hSinv i (by simp [is]) t y) z hzK x

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

theorem finiteFrequencyKernel_eq_map_coannihilator (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    finiteFrequencyKernel P eta js =
      (restrictedFrequencySpan P eta js).dualCoannihilator.map P.subtype := by
  ext v
  constructor
  · intro hv
    let x : P := ⟨v, finiteFrequencyKernel_le P eta js hv⟩
    exact ⟨x, (mem_restrictedFrequencySpan_coannihilator P eta js x).mpr hv, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_restrictedFrequencySpan_coannihilator P eta js x).mp hx

theorem finiteFrequencyKernel_eq_of_span_eq (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) (xi : I → V →ₗ[ℚ] ℚ) (is : List I)
    (hspan : restrictedFrequencySpan P eta js = restrictedFrequencySpan P xi is) :
    finiteFrequencyKernel P eta js = finiteFrequencyKernel P xi is := by
  rw [finiteFrequencyKernel_eq_map_coannihilator, finiteFrequencyKernel_eq_map_coannihilator, hspan]

theorem exists_restricted_frequency_basis [FiniteDimensional ℚ V] (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    ∃ m : ℕ, m ≤ finrank ℚ P ∧ ∃ indices : Fin m → J,
      (∀ i, indices i ∈ js) ∧
      LinearIndependent ℚ (fun i => (eta (indices i)).comp P.subtype) ∧
      Submodule.span ℚ (Set.range (fun i => (eta (indices i)).comp P.subtype)) =
        restrictedFrequencySpan P eta js := by
  classical
  let W := restrictedFrequencySpan P eta js
  obtain ⟨u, hu, hspan, hlin⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ
    ((fun j => (eta j).comp P.subtype) '' {j | j ∈ js})
  have hex (i : Fin (finrank ℚ W)) :
      ∃ j, j ∈ js ∧ (eta j).comp P.subtype = u i := hu i
  choose indices hindices heq using hex
  have hfun : (fun i => (eta (indices i)).comp P.subtype) = u := funext heq
  refine ⟨finrank ℚ W, ?_, indices, hindices, ?_, ?_⟩
  · have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    omega
  · rw [hfun]
    exact hlin
  · rw [hfun]
    exact hspan

theorem restrictedFrequencySpan_finRange (P : Submodule ℚ V) {m : ℕ}
    (eta : Fin m → V →ₗ[ℚ] ℚ) :
    restrictedFrequencySpan P eta (List.finRange m) =
      Submodule.span ℚ (Set.range (fun i => (eta i).comp P.subtype)) := by
  unfold restrictedFrequencySpan
  congr 1
  ext x
  simp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L Y W J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] [LieRing W] [LieAlgebra ℚ W] {s : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

def pivotAnnihilatorIdeal : LieIdeal ℚ L :=
  F.topSubspaceIdeal (finiteFrequencyKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta js)
    ((finiteFrequencyKernel_le _ _ _).trans inf_le_left)

theorem mem_pivotAnnihilatorIdeal (x : L) :
    x ∈ F.pivotAnnihilatorIdeal π eta js ↔
      x ∈ F.layer s ∧ π x = 0 ∧ ∀ j ∈ js, eta j x = 0 := by
  change x ∈ finiteFrequencyKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta js ↔ _
  rw [mem_finiteFrequencyKernel]
  change ((x ∈ F.layer s ∧ π x = 0) ∧ ∀ j ∈ js, eta j x = 0) ↔ _
  exact and_assoc

noncomputable def pivotQuotientMarkedMap : (L ⧸ F.pivotAnnihilatorIdeal π eta js) →ₗ⁅ℚ⁆ Y :=
  lieQuotientDescend (F.pivotAnnihilatorIdeal π eta js) π
    (fun x hx => ((F.mem_pivotAnnihilatorIdeal π eta js x).mp hx).2.1)

noncomputable def pivotQuotientFrequency (j : J) (hj : j ∈ js) :
    (L ⧸ F.pivotAnnihilatorIdeal π eta js) →ₗ[ℚ] ℚ :=
  (F.pivotAnnihilatorIdeal π eta js).toSubmodule.liftQ (eta j)
    (fun x hx => ((F.mem_pivotAnnihilatorIdeal π eta js x).mp hx).2.2 j hj)

@[simp] theorem pivotQuotientMarkedMap_mk (x : L) :
    F.pivotQuotientMarkedMap π eta js (lieQuotientMap (F.pivotAnnihilatorIdeal π eta js) x) =
      π x := rfl

@[simp] theorem pivotQuotientFrequency_mk (j : J) (hj : j ∈ js) (x : L) :
    F.pivotQuotientFrequency π eta js j hj
      (lieQuotientMap (F.pivotAnnihilatorIdeal π eta js) x) = eta j x := rfl

noncomputable def pivotProductQuotientMap :
    (L × W) →ₗ⁅ℚ⁆ (L ⧸ F.pivotAnnihilatorIdeal π eta js) × W :=
  (lieQuotientMap (F.pivotAnnihilatorIdeal π eta js)).prodMap (LieHom.id : W →ₗ⁅ℚ⁆ W)

noncomputable def pivotProductMarkedMap :
    ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × W) →ₗ⁅ℚ⁆ (Y × W) :=
  (F.pivotQuotientMarkedMap π eta js).prodMap (LieHom.id : W →ₗ⁅ℚ⁆ W)

@[simp] theorem pivotProductMarkedMap_quotient (x : L × W) :
    F.pivotProductMarkedMap π eta js (F.pivotProductQuotientMap π eta js x) =
      (π x.1, x.2) := rfl

variable (partner : J → W →ₗ[ℚ] ℚ)

def joinedFrequencyTop : Submodule ℚ (L × W) :=
  finiteFrequencyKernel ((F.layer s).prod (⊤ : Submodule ℚ W))
    (fun j => (eta j).comp (LinearMap.fst ℚ L W) +
      (partner j).comp (LinearMap.snd ℚ L W)) js

theorem mem_joinedFrequencyTop (x : L × W) :
    x ∈ F.joinedFrequencyTop eta js partner ↔
      x.1 ∈ F.layer s ∧ ∀ j ∈ js, eta j x.1 + partner j x.2 = 0 := by
  rw [joinedFrequencyTop, mem_finiteFrequencyKernel]
  simp only [Submodule.mem_prod, Submodule.mem_top, and_true,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]

noncomputable def joinedFrequencyQuotientTop :
    Submodule ℚ ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × W) :=
  (F.joinedFrequencyTop eta js partner).map (F.pivotProductQuotientMap π eta js).toLinearMap

theorem joinedFrequencyQuotientTop_constraint
    (x : (L ⧸ F.pivotAnnihilatorIdeal π eta js) × W)
    (hx : x ∈ F.joinedFrequencyQuotientTop π eta js partner) (j : J) (hj : j ∈ js) :
    F.pivotQuotientFrequency π eta js j hj x.1 + partner j x.2 = 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ((F.mem_joinedFrequencyTop eta js partner y).mp hy).2 j hj

theorem joinedFrequencyQuotientTop_kernel_eq_zero
    (x : (L ⧸ F.pivotAnnihilatorIdeal π eta js) × W)
    (hx : x ∈ F.joinedFrequencyQuotientTop π eta js partner)
    (hzero : F.pivotProductMarkedMap π eta js x = 0) : x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hπ : π y.1 = 0 := congrArg Prod.fst hzero
  have hpartner : y.2 = 0 := congrArg Prod.snd hzero
  obtain ⟨htop, hconstraints⟩ := (F.mem_joinedFrequencyTop eta js partner y).mp hy
  have hmem : y.1 ∈ F.pivotAnnihilatorIdeal π eta js := by
    apply (F.mem_pivotAnnihilatorIdeal π eta js y.1).mpr
    refine ⟨htop, hπ, ?_⟩
    intro j hj
    simpa only [hpartner, map_zero, add_zero] using hconstraints j hj
  apply Prod.ext
  · exact (lieQuotientMap_eq_zero (F.pivotAnnihilatorIdeal π eta js) y.1).mpr hmem
  · exact hpartner

theorem joinedFrequencyQuotientTop_injective :
    Function.Injective (fun x : F.joinedFrequencyQuotientTop π eta js partner =>
      F.pivotProductMarkedMap π eta js x.val) := by
  intro x y hxy
  change F.pivotProductMarkedMap π eta js x.val =
    F.pivotProductMarkedMap π eta js y.val at hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply F.joinedFrequencyQuotientTop_kernel_eq_zero π eta js partner (x.val - y.val)
    ((F.joinedFrequencyQuotientTop π eta js partner).sub_mem x.property y.property)
  rw [map_sub, hxy, sub_self]

theorem joinedFastTop_kernel_eq_zero
    (T : Submodule ℚ ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × W))
    (hT : T ≤ F.joinedFrequencyQuotientTop π eta js partner)
    (x : (L ⧸ F.pivotAnnihilatorIdeal π eta js) × W) (hx : x ∈ T)
    (hzero : F.pivotProductMarkedMap π eta js x = 0) : x = 0 :=
  F.joinedFrequencyQuotientTop_kernel_eq_zero π eta js partner x (hT hx) hzero

end Erdos3.NilpotentLieFiltration

end

end OAI
