import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistParameterPartition
import OAI.Combinatorics.Progressions.Estimates.PhysicalBaseInjection
import OAI.Combinatorics.Progressions.Sampling.FiniteObservationRetraction

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def integerPhysicalSite {K I : Type*} [Fintype K] (root : K → ℤ)
    (z : Option K × I → ℤ) : I → ℤ :=
  fun i => z (none,i) + ∑ k, root k * z (some k,i)

theorem integerPhysicalSite_cast_apply {K I : Type*} [Fintype K]
    (root : K → ℤ) (z : Option K × I → ℤ) (i : I) :
    (integerPhysicalSite root z i : ℝ) = physicalAffineSite root z i := by
  have h := physicalAffineSite_baseArrayJoin_apply root
    (fun k => z (some k.1,k.2)) (fun i => z (none,i)) i
  rw [baseArrayJoin_eta] at h
  simpa only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul] using h.symm

def integerBoxCenter {I : Type*} (N : I → ℕ) : I → ℤ := fun i => (N i / 2 : ℕ)

def centeredIntegerPhysicalSite {K I : Type*} [Fintype K] (root : K → ℤ) (N : I → ℕ)
    (z : Option K × I → ℤ) : I → ℤ := integerBoxCenter N + integerPhysicalSite root z

theorem centeredIntegerPhysicalSite_cast {K I : Type*} [Fintype K]
    (root : K → ℤ) (N : I → ℕ) (z : Option K × I → ℤ) :
    (fun i => (centeredIntegerPhysicalSite root N z i : ℝ)) =
      (fun i => (integerBoxCenter N i : ℝ)) + physicalAffineSite root z := by
  funext i
  simp only [centeredIntegerPhysicalSite, Pi.add_apply, Int.cast_add, integerPhysicalSite_cast_apply]

noncomputable def physicalSiteWidth {K I : Type*} [Fintype K]
    (root : K → ℤ) (W : Option K × I → ℝ) (i : I) : ℝ :=
  W (none,i) + ∑ k, |(root k : ℝ)| * W (some k,i)

theorem integerPhysicalSite_abs_bound {K I : Type*} [Fintype K]
    (root : K → ℤ) (W : Option K × I → ℝ) (z : Option K × I → ℤ)
    (hz : ∀ a, |(z a : ℝ)| ≤ W a) (i : I) :
    |(integerPhysicalSite root z i : ℝ)| ≤ physicalSiteWidth root W i := by
  simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul, physicalSiteWidth]
  calc
    _ ≤ |(z (none,i) : ℝ)| + |∑ k, (root k : ℝ) * (z (some k,i) : ℝ)| := abs_add_le _ _
    _ ≤ |(z (none,i) : ℝ)| + ∑ k, |(root k : ℝ) * (z (some k,i) : ℝ)| :=
      add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ _ := add_le_add (hz _) (Finset.sum_le_sum (fun k _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hz _) (abs_nonneg _)))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

def integerBaseTranslation {K I : Type*} (b : I → ℤ) : Option K × I → ℤ :=
  baseArrayJoin 0 b

namespace BooleanCubeKernel

open scoped BigOperators

theorem integerPhysicalSite_add {K I : Type*} [Fintype K]
    (root : K → ℤ) (z w : Option K × I → ℤ) :
    integerPhysicalSite root (z + w) = integerPhysicalSite root z + integerPhysicalSite root w := by
  funext i
  simp only [integerPhysicalSite, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem integerPhysicalSite_baseTranslation {K I : Type*} [Fintype K]
    (root : K → ℤ) (b : I → ℤ) :
    integerPhysicalSite root (integerBaseTranslation b) = b := by
  funext i
  simp [integerPhysicalSite, integerBaseTranslation, baseArrayJoin]

theorem integerPhysicalSite_baseTranslation_add {K I : Type*} [Fintype K]
    (root : K → ℤ) (b : I → ℤ) (z : Option K × I → ℤ) :
    integerPhysicalSite root (integerBaseTranslation b + z) = b + integerPhysicalSite root z := by
  rw [integerPhysicalSite_add, integerPhysicalSite_baseTranslation]

theorem physicalAffineSite_baseTranslation_add {K I : Type*} [Fintype K]
    (root : K → ℤ) (b : I → ℤ) (z : Option K × I → ℤ) :
    physicalAffineSite root (integerBaseTranslation b + z) =
      (fun i => (b i : ℝ)) + physicalAffineSite root z := by
  funext i
  simp only [← integerPhysicalSite_cast_apply, integerPhysicalSite_baseTranslation_add,
    Pi.add_apply, Int.cast_add]

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (N : I → ℕ) (hN : (integerBox N).Nonempty)

noncomputable def integerBoxObservation : (I → ℝ) → integerBox N :=
  finiteObservation (integerBox N) hN (fun x i => (x i : ℝ))

theorem integerBoxObservation_cast (x : integerBox N) :
    integerBoxObservation N hN (fun i => (x.val i : ℝ)) = x := by
  apply finiteObservation_apply
  intro a b h
  funext i
  have hi := congrFun h i
  change (a i : ℝ) = (b i : ℝ) at hi
  exact_mod_cast hi

theorem integerBoxObservation_reference :
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).fiberLaw
      (fun x => integerBoxObservation N hN (fun i => (x.val i : ℝ))) =
        FiniteProbabilityWeights.uniformFinset (integerBox N) hN := by
  have he : (fun x : integerBox N => integerBoxObservation N hN (fun i => (x.val i : ℝ))) = id :=
    funext (integerBoxObservation_cast N hN)
  rw [he, FiniteProbabilityWeights.fiberLaw_id]

namespace BooleanCubeKernel

theorem integerBoxObservation_physical {K : Type*} [Fintype K]
    (root : K → ℤ) (z : Option K × I → ℤ)
    (hz : integerPhysicalSite root z ∈ integerBox N) :
    (integerBoxObservation N hN (physicalAffineSite root z)).val = integerPhysicalSite root z := by
  have he := congrArg Subtype.val (integerBoxObservation_cast N hN ⟨integerPhysicalSite root z,hz⟩)
  simpa only [integerPhysicalSite_cast_apply] using he

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open BooleanCubeKernel
open scoped BigOperators Classical

variable {K : Type*} {P : K → ℕ} {q r : ℕ}

def composeSlice (S : ResidueBoxSlice P q) (T : ResidueBoxSlice S.length r) :
    ResidueBoxSlice P (q * r) where
  start k := S.start k + q * T.start k
  length := T.length
  inside k j hj := by
    have h := S.inside k _ (T.inside k j hj)
    convert h using 1; ring

theorem composeSlice_point (S : ResidueBoxSlice P q) (T : ResidueBoxSlice S.length r)
    (u : ∀ k, Fin (T.length k)) : (S.composeSlice T).point u = S.point (T.point u) := by
  funext k
  apply Fin.ext
  change S.start k + q * T.start k + (q * r) * (u k).val =
    S.start k + q * (T.start k + r * (u k).val)
  ring

def parameterCell (Q : ∀ k, FiniteProgressionPartition (P k))
    (hstep : ∀ k c, (Q k).step c = r) (c : ∀ k, (Q k).Label) : ResidueBoxSlice P r where
  start k := (Q k).start (c k)
  length k := (Q k).length (c k)
  inside k j hj := by simpa only [hstep] using (Q k).point_lt (c k) hj

theorem parameterCell_point [Fintype K] [DecidableEq K]
    (Q : ∀ k, FiniteProgressionPartition (P k))
    (hstep : ∀ k c, (Q k).step c = r) (c : ∀ k, (Q k).Label)
    (u : ∀ k, Fin ((Q k).length (c k))) :
    (parameterCell Q hstep c).point u = BoxProgressionPartition.point Q c u := by
  funext k
  apply Fin.ext
  simp only [point, parameterCell, BoxProgressionPartition.point_val, hstep]

theorem stride_mul_length_le_twice (S : ResidueBoxSlice P q) (k : K)
    (hlen : 2 ≤ S.length k) : q * S.length k ≤ 2 * P k := by
  have hlast := S.inside k (S.length k - 1) (by omega)
  have hlen' : S.length k ≤ 2 * (S.length k - 1) := by omega
  have hmul := Nat.mul_le_mul_left q hlen'
  nlinarith

theorem composeSlice_length_lower (S : ResidueBoxSlice P q)
    (T : ResidueBoxSlice S.length r) {cost loss : ℝ}
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hT : ∀ k, (S.length k : ℝ) * Real.exp (-loss) ≤ T.length k) (k : K) :
    Real.exp (-(cost + loss)) * (P k : ℝ) ≤ (S.composeSlice T).length k := by
  calc
    _ = (Real.exp (-cost) * (P k : ℝ)) * Real.exp (-loss) := by
      rw [mul_right_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (S.length k : ℝ) * Real.exp (-loss) :=
      mul_le_mul_of_nonneg_right (hS k) (Real.exp_nonneg _)
    _ ≤ _ := hT k

theorem length_large_of_cost (S : ResidueBoxSlice P q) {cost target : ℝ}
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + target) ≤ (P k : ℝ)) (k : K) :
    Real.exp target ≤ (S.length k : ℝ) := by
  calc
    _ = Real.exp (-cost) * Real.exp (cost + target) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-cost) * (P k : ℝ) :=
      mul_le_mul_of_nonneg_left (hP k) (Real.exp_nonneg _)
    _ ≤ _ := hS k

theorem stride_le_twice_exp_cost (S : ResidueBoxSlice P q) {cost : ℝ}
    (k : K) (hlen : 2 ≤ S.length k)
    (hS : Real.exp (-cost) * (P k : ℝ) ≤ S.length k) :
    (q : ℝ) ≤ 2 * Real.exp cost := by
  have hP : (0 : ℝ) < P k := by
    have h := S.inside k 0 (by omega)
    exact_mod_cast (show 0 < P k by omega)
  have hspan : (q : ℝ) * S.length k ≤ 2 * (P k : ℝ) := by
    exact_mod_cast S.stride_mul_length_le_twice k hlen
  have hmul := (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg q)).trans hspan
  have hq : (q : ℝ) * Real.exp (-cost) ≤ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hq (Real.exp_nonneg cost)
  simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] using h

variable [Fintype K] {X : Type*}

def pullbackIntegerFrame (S : ResidueBoxSlice P q) (frame : Option K × X → ℤ) :
    Option K × X → ℤ := fun i => match i.1 with
  | none => integerPhysicalSite (fun k => (S.start k : ℤ)) frame i.2
  | some k => (q : ℤ) * frame (some k, i.2)

theorem integerPhysicalSite_pullback (S : ResidueBoxSlice P q)
    (frame : Option K × X → ℤ) (u : K → ℤ) :
    integerPhysicalSite u (S.pullbackIntegerFrame frame) =
      integerPhysicalSite (fun k => (S.start k : ℤ) + (q : ℤ) * u k) frame := by
  funext x
  simp only [integerPhysicalSite, pullbackIntegerFrame, add_mul, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem pullback_normalized_slope_bound (S : ResidueBoxSlice P q)
    (hlen : ∀ k, 2 ≤ S.length k) (frame : Option K × X → ℤ)
    (N : X → ℕ) (C : K → ℝ)
    (hslope : ∀ k x, |(frame (some k, x) : ℝ) / N x| * P k ≤ C k)
    (k : K) (x : X) :
    |(S.pullbackIntegerFrame frame (some k, x) : ℝ) / N x| * S.length k ≤ 2 * C k := by
  have hspan : (q : ℝ) * S.length k ≤ 2 * (P k : ℝ) := by
    exact_mod_cast S.stride_mul_length_le_twice k (hlen k)
  calc
    _ = |(frame (some k, x) : ℝ) / N x| * ((q : ℝ) * S.length k) := by
      simp only [pullbackIntegerFrame, Int.cast_mul, Int.cast_natCast, mul_div_assoc,
        abs_mul, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ _)]
      ring
    _ ≤ |(frame (some k, x) : ℝ) / N x| * (2 * (P k : ℝ)) :=
      mul_le_mul_of_nonneg_left hspan (abs_nonneg _)
    _ = 2 * (|(frame (some k, x) : ℝ) / N x| * P k) := by ring
    _ ≤ 2 * C k := mul_le_mul_of_nonneg_left (hslope k x) (by norm_num)

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBoxObservation_mean {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) (hN : (integerBox N).Nonempty) (f : integerBox N → ℝ) :
    (𝔼 x ∈ integerBox N, f (integerBoxObservation N hN (fun i => (x i : ℝ)))) =
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).mean f := by
  have h := (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).fiberLaw_mean
    (fun x => integerBoxObservation N hN (fun i => (x.val i : ℝ))) f
  rw [integerBoxObservation_reference, FiniteProbabilityWeights.uniformFinset_mean
    (integerBox N) hN (fun x => f (integerBoxObservation N hN (fun i => (x i : ℝ))))] at h
  exact h.symm

theorem integerBoxObservation_complexMean {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) (hN : (integerBox N).Nonempty) (f : integerBox N → ℂ) :
    (𝔼 x ∈ integerBox N, f (integerBoxObservation N hN (fun i => (x i : ℝ)))) =
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).complexMean f := by
  have h := (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).fiberLaw_complexMean
    (fun x => integerBoxObservation N hN (fun i => (x.val i : ℝ))) f
  rw [integerBoxObservation_reference, FiniteProbabilityWeights.uniformFinset_complexMean
    (integerBox N) hN (fun x => f (integerBoxObservation N hN (fun i => (x i : ℝ))))] at h
  exact h.symm

end Erdos3

end

end OAI
