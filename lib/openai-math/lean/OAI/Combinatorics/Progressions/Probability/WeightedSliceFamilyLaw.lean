import OAI.Combinatorics.Progressions.Estimates.ProductMeanPullback
import OAI.Combinatorics.Progressions.Estimates.ProgressionCubeEmbedding
import OAI.Combinatorics.Progressions.Polynomial.UniformSlicePhaseLaw

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_pi_transport {n : ℕ} {X Y Z : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  induction n with
  | zero =>
      rw [complexMean_empty_tuple, complexMean_empty_tuple]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [complexMean_pi_fin_cons, complexMean_pi_fin_cons]
      simp only [dependent_fin_cons_map]
      calc
        _ = (p 0).complexMean (fun a => (pi (fun i : Fin n => q i.succ)).complexMean
            (fun y => f (Fin.cons (F 0 a) (fun i => G i.succ (y i))))) := by
          congr 1
          funext a
          exact ih (fun i => p i.succ) (fun i => q i.succ)
            (fun i => F i.succ) (fun i => G i.succ) (fun i => h i.succ) (fun z => f (Fin.cons (F 0 a) z))
        _ = _ := h 0 (fun z => (pi (fun i : Fin n => q i.succ)).complexMean
          (fun y => f (Fin.cons z (fun i => G i.succ (y i)))))

theorem mean_pi_transport {n : ℕ} {X Y Z : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℝ) :
    (pi p).mean (fun x => f (fun i => F i (x i))) =
      (pi q).mean (fun y => f (fun i => G i (y i))) := by
  have he := congrArg Complex.re (complexMean_pi_transport p q F G h (fun z => (f z : ℂ)))
  simpa only [complexMean_re, Complex.ofReal_re] using he

theorem complexMean_pi_transport_fintype {I : Type*} [Fintype I] [DecidableEq I]
    {X Y Z : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f' : (∀ j, Z (e j)) → ℂ := fun z => f ((Equiv.piCongrLeft Z e) z)
  have hp := productComplexMean_reindex p e
    (fun x => f' (fun j => F (e j) (x j)))
  have hq := productComplexMean_reindex q e
    (fun x => f' (fun j => G (e j) (x j)))
  have ht := complexMean_pi_transport (fun j => p (e j)) (fun j => q (e j))
    (fun j => F (e j)) (fun j => G (e j)) (fun j => h (e j)) f'
  have hcomp (z : ∀ i, Z i) : f' (fun j => z (e j)) = f z := by
    change f ((Equiv.piCongrLeft Z e) ((Equiv.piCongrLeft Z e).symm z)) = f z
    rw [Equiv.apply_symm_apply]
  calc
    _ = (pi p).complexMean (fun x => f' (fun j => F (e j) (x (e j)))) := by
      congr 1
      funext x
      exact (hcomp (fun i => F i (x i))).symm
    _ = (pi q).complexMean (fun x => f' (fun j => G (e j) (x (e j)))) :=
      hp.trans (ht.trans hq.symm)
    _ = _ := by
      congr 1
      funext x
      exact hcomp (fun i => G i (x i))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

theorem finiteImageMass_eq_of_complexMean {X Y Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Z]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (F : X → Z) (G : Y → Z)
    (h : ∀ f : Z → ℂ, p.complexMean (fun x => f (F x)) = q.complexMean (fun y => f (G y))) (z : Z) :
    finiteImageMass p F z = finiteImageMass q G z := by
  have he := congrArg Complex.re (h (fun t => if t = z then 1 else 0))
  simpa only [FiniteProbabilityWeights.complexMean_re, apply_ite, Complex.one_re, Complex.zero_re,
    finiteImageMass] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def zeroScalarCubeIntervalEquiv (α : Type*) [Fintype α]
    [DecidableEq α] [IsEmpty α] (L : ℕ) :
    ↥(integerScalarCubeSet α L) ≃ ↥(Finset.Ico (0 : ℤ) (L : ℤ)) where
  toFun x := by
    have h0 := ((mem_integerScalarCubeSet L x.val).mp x.property) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h0
    exact ⟨x.val none, Finset.mem_Ico.mpr h0⟩
  invFun z := by
    have hz := Finset.mem_Ico.mp z.property
    let x : IntegerScalarCubeBox α L := fun _ =>
      ⟨z.val, Finset.mem_Ico.mpr ⟨by omega, hz.2⟩⟩
    refine ⟨x, (mem_integerScalarCubeSet L x).mpr ?_⟩
    intro t
    have ht : t = ∅ := Subsingleton.elim _ _
    simpa only [ht, integerScalarCubeValue, Finset.sum_empty, add_zero] using hz
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    cases i with
    | none => rfl
    | some a => exact isEmptyElim a
  right_inv z := by apply Subtype.ext; rfl

theorem integerScalarCubeWeights_zero_mean (α : Type*) [Fintype α]
    [DecidableEq α] [IsEmpty α] (L : ℕ) (hL : 0 < L) (f : ℤ → ℝ) :
    (integerScalarCubeWeights α L hL).mean (fun x => f (x none : ℤ)) =
      (intervalUniformWeights 0 (L : ℤ) (by exact_mod_cast hL)).mean
        (fun x => f x.val) := by
  rw [integerScalarCubeWeights_mean, intervalUniformWeights_mean]
  exact Fintype.expect_equiv (zeroScalarCubeIntervalEquiv α L) _ _ (fun _ => rfl)

theorem integerScalarCubeWeights_zero_complexMean (α : Type*) [Fintype α]
    [DecidableEq α] [IsEmpty α] (L : ℕ) (hL : 0 < L) (f : ℤ → ℂ) :
    (integerScalarCubeWeights α L hL).complexMean (fun x => f (x none : ℤ)) =
      (intervalUniformWeights 0 (L : ℤ) (by exact_mod_cast hL)).complexMean
        (fun x => f x.val) := by
  apply Complex.ext
  · simpa only [FiniteProbabilityWeights.complexMean_re] using
      integerScalarCubeWeights_zero_mean α L hL (fun x => (f x).re)
  · simpa only [FiniteProbabilityWeights.complexMean_im] using
      integerScalarCubeWeights_zero_mean α L hL (fun x => (f x).im)

variable {D α : Type*} [Fintype D] [DecidableEq D]
variable [Fintype α] [DecidableEq α] [IsEmpty α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)

omit [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] in

theorem principalTupleIntegers_zero (y : PrincipalIntegerTuples B h α L)
    (a : JointBlockParameter B h α) :
    principalTupleIntegers y a = (y ⟨a.1, a.2.1, a.2.2.1⟩ none : ℤ) := by
  unfold principalTupleIntegers
  have ha : a.2.2.2 = none := by
    cases ha : a.2.2.2 with
    | none => rfl
    | some x => exact isEmptyElim x
  rw [ha]

theorem principalTupleWeights_zero_complexMean (f : (PrincipalTupleIndex B h → ℤ) → ℂ) :
    (principalTupleWeights (α := α) B h L hL).complexMean
      (fun y => f (fun j => (y j none : ℤ))) =
      (integerBoxUniformWeights (fun _ => 0) (fun j => (L j : ℤ))
        (fun j => by exact_mod_cast hL j)).complexMean
        (fun y => f (fun j => (y j : ℤ))) := by
  exact FiniteProbabilityWeights.complexMean_pi_transport_fintype
    (fun j => integerScalarCubeWeights α (L j) (hL j))
    (fun j => intervalUniformWeights 0 (L j : ℤ) (by exact_mod_cast hL j))
    (fun _ x => (x none : ℤ)) (fun _ x => (x : ℤ))
    (fun j g => integerScalarCubeWeights_zero_complexMean α (L j) (hL j) g) f

theorem principalTupleWeights_zero_mean (f : (PrincipalTupleIndex B h → ℤ) → ℝ) :
    (principalTupleWeights (α := α) B h L hL).mean
      (fun y => f (fun j => (y j none : ℤ))) =
      (integerBoxUniformWeights (fun _ => 0) (fun j => (L j : ℤ))
        (fun j => by exact_mod_cast hL j)).mean
        (fun y => f (fun j => (y j : ℤ))) := by
  have he := congrArg Complex.re
    (principalTupleWeights_zero_complexMean (α := α) B h L hL (fun z => (f z : ℂ)))
  simpa only [FiniteProbabilityWeights.complexMean_re, Complex.ofReal_re] using he

theorem principalTupleWeights_zero_law :
    (principalTupleWeights (α := α) B h L hL).toPMF.map
      (fun y => fun j => (y j none : ℤ)) =
      (integerBoxUniformWeights (fun _ => 0) (fun j => (L j : ℤ))
        (fun j => by exact_mod_cast hL j)).toPMF.map
        (fun y => fun j => (y j : ℤ)) := by
  ext z
  apply ENNReal.ofReal_toReal (PMF.apply_ne_top _ _) |>.symm.trans
  apply Eq.trans _ (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _))
  congr 1
  rw [FiniteProbabilityWeights.toPMF_map_toReal,
    FiniteProbabilityWeights.toPMF_map_toReal]
  exact principalTupleWeights_zero_mean (α := α) B h L hL
    (fun y => @ite ℝ (y = z) (Classical.propDecidable _) 1 0)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem progressionSupportedCube_nonempty (q m H : ℕ) (c : ℤ) (hL : 0 < m * H) (hm : 0 < m) :
    Nonempty (SupportedCube q (integerProgressionSupport c (m : ℤ) H : Set ℤ)) := by
  have hc : c ∈ integerProgressionSupport c (m : ℤ) H := by
    apply (mem_integerProgressionSupport_iff c m H hm c).mpr
    refine ⟨le_rfl, ?_, rfl⟩
    have hL' : (0 : ℤ) < (m * H : ℕ) := by exact_mod_cast hL
    omega
  refine ⟨⟨(fun _ => 0, c), fun ω => ?_⟩⟩
  simpa only [cubeShift, ite_self, Finset.sum_const_zero, add_zero, Finset.mem_coe] using hc

noncomputable def uniformProgressionCubeWeights (q m H : ℕ) (c : ℤ) (hL : 0 < m * H) (hm : 0 < m) :
    FiniteProbabilityWeights (SupportedCube q (integerProgressionSupport c (m : ℤ) H : Set ℤ)) := by
  letI := progressionSupportedCube_nonempty q m H c hL hm
  exact FiniteProbabilityWeights.uniform _

theorem uniformProgressionCubeWeights_complexMean (q m H : ℕ) (c : ℤ) (hL : 0 < m * H) (hm : 0 < m)
    (F : SupportedCube q (integerProgressionSupport c (m : ℤ) H : Set ℤ) → ℂ) :
    (uniformProgressionCubeWeights q m H c hL hm).complexMean F = 𝔼 x, F x := by
  let := progressionSupportedCube_nonempty q m H c hL hm
  exact FiniteProbabilityWeights.uniform_complexMean F

theorem progressionCubeFamily_complexMean {g : ℕ} (q : ℕ) (m H : Fin g → ℕ) (c : Fin g → ℤ)
    (hL : ∀ j, 0 < m j * H j) (hm : ∀ j, 0 < m j) (hsize : ∀ j, (q + 1) * m j ≤ m j * H j)
    (F : (Fin g → Option (Fin q) → ℤ) → ℂ) :
    (FiniteProbabilityWeights.pi (fun j =>
      (normalizedProgressionCubeSource q (m j) (H j) (c j) (hL j) (hm j) (hsize j)).source)).complexMean
        (fun x => F (fun j => affineIntegerCubeCoordinates (cubeRootOffset (c j)) (fun _ => 1)
          (fun i => (x j i : ℤ)))) =
    (FiniteProbabilityWeights.pi (fun j =>
      uniformProgressionCubeWeights q (m j) (H j) (c j) (hL j) (hm j))).complexMean
        (fun x => F (fun j => supportedCubeCoordinates (x j).val)) := by
  refine FiniteProbabilityWeights.complexMean_pi_transport
    (fun j => (normalizedProgressionCubeSource q (m j) (H j) (c j) (hL j) (hm j) (hsize j)).source)
    (fun j => uniformProgressionCubeWeights q (m j) (H j) (c j) (hL j) (hm j))
    (fun j x => affineIntegerCubeCoordinates (cubeRootOffset (c j)) (fun _ => 1) (fun i => (x i : ℤ)))
    (fun _ x => supportedCubeCoordinates x.val) ?_ F
  intro j f
  rw [uniformProgressionCubeWeights_complexMean]
  exact normalizedProgressionCubeSource_complexMean q (m j) (H j) (c j) (hL j) (hm j) (hsize j) f

theorem progressionCubeBlocks_complexMean {b g : ℕ} (q : ℕ)
    (m H : Fin b → Fin g → ℕ) (c : Fin b → Fin g → ℤ)
    (hL : ∀ a j, 0 < m a j * H a j) (hm : ∀ a j, 0 < m a j)
    (hsize : ∀ a j, (q + 1) * m a j ≤ m a j * H a j)
    (F : (Fin b → Fin g → Option (Fin q) → ℤ) → ℂ) :
    (FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j =>
      (normalizedProgressionCubeSource q (m a j) (H a j) (c a j) (hL a j) (hm a j) (hsize a j)).source))).complexMean
        (fun x => F (fun a j => affineIntegerCubeCoordinates (cubeRootOffset (c a j)) (fun _ => 1)
          (fun i => (x a j i : ℤ)))) =
    (FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j =>
      uniformProgressionCubeWeights q (m a j) (H a j) (c a j) (hL a j) (hm a j)))).complexMean
        (fun x => F (fun a j => supportedCubeCoordinates (x a j).val)) := by
  refine FiniteProbabilityWeights.complexMean_pi_transport
    (fun a => FiniteProbabilityWeights.pi (fun j =>
      (normalizedProgressionCubeSource q (m a j) (H a j) (c a j) (hL a j) (hm a j) (hsize a j)).source))
    (fun a => FiniteProbabilityWeights.pi (fun j =>
      uniformProgressionCubeWeights q (m a j) (H a j) (c a j) (hL a j) (hm a j)))
    (fun a x j => affineIntegerCubeCoordinates (cubeRootOffset (c a j)) (fun _ => 1) (fun i => (x j i : ℤ)))
    (fun _ x j => supportedCubeCoordinates (x j).val) ?_ F
  intro a f
  exact progressionCubeFamily_complexMean q (m a) (H a) (c a) (hL a) (hm a) (hsize a) f

theorem progressionCubeBlocks_imageMass {b g : ℕ} {Z : Type*} [DecidableEq Z] (q : ℕ)
    (m H : Fin b → Fin g → ℕ) (c : Fin b → Fin g → ℤ)
    (hL : ∀ a j, 0 < m a j * H a j) (hm : ∀ a j, 0 < m a j)
    (hsize : ∀ a j, (q + 1) * m a j ≤ m a j * H a j)
    (Y : (Fin b → Fin g → Option (Fin q) → ℤ) → Z) (z : Z) :
    finiteImageMass
      (FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j =>
        (normalizedProgressionCubeSource q (m a j) (H a j) (c a j) (hL a j) (hm a j) (hsize a j)).source)))
      (fun x => Y (fun a j => affineIntegerCubeCoordinates (cubeRootOffset (c a j)) (fun _ => 1)
        (fun i => (x a j i : ℤ)))) z =
    finiteImageMass
      (FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j =>
        uniformProgressionCubeWeights q (m a j) (H a j) (c a j) (hL a j) (hm a j))))
      (fun x => Y (fun a j => supportedCubeCoordinates (x a j).val)) z := by
  apply finiteImageMass_eq_of_complexMean
  intro f
  exact progressionCubeBlocks_complexMean q m H c hL hm hsize (fun x => f (Y x))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem weightedSliceFamily_complexMean {g q : ℕ}
    (s : Fin g → NormalizedScalarCubeSource (Fin q)) (root : Fin g → ℤ)
    (F : (Fin g → Option (Fin q) → ℤ) → ℂ) :
    (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
        (fun x => F (fun j => shiftScalarCube (root j) (fun i => (x j i : ℤ)))) =
      (FiniteProbabilityWeights.pi (fun j => (s j).sliceWeights (root j))).complexMean
        (fun x => F (fun j => supportedCubeCoordinates (x j).val.val)) := by
  exact FiniteProbabilityWeights.complexMean_pi_transport
    (fun j => (s j).source) (fun j => (s j).sliceWeights (root j))
    (fun j x => shiftScalarCube (root j) (fun i => (x i : ℤ)))
    (fun _ x => supportedCubeCoordinates x.val.val)
    (fun j f => (s j).source_slice_complexMean (root j) f) F

theorem weightedSliceBlocks_complexMean {b g q : ℕ}
    (s : Fin b → Fin g → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin g → ℤ)
    (F : (Fin b → Fin g → Option (Fin q) → ℤ) → ℂ) :
    (FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j => (s a j).source))).complexMean
        (fun x => F (fun a j => shiftScalarCube (root a j) (fun i => (x a j i : ℤ)))) =
      (FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi
        (fun j => (s a j).sliceWeights (root a j)))).complexMean
        (fun x => F (fun a j => supportedCubeCoordinates (x a j).val.val)) := by
  exact FiniteProbabilityWeights.complexMean_pi_transport
    (fun a => FiniteProbabilityWeights.pi (fun j => (s a j).source))
    (fun a => FiniteProbabilityWeights.pi (fun j => (s a j).sliceWeights (root a j)))
    (fun a x j => shiftScalarCube (root a j) (fun i => (x j i : ℤ)))
    (fun _ x j => supportedCubeCoordinates (x j).val.val)
    (fun a f => weightedSliceFamily_complexMean (s a) (root a) f) F

noncomputable def moderateSliceWeights {g q : ℕ} (c : NormalizedScalarCubeSource Empty)
    (s : Fin g → NormalizedScalarCubeSource (Fin q)) (root : Fin g → ℤ) :
    FiniteProbabilityWeights (c.CoefficientDomain × (∀ j, (s j).SliceDomain (root j))) :=
  c.coefficientWeights.prod (FiniteProbabilityWeights.pi (fun j => (s j).sliceWeights (root j)))

theorem moderateSlice_complexMean {g q : ℕ} (c : NormalizedScalarCubeSource Empty)
    (s : Fin g → NormalizedScalarCubeSource (Fin q)) (root : Fin g → ℤ)
    (F : (ℤ × (Fin g → Option (Fin q) → ℤ)) → ℂ) :
    (c.source.prod (FiniteProbabilityWeights.pi (fun j => (s j).source))).complexMean
        (fun x => F ((x.1 none : ℤ), fun j => shiftScalarCube (root j) (fun i => (x.2 j i : ℤ)))) =
      (moderateSliceWeights c s root).complexMean
        (fun x => F ((x.1 : ℤ), fun j => supportedCubeCoordinates (x.2 j).val.val)) := by
  rw [moderateSliceWeights, FiniteProbabilityWeights.complexMean_prod, FiniteProbabilityWeights.complexMean_prod]
  calc
    _ = c.source.complexMean (fun z =>
        (FiniteProbabilityWeights.pi (fun j => (s j).sliceWeights (root j))).complexMean
          (fun y => F ((z none : ℤ), fun j => supportedCubeCoordinates (y j).val.val))) := by
      congr 1
      funext z
      exact weightedSliceFamily_complexMean s root (fun y => F ((z none : ℤ), y))
    _ = _ := c.source_coefficient_complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (s j).sliceWeights (root j))).complexMean
        (fun y => F (z, fun j => supportedCubeCoordinates (y j).val.val)))

theorem moderateSliceBlocks_complexMean {b g q : ℕ} (c : Fin b → NormalizedScalarCubeSource Empty)
    (s : Fin b → Fin g → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin g → ℤ)
    (F : (Fin b → ℤ × (Fin g → Option (Fin q) → ℤ)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun a => (c a).source.prod
      (FiniteProbabilityWeights.pi (fun j => (s a j).source)))).complexMean
        (fun x => F (fun a => ((x a).1 none, fun j => shiftScalarCube (root a j) (fun i => ((x a).2 j i : ℤ))))) =
      (FiniteProbabilityWeights.pi (fun a => moderateSliceWeights (c a) (s a) (root a))).complexMean
        (fun x => F (fun a => (((x a).1 : ℤ), fun j => supportedCubeCoordinates ((x a).2 j).val.val))) := by
  exact FiniteProbabilityWeights.complexMean_pi_transport
    (fun a => (c a).source.prod (FiniteProbabilityWeights.pi (fun j => (s a j).source)))
    (fun a => moderateSliceWeights (c a) (s a) (root a))
    (fun a x => ((x.1 none : ℤ), fun j => shiftScalarCube (root a j) (fun i => (x.2 j i : ℤ))))
    (fun _ x => ((x.1 : ℤ), fun j => supportedCubeCoordinates (x.2 j).val.val))
    (fun a f => moderateSlice_complexMean (c a) (s a) (root a) f) F

end Erdos3

end

end OAI
