import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxControl

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem physical_truncation_restore_difference
    {X I ι : Type*} [Fintype X] [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
    (p : FiniteProbabilityWeights X) (location : X → I → ℤ) (w : X → ℝ)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (b : ℕ) (h g : (I → ℤ) → ℝ)
    (hh : ∀ x ∉ translatedIntegerBox lo N, h x = 0)
    (hg : ∀ x ∉ translatedIntegerBox lo N, g x = 0)
    {r epsilon R : ℝ} (hr : 0 ≤ r)
    (heh : |p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b h (location x))| ≤ epsilon)
    (heg : |p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b g (location x))| ≤ epsilon)
    (hlow : p.mean (fun x => w x *
      (physicalBoxTruncation lo N P hpos q b h (location x) -
        r * physicalBoxTruncation lo N P hpos q b g (location x))) ≤ R) :
    p.mean (fun x => w x * (h (location x) - r * g (location x))) ≤ R + (1 + r) * epsilon := by
  have hid : p.mean (fun x => w x * (h (location x) - r * g (location x))) =
      p.mean (fun x => w x * (physicalBoxTruncation lo N P hpos q b h (location x) -
        r * physicalBoxTruncation lo N P hpos q b g (location x))) +
      p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b h (location x)) -
      r * p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b g (location x)) := by
    rw [← p.mean_add, ← p.mean_const_mul, ← p.mean_sub]
    congr 1
    funext x
    rw [physicalBoxResidual_eq_sub lo N P hpos q b h hh,
      physicalBoxResidual_eq_sub lo N P hpos q b g hg]
    ring
  rw [hid]
  have hhup := (abs_le.mp heh).2
  have hglow := mul_le_mul_of_nonneg_left (abs_le.mp heg).1 hr
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem physicalBoxTruncation_congr_on_box
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f g : (I → ℤ) → ℝ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    physicalBoxTruncation lo N P hpos q b f = physicalBoxTruncation lo N P hpos q b g := by
  funext x
  unfold physicalBoxTruncation
  split_ifs with hx
  · exact congrFun (residuePhysicalTruncation_congr_on_box _ _ _ _ _ q b f g
      (fun z hz => hfg z (physicalBoxCell_subset lo N P hstep hpos _ hz))) x
  · rfl

theorem physicalBoxResidual_congr_on_box
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f g : (I → ℤ) → ℝ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    physicalBoxResidual lo N P hpos q b f = physicalBoxResidual lo N P hpos q b g := by
  funext x
  unfold physicalBoxResidual
  rw [physicalBoxTruncation_congr_on_box lo N P hstep hpos q b f g hfg]
  split_ifs with hx
  · rw [hfg x hx]
  · rfl

theorem physicalBoxTruncation_zeroExtend
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) :
    physicalBoxTruncation lo N P hpos q b (realZeroExtendFinset (translatedIntegerBox lo N) f) =
      physicalBoxTruncation lo N P hpos q b f :=
  physicalBoxTruncation_congr_on_box lo N P hstep hpos q b _ f
    (fun _ hx => realZeroExtendFinset_on _ f hx)

theorem physicalBoxResidual_zeroExtend
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) :
    physicalBoxResidual lo N P hpos q b (realZeroExtendFinset (translatedIntegerBox lo N) f) =
      physicalBoxResidual lo N P hpos q b f :=
  physicalBoxResidual_congr_on_box lo N P hstep hpos q b _ f
    (fun _ hx => realZeroExtendFinset_on _ f hx)

theorem physical_zero_extension_restore_difference
    {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (location : X → I → ℤ) (w : X → ℝ)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (h g : (I → ℤ) → ℝ)
    {r epsilon R : ℝ} (hr : 0 ≤ r)
    (heh : |p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b h (location x))| ≤ epsilon)
    (heg : |p.mean (fun x => w x * physicalBoxResidual lo N P hpos q b g (location x))| ≤ epsilon)
    (hlow : p.mean (fun x => w x *
      (physicalBoxTruncation lo N P hpos q b h (location x) -
        r * physicalBoxTruncation lo N P hpos q b g (location x))) ≤ R) :
    p.mean (fun x => w x *
      (realZeroExtendFinset (translatedIntegerBox lo N) h (location x) -
        r * realZeroExtendFinset (translatedIntegerBox lo N) g (location x))) ≤ R + (1 + r) * epsilon := by
  apply physical_truncation_restore_difference p location w lo N P hpos q b _ _
    (fun _ hx => realZeroExtendFinset_off _ h hx)
    (fun _ hx => realZeroExtendFinset_off _ g hx) hr
  · simpa only [physicalBoxResidual_zeroExtend lo N P hstep hpos q b h] using heh
  · simpa only [physicalBoxResidual_zeroExtend lo N P hstep hpos q b g] using heg
  · simpa only [physicalBoxTruncation_zeroExtend lo N P hstep hpos q b h,
      physicalBoxTruncation_zeroExtend lo N P hstep hpos q b g] using hlow

end Erdos3

end

end OAI
