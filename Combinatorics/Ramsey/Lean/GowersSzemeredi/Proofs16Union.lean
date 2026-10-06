import GowersSzemeredi.Proofs16Basic
import GowersSzemeredi.Proofs16BaseCaseUnion
import GowersSzemeredi.ProofInfrastructure

/-!
# Auditing finite unions of multiply-linear relations

This file isolates the zero-iteration obstruction in the statement of
Lemma 16.8 and exports its proper-box union and sum closure.  A single globally multilinear graph is multiply linear with
iteration parameter zero, but the union of two distinct such graphs cannot be
covered by the one graph allowed by the same zero parameter.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma isMultilinear_const {N k : Nat} (c : ZMod N) :
    IsMultilinear (fun _ : Point N k => c) := by
  classical
  let e0 : Fin k -> Bool := fun _ => false
  refine ⟨fun e => if e = e0 then c else 0, ?_⟩
  intro x
  rw [Finset.sum_eq_single e0]
  · simp [e0]
  · intro e _he hne
    simp [hne]
  · simp

private lemma singleton_box_partition {N k : Nat} [NeZero N]
    (P : Box N k) : IsBoxPartition (fun _ : Fin 1 => P) P := by
  constructor
  · intro x
    simp
  · intro i j hij
    exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim

private lemma multiplyLinear_const_zero {N k : Nat} [NeZero N]
    (gamma : Real) (c : ZMod N) :
    MultiplyLinear gamma 0
      (partialGraph (Finset.univ : Finset (Point N k)) (fun _ => c)) := by
  intro theta htheta hthetaOne P hP
  refine ⟨1, 1, P.carrier, (fun _ : Fin 1 => P),
    (fun _ _ _ => c), Finset.Subset.rfl, ?_, singleton_box_partition P, (fun _ => hP), ?_, ?_, ?_, ?_⟩
  · have hcard : (0 : Real) <= P.carrier.card := by positivity
    nlinarith
  · simp
  · simp
  · intro j i
    exact isMultilinear_const c
  · intro j x hxQ hxH y hxy
    have hy : y = c := by
      rw [partialGraph, Finset.mem_image] at hxy
      obtain ⟨z, _hz, hzx⟩ := hxy
      exact (congrArg Prod.snd hzx).symm
    exact ⟨0, hy⟩

private def lemma168Gamma (i : Fin 2) :
    Finset (Point 2 1 × ZMod 2) :=
  partialGraph Finset.univ (fun _ => (i.val : ZMod 2))

private def lemma168Box : Box 2 1 where
  axis := fun _ => modInterval 2 0 1
  commonDiff := 1
  axis_step := by intro i; rfl

private def lemma168Point : Point 2 1 := fun _ => 0

private lemma lemma168Point_mem_box : lemma168Point ∈ lemma168Box.carrier := by
  classical
  simp [lemma168Point, lemma168Box, Box.carrier, modInterval, ModAP.carrier]

private lemma lemma168_pair_mem (x : Point 2 1) (i : Fin 2) :
    (x, (i.val : ZMod 2)) ∈ section16FinsetUnion lemma168Gamma := by
  classical
  rw [section16FinsetUnion, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [lemma168Gamma, partialGraph, Finset.mem_image]
  exact ⟨x, Finset.mem_univ x, rfl⟩

/-- The live Lemma 16.8 is false when its real iteration parameter `s` is
zero.  The faithful repair is to impose the positivity that the paper assumes
for this iteration count. -/
theorem lemma_16_8_zero_iteration_counterexample :
    ¬ lemma_16_8_without_positive_iteration := by
  intro h
  have hGamma : ∀ i, MultiplyLinear (1 : Real) 0 (lemma168Gamma i) := by
    intro i
    exact multiplyLinear_const_zero 1 (i.val : ZMod 2)
  have hunion : MultiplyLinear (1 : Real) ((2 : Real) * 0)
      (section16FinsetUnion lemma168Gamma) :=
    h.1 2 0 2 (1 : Real) 0 lemma168Gamma hGamma
  obtain ⟨M, q, H, Q, mu, hHP, hHcard, hpartition, hproper, hq, hwidth,
      hmultilinear, hcover⟩ := hunion (1 / 2 : Real) (by norm_num) (by norm_num) lemma168Box
      (by intro i; simp [lemma168Box, ModAP.IsProper, modInterval, ModAP.carrier])
  have hcarrierPos : (0 : Real) < lemma168Box.carrier.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨lemma168Point, lemma168Point_mem_box⟩
  have hHpos : 0 < H.card := by
    have hhalf : (0 : Real) < (1 - (1 / 2 : Real)) * lemma168Box.carrier.card := by
      positivity
    exact_mod_cast lt_of_lt_of_le hhalf hHcard
  obtain ⟨x, hxH⟩ := Finset.card_pos.mp hHpos
  have hxP : x ∈ lemma168Box.carrier := hHP hxH
  obtain ⟨j, hxQ⟩ := (hpartition.1 x).mp hxP
  obtain ⟨i0, hi0⟩ := hcover j x hxQ hxH 0 (lemma168_pair_mem x 0)
  obtain ⟨i1, hi1⟩ := hcover j x hxQ hxH 1 (lemma168_pair_mem x 1)
  have hqOne : q ≤ 1 := by
    simpa using hq
  have hi : i0 = i1 := by
    apply Fin.ext
    omega
  have hzeroOne : (0 : ZMod 2) = 1 := by
    rw [hi0, hi, ← hi1]
  norm_num at hzeroOne

private lemma multiplyLinear_empty_zero {N d : Nat} [NeZero N]
    (gamma : Real) :
    MultiplyLinear gamma 0 (∅ : Finset (Point N d × ZMod N)) := by
  intro theta htheta hthetaOne P hP
  refine ⟨1, 0, P.carrier, (fun _ : Fin 1 => P),
    (fun _ i => Fin.elim0 i), Finset.Subset.rfl, ?_,
    singleton_box_partition P, (fun _ => hP), ?_, ?_, ?_, ?_⟩
  · have hcard : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · simp [multipleQ, multipleC]
  · simp [multipleC]
  · intro j i
    exact Fin.elim0 i
  · intro j x hxQ hxH y hxy
    simp at hxy

private lemma multiplyLinearFunction_zero_zero {N d : Nat} [NeZero N]
    (gamma : Real) (B : Finset (Point N d)) :
    MultiplyLinearFunction gamma 0 B (fun _ => 0) := by
  intro theta htheta hthetaOne P hP
  refine ⟨1, 1, P.carrier, (fun _ : Fin 1 => P),
    (fun _ _ _ => 0), Finset.Subset.rfl, ?_, singleton_box_partition P, (fun _ => hP),
    ?_, ?_, ?_, ?_⟩
  · have hcard : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · simp [multipleQ, multipleC]
  · simp [multipleC]
  · intro j i
    exact isMultilinear_const 0
  · intro j x hxQ hxH y hxy
    have hy : y = 0 := by
      obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hxy
      exact (congrArg Prod.snd hz).symm
    exact ⟨0, hy⟩

/-- The repaired form of Gowers's Lemma 16.8. -/
theorem lemma_16_8_holds : lemma_16_8 := by
  constructor
  · intro N k r _ gamma s Gamma hs hGamma
    by_cases hr : r = 0
    · subst r
      simpa [section16FinsetUnion] using
        (multiplyLinear_empty_zero (N := N) (d := k + 1) gamma)
    · exact BaseCase.properMultiplyLinear_finsetUnion gamma s hs Gamma (Nat.pos_of_ne_zero hr) hGamma
  · intro N k r _ gamma s B phi hs hphi
    by_cases hr : r = 0
    · subst r
      simpa using (multiplyLinearFunction_zero_zero
        (N := N) (d := k + 1) gamma B)
    · exact BaseCase.properMultiplyLinear_fin_sum gamma s hs B phi (Nat.pos_of_ne_zero hr) hphi

end LeanProofs.GowersSzemeredi
