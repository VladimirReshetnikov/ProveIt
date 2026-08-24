import GowersSzemeredi.Proofs14Arrangements
import Mathlib.Analysis.MeanInequalities

/-!
# Higher moments of respected general arrangements

This module proves Lemma 14.7.  For each common side vector, we form the
Fourier transform of the weighted collection of constituent cubes.  Its
fourth and sixteenth moments count respected `2`- and `8`-arrangements,
respectively.  Parseval and the interpolation inequality of Lemma 9.1 then
give the claimed seventh-power lower bound.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

local instance cor147PropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private abbrev cor147Atom (N k : Nat) := Point N k × ZMod N

private def cor147CubeIn {N k : Nat}
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (z : cor147Atom N k) : Prop :=
  ∀ e, appendCoordinate (AxisCube.vertex (z.1, h) e) z.2 ∈ B

private def cor147CubeValue {N k : Nat} [NeZero N]
  (phi : Point N (k + 1) → ZMod N) (h : Point N k)
    (z : cor147Atom N k) : ZMod N :=
  ∑ e : Fin k → Bool, (-1 : ZMod N) ^ boolWeight e *
    phi (appendCoordinate (AxisCube.vertex (z.1, h) e) z.2)

private noncomputable def cor147Phase {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (u x : ZMod N) : Complex := by
  classical
  exact ∑ y : Point N k,
    if cor147CubeIn B h (y, x) then
      exponential (cor147CubeValue phi h (y, x) * u)
    else 0

@[simp] private lemma cor147_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma cor147_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

@[simp] private lemma cor147_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact (ZMod.stdAddChar (N := N)).norm_apply x

private lemma cor147_ofReal_norm_even_pow (z : Complex) (d : Nat) :
    (((‖z‖ ^ (2 * d) : Real)) : Complex) = z ^ d * star z ^ d := by
  calc
    (((‖z‖ ^ (2 * d) : Real)) : Complex) =
        (((‖z‖ ^ 2 : Real)) : Complex) ^ d := by
      rw [← Complex.ofReal_pow, ← pow_mul]
    _ = (z * star z) ^ d := by
      congr 1
      rw [Complex.star_def, Complex.mul_conj']
      norm_cast
    _ = z ^ d * star z ^ d := by rw [mul_pow]

private def cor147PairEquiv (d : Nat) (G : Type*) :
    ((Fin d → G) × (Fin d → G)) ≃ (Fin (2 * d) → G) :=
  (Fin.appendEquiv d d).trans
    ((finCongr (Nat.two_mul d).symm).arrowCongr (Equiv.refl G))

private def cor147LeftIndex (d : Nat) (i : Fin d) : Fin (2 * d) :=
  Fin.cast (Nat.two_mul d).symm (Fin.castAdd d i)

private def cor147RightIndex (d : Nat) (i : Fin d) : Fin (2 * d) :=
  Fin.cast (Nat.two_mul d).symm (Fin.natAdd d i)

@[simp] private lemma cor147_pairEquiv_left (d : Nat) (G : Type*)
    (a b : Fin d → G) (i : Fin d) :
    cor147PairEquiv d G (a, b) (cor147LeftIndex d i) = a i := by
  simp [cor147PairEquiv, cor147LeftIndex]

@[simp] private lemma cor147_pairEquiv_right (d : Nat) (G : Type*)
    (a b : Fin d → G) (i : Fin d) :
    cor147PairEquiv d G (a, b) (cor147RightIndex d i) = b i := by
  change Fin.append a b (Fin.natAdd d i) = b i
  exact Fin.append_right a b i

private lemma cor147_leftIndex_mem (d : Nat) (i : Fin d) :
    (cor147LeftIndex d i : Nat) < d := by
  simp [cor147LeftIndex]

private lemma cor147_rightIndex_mem (d : Nat) (i : Fin d) :
    d ≤ (cor147RightIndex d i : Nat) := by
  simp [cor147RightIndex]

private lemma cor147_leftIndex_injective (d : Nat) :
    Function.Injective (cor147LeftIndex d) := by
  intro i j hij
  apply Fin.ext
  simpa [cor147LeftIndex] using congrArg Fin.val hij

private lemma cor147_rightIndex_injective (d : Nat) :
    Function.Injective (cor147RightIndex d) := by
  intro i j hij
  apply Fin.ext
  simpa [cor147RightIndex] using congrArg Fin.val hij

private lemma cor147_leftIndex_surj (d : Nat) (j : Fin (2 * d))
    (hj : (j : Nat) < d) :
    ∃ i : Fin d, cor147LeftIndex d i = j := by
  refine ⟨⟨j, hj⟩, ?_⟩
  apply Fin.ext
  simp [cor147LeftIndex]

private lemma cor147_rightIndex_surj (d : Nat) (j : Fin (2 * d))
    (hj : d ≤ (j : Nat)) :
    ∃ i : Fin d, cor147RightIndex d i = j := by
  have hjlt : (j : Nat) < d + d := by
    simpa [Nat.two_mul] using j.isLt
  refine ⟨⟨(j : Nat) - d, by omega⟩, ?_⟩
  apply Fin.ext
  simp [cor147RightIndex]
  omega

private lemma cor147_sum_left {G : Type*} [AddCommMonoid G] (d : Nat)
    (a b : Fin d → G) :
    (Finset.univ.filter (fun j : Fin (2 * d) ↦ (j : Nat) < d)).sum
        (cor147PairEquiv d G (a, b)) = ∑ i, a i := by
  symm
  apply Finset.sum_bij (fun i _ ↦ cor147LeftIndex d i)
  · intro i _
    simp [cor147_leftIndex_mem]
  · intro i _ j _ hij
    exact cor147_leftIndex_injective d hij
  · intro j hj
    have hjlt : (j : Nat) < d := (Finset.mem_filter.mp hj).2
    obtain ⟨i, hi⟩ := cor147_leftIndex_surj d j hjlt
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    exact (cor147_pairEquiv_left d G a b i).symm

private lemma cor147_sum_right {G : Type*} [AddCommMonoid G] (d : Nat)
    (a b : Fin d → G) :
    (Finset.univ.filter (fun j : Fin (2 * d) ↦ d ≤ (j : Nat))).sum
        (cor147PairEquiv d G (a, b)) = ∑ i, b i := by
  symm
  apply Finset.sum_bij (fun i _ ↦ cor147RightIndex d i)
  · intro i _
    simp [cor147_rightIndex_mem]
  · intro i _ j _ hij
    exact cor147_rightIndex_injective d hij
  · intro j hj
    have hjge : d ≤ (j : Nat) := (Finset.mem_filter.mp hj).2
    obtain ⟨i, hi⟩ := cor147_rightIndex_surj d j hjge
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    exact (cor147_pairEquiv_right d G a b i).symm

private lemma cor147_pairEquiv_comp {G H : Type*} (d : Nat)
    (f : G → H) (a b : Fin d → G) (j : Fin (2 * d)) :
    f (cor147PairEquiv d G (a, b) j) =
      cor147PairEquiv d H (f ∘ a, f ∘ b) j := by
  by_cases hj : (j : Nat) < d
  · obtain ⟨i, rfl⟩ := cor147_leftIndex_surj d j hj
    simp
  · obtain ⟨i, rfl⟩ := cor147_rightIndex_surj d j (by omega)
    simp

private lemma cor147_sum_left_comp {G H : Type*} [AddCommMonoid H]
    (d : Nat) (f : G → H) (a b : Fin d → G) :
    (Finset.univ.filter (fun j : Fin (2 * d) ↦ (j : Nat) < d)).sum
        (fun j ↦ f (cor147PairEquiv d G (a, b) j)) =
      ∑ i, f (a i) := by
  calc
    _ = (Finset.univ.filter (fun j : Fin (2 * d) ↦ (j : Nat) < d)).sum
        (cor147PairEquiv d H (f ∘ a, f ∘ b)) := by
          apply Finset.sum_congr rfl
          intro j _
          exact cor147_pairEquiv_comp d f a b j
    _ = ∑ i, f (a i) := by
          simpa [Function.comp_apply] using
            cor147_sum_left (G := H) d (f ∘ a) (f ∘ b)

private lemma cor147_sum_right_comp {G H : Type*} [AddCommMonoid H]
    (d : Nat) (f : G → H) (a b : Fin d → G) :
    (Finset.univ.filter (fun j : Fin (2 * d) ↦ d ≤ (j : Nat))).sum
        (fun j ↦ f (cor147PairEquiv d G (a, b) j)) =
      ∑ i, f (b i) := by
  calc
    _ = (Finset.univ.filter (fun j : Fin (2 * d) ↦ d ≤ (j : Nat))).sum
        (cor147PairEquiv d H (f ∘ a, f ∘ b)) := by
          apply Finset.sum_congr rfl
          intro j _
          exact cor147_pairEquiv_comp d f a b j
    _ = ∑ i, f (b i) := by
          simpa [Function.comp_apply] using
            cor147_sum_right (G := H) d (f ∘ a) (f ∘ b)

private lemma cor147_all_pair_iff {G : Type*} (d : Nat) (P : G → Prop)
    (a b : Fin d → G) :
    (∀ j, P (cor147PairEquiv d G (a, b) j)) ↔
      (∀ i, P (a i)) ∧ ∀ i, P (b i) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa using h (cor147LeftIndex d i)
    · intro i
      simpa using h (cor147RightIndex d i)
  · rintro ⟨ha, hb⟩ j
    by_cases hj : (j : Nat) < d
    · obtain ⟨i, rfl⟩ := cor147_leftIndex_surj d j hj
      simpa using ha i
    · obtain ⟨i, rfl⟩ := cor147_rightIndex_surj d j (by omega)
      simpa using hb i

private abbrev cor147PairFamily (N k d : Nat) :=
  (Fin d → cor147Atom N k) × (Fin d → cor147Atom N k)

private def cor147Good {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (p : cor147PairFamily N k d) : Prop :=
  (∀ i, cor147CubeIn B h (p.1 i)) ∧
  (∀ i, cor147CubeIn B h (p.2 i)) ∧
  (∑ i, (p.1 i).2) = ∑ i, (p.2 i).2 ∧
  (∑ i, cor147CubeValue phi h (p.1 i)) =
    ∑ i, cor147CubeValue phi h (p.2 i)

private def cor147ArrangementEquiv (N k d : Nat) :
    (Point N k × cor147PairFamily N k d) ≃ GeneralArrangement N k d :=
  (Equiv.refl (Point N k)).prodCongr
    ((cor147PairEquiv d (cor147Atom N k)).trans
      (Equiv.arrowProdEquivProdArrow (Fin (2 * d))
        (fun _ ↦ Point N k) (fun _ ↦ ZMod N)))

@[simp] private lemma cor147_arrangementEquiv_side {N k d : Nat}
    (h : Point N k) (p : cor147PairFamily N k d) :
    (cor147ArrangementEquiv N k d (h, p)).side = h := rfl

@[simp] private lemma cor147_arrangementEquiv_base {N k d : Nat}
    (h : Point N k) (p : cor147PairFamily N k d) (j : Fin (2 * d)) :
    (cor147ArrangementEquiv N k d (h, p)).base j =
      (cor147PairEquiv d (cor147Atom N k) p j).1 := rfl

@[simp] private lemma cor147_arrangementEquiv_crossSection {N k d : Nat}
    (h : Point N k) (p : cor147PairFamily N k d) (j : Fin (2 * d)) :
    (cor147ArrangementEquiv N k d (h, p)).crossSection j =
      (cor147PairEquiv d (cor147Atom N k) p j).2 := rfl

private lemma cor147_arrangement_vertex {N k d : Nat}
    (h : Point N k) (p : cor147PairFamily N k d)
    (e : Fin k → Bool) (j : Fin (2 * d)) :
    (cor147ArrangementEquiv N k d (h, p)).vertex e j =
      appendCoordinate
        (AxisCube.vertex
          ((cor147PairEquiv d (cor147Atom N k) p j).1, h) e)
        (cor147PairEquiv d (cor147Atom N k) p j).2 := by
  rfl

private lemma cor147_arrangement_cubeValue {N k d : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (h : Point N k)
    (p : cor147PairFamily N k d) (j : Fin (2 * d)) :
    (cor147ArrangementEquiv N k d (h, p)).cubeValue phi j =
      cor147CubeValue phi h (cor147PairEquiv d (cor147Atom N k) p j) := by
  rfl

private lemma cor147_good_iff_arrangement {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (p : cor147PairFamily N k d) :
    cor147Good B phi h p ↔
      (cor147ArrangementEquiv N k d (h, p)).IsIn B ∧
        (cor147ArrangementEquiv N k d (h, p)).IsRespected phi := by
  have hmem :
      (∀ (e : Fin k → Bool) (j : Fin (2 * d)),
        (cor147ArrangementEquiv N k d (h, p)).vertex e j ∈ B) ↔
        ((∀ i, cor147CubeIn B h (p.1 i)) ∧
          ∀ i, cor147CubeIn B h (p.2 i)) := by
    rw [forall_comm]
    change (∀ j, cor147CubeIn B h
      (cor147PairEquiv d (cor147Atom N k) p j)) ↔ _
    exact cor147_all_pair_iff d (cor147CubeIn B h) p.1 p.2
  have hcross :
      (Finset.univ.filter (fun j : Fin (2 * d) ↦ (j : Nat) < d)).sum
          (cor147ArrangementEquiv N k d (h, p)).crossSection =
        (Finset.univ.filter (fun j : Fin (2 * d) ↦ d ≤ (j : Nat))).sum
          (cor147ArrangementEquiv N k d (h, p)).crossSection ↔
      (∑ i, (p.1 i).2) = ∑ i, (p.2 i).2 := by
    simp only [cor147_arrangementEquiv_crossSection]
    rw [cor147_sum_left_comp d (fun z : cor147Atom N k ↦ z.2) p.1 p.2,
      cor147_sum_right_comp d (fun z : cor147Atom N k ↦ z.2) p.1 p.2]
  have hvalue :
      (Finset.univ.filter (fun j : Fin (2 * d) ↦ (j : Nat) < d)).sum
          (fun j ↦ (cor147ArrangementEquiv N k d (h, p)).cubeValue phi j) =
        (Finset.univ.filter (fun j : Fin (2 * d) ↦ d ≤ (j : Nat))).sum
          (fun j ↦ (cor147ArrangementEquiv N k d (h, p)).cubeValue phi j) ↔
      (∑ i, cor147CubeValue phi h (p.1 i)) =
        ∑ i, cor147CubeValue phi h (p.2 i) := by
    simp only [cor147_arrangement_cubeValue]
    rw [cor147_sum_left_comp d (cor147CubeValue phi h) p.1 p.2,
      cor147_sum_right_comp d (cor147CubeValue phi h) p.1 p.2]
  unfold cor147Good GeneralArrangement.IsIn GeneralArrangement.IsRespected
    IsAdditiveTuple
  rw [hcross, hmem, hvalue]
  aesop

private lemma cor147_good_count_eq {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    countWhere (fun hp : Point N k × cor147PairFamily N k d ↦
      cor147Good B phi hp.1 hp.2) =
      respectedGeneralArrangementCount d B phi := by
  classical
  unfold respectedGeneralArrangementCount countWhere
  apply Finset.card_equiv (cor147ArrangementEquiv N k d)
  intro hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact cor147_good_iff_arrangement B phi hp.1 hp.2

@[simp] private lemma cor147_prod_exponential {N d : Nat} [NeZero N]
    (f : Fin d → ZMod N) :
    ∏ i, exponential (f i) = exponential (∑ i, f i) := by
  symm
  induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
  | empty => simp [exponential]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        cor147_exponential_add, ih]

private lemma cor147_sum_exponential_mul {N : Nat} [NeZero N]
    (x : ZMod N) :
    ∑ u : ZMod N, exponential (x * u) =
      if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

private noncomputable def cor147FourierTerm {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (u r : ZMod N) (z : cor147Atom N k) : Complex := by
  classical
  exact exponential (-(z.2 * r)) *
    if cor147CubeIn B h z then
      exponential (cor147CubeValue phi h z * u)
    else 0

private lemma cor147_prod_fourierTerm {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (u r : ZMod N) (a : Fin d → cor147Atom N k) :
    ∏ i, cor147FourierTerm B phi h u r (a i) =
      if ∀ i, cor147CubeIn B h (a i) then
        exponential
          (-((∑ i, (a i).2) * r) +
            (∑ i, cor147CubeValue phi h (a i)) * u)
      else 0 := by
  classical
  by_cases ha : ∀ i, cor147CubeIn B h (a i)
  · rw [if_pos ha]
    simp only [cor147FourierTerm, if_pos (ha _)]
    simp_rw [← cor147_exponential_add]
    rw [cor147_prod_exponential]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_mul, Finset.sum_mul]
  · rw [if_neg ha]
    simp only [not_forall] at ha
    obtain ⟨i, hi⟩ := ha
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [cor147FourierTerm, hi]

private lemma cor147_pair_orthogonality {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (a b : Fin d → cor147Atom N k) :
    (∑ u : ZMod N, ∑ r : ZMod N,
      (∏ i, cor147FourierTerm B phi h u r (a i)) *
        star (∏ i, cor147FourierTerm B phi h u r (b i))) =
      if cor147Good B phi h (a, b) then (N : Complex) ^ 2 else 0 := by
  classical
  by_cases ha : ∀ i, cor147CubeIn B h (a i) <;>
    by_cases hb : ∀ i, cor147CubeIn B h (b i)
  · simp_rw [cor147_prod_fourierTerm, if_pos ha, if_pos hb,
      cor147_star_exponential, ← cor147_exponential_add]
    have hphase (u r : ZMod N) :
        (-((∑ i, (a i).2) * r) +
              (∑ i, cor147CubeValue phi h (a i)) * u) +
            -(-((∑ i, (b i).2) * r) +
              (∑ i, cor147CubeValue phi h (b i)) * u) =
          ((∑ i, cor147CubeValue phi h (a i)) -
              ∑ i, cor147CubeValue phi h (b i)) * u +
            ((∑ i, (b i).2) - ∑ i, (a i).2) * r := by
      ring
    simp_rw [hphase, cor147_exponential_add]
    calc
      (∑ u : ZMod N, ∑ r : ZMod N,
          exponential
              (((∑ i, cor147CubeValue phi h (a i)) -
                ∑ i, cor147CubeValue phi h (b i)) * u) *
            exponential (((∑ i, (b i).2) - ∑ i, (a i).2) * r)) =
          (∑ u : ZMod N,
            exponential
              (((∑ i, cor147CubeValue phi h (a i)) -
                ∑ i, cor147CubeValue phi h (b i)) * u)) *
          (∑ r : ZMod N,
            exponential (((∑ i, (b i).2) - ∑ i, (a i).2) * r)) := by
              simp_rw [← Finset.mul_sum]
              rw [← Finset.sum_mul]
      _ = if cor147Good B phi h (a, b) then (N : Complex) ^ 2 else 0 := by
        rw [cor147_sum_exponential_mul, cor147_sum_exponential_mul]
        by_cases hx : (∑ i, (a i).2) = ∑ i, (b i).2
        · by_cases hv :
              (∑ i, cor147CubeValue phi h (a i)) =
                ∑ i, cor147CubeValue phi h (b i)
          · simp [cor147Good, ha, hb, hx, hv, pow_two]
          · have hdiff :
                (∑ i, cor147CubeValue phi h (a i)) -
                    ∑ i, cor147CubeValue phi h (b i) ≠ 0 :=
              sub_ne_zero.mpr hv
            simp [cor147Good, ha, hb, hx, hv, hdiff]
        · have hdiff : (∑ i, (b i).2) - ∑ i, (a i).2 ≠ 0 :=
            sub_ne_zero.mpr (Ne.symm hx)
          by_cases hv :
              (∑ i, cor147CubeValue phi h (a i)) =
                ∑ i, cor147CubeValue phi h (b i)
          · simp [cor147Good, ha, hb, hx, hv, hdiff]
          · have hvdiff :
                (∑ i, cor147CubeValue phi h (a i)) -
                    ∑ i, cor147CubeValue phi h (b i) ≠ 0 :=
              sub_ne_zero.mpr hv
            simp [cor147Good, ha, hb, hx, hv, hdiff, hvdiff]
  · simp [cor147_prod_fourierTerm, ha, hb, cor147Good]
  · simp [cor147_prod_fourierTerm, ha, hb, cor147Good]
  · simp [cor147_prod_fourierTerm, ha, hb, cor147Good]

private lemma cor147_sum_pair {X Y M : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid M] (F : X × Y → M) :
    (∑ p : X × Y, F p) = ∑ x : X, ∑ y : Y, F (x, y) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

private lemma cor147_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) (c : Complex) :
    (∑ x : X, if P x then c else 0) = c * countWhere P := by
  classical
  unfold countWhere
  rw [← Finset.sum_filter]
  simp [mul_comm]

private lemma cor147_fourier_eq {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (u r : ZMod N) :
    fourier (cor147Phase B phi h u) r =
      ∑ z : cor147Atom N k, cor147FourierTerm B phi h u r z := by
  classical
  rw [cor147_sum_pair]
  simp only [fourier, ZMod.dft_apply, smul_eq_mul, cor147Phase,
    cor147FourierTerm, exponential]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]

private lemma cor147_norm_power_expansion {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (u r : ZMod N) :
    (((‖fourier (cor147Phase B phi h u) r‖ ^ (2 * d) : Real)) : Complex) =
      ∑ a : Fin d → cor147Atom N k,
        ∑ b : Fin d → cor147Atom N k,
          (∏ i, cor147FourierTerm B phi h u r (a i)) *
            star (∏ i, cor147FourierTerm B phi h u r (b i)) := by
  rw [cor147_ofReal_norm_even_pow, cor147_fourier_eq]
  rw [Fintype.sum_pow]
  simp only [star_sum, Fintype.sum_pow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [star_prod]

private lemma cor147_moment_eq_count {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    (∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
      ‖fourier (cor147Phase B phi h u) r‖ ^ (2 * d)) =
      (N : Real) ^ 2 * respectedGeneralArrangementCount d B phi := by
  classical
  have hcomplex :
      (((∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
          ‖fourier (cor147Phase B phi h u) r‖ ^ (2 * d) : Real)) : Complex) =
        (((N : Real) ^ 2 * countWhere
          (fun hp : Point N k × cor147PairFamily N k d ↦
            cor147Good B phi hp.1 hp.2) : Real) : Complex) := by
    rw [Complex.ofReal_sum]
    calc
      (∑ h : Point N k,
          (((∑ u : ZMod N, ∑ r : ZMod N,
            ‖fourier (cor147Phase B phi h u) r‖ ^ (2 * d) : Real)) :
              Complex)) =
          ∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
            ∑ a : Fin d → cor147Atom N k,
              ∑ b : Fin d → cor147Atom N k,
                (∏ i, cor147FourierTerm B phi h u r (a i)) *
                  star (∏ i, cor147FourierTerm B phi h u r (b i)) := by
            apply Finset.sum_congr rfl
            intro h _
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro u _
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro r _
            exact cor147_norm_power_expansion B phi h u r
      _ = ∑ h : Point N k,
          ∑ a : Fin d → cor147Atom N k,
            ∑ b : Fin d → cor147Atom N k,
              ∑ u : ZMod N, ∑ r : ZMod N,
                (∏ i, cor147FourierTerm B phi h u r (a i)) *
                  star (∏ i, cor147FourierTerm B phi h u r (b i)) := by
            apply Finset.sum_congr rfl
            intro h _
            calc
              (∑ u : ZMod N, ∑ r : ZMod N,
                  ∑ a : Fin d → cor147Atom N k,
                    ∑ b : Fin d → cor147Atom N k,
                      (∏ i, cor147FourierTerm B phi h u r (a i)) *
                        star (∏ i, cor147FourierTerm B phi h u r (b i))) =
                ∑ u : ZMod N, ∑ a : Fin d → cor147Atom N k,
                  ∑ b : Fin d → cor147Atom N k, ∑ r : ZMod N,
                    (∏ i, cor147FourierTerm B phi h u r (a i)) *
                      star (∏ i, cor147FourierTerm B phi h u r (b i)) := by
                  apply Finset.sum_congr rfl
                  intro u _
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro a _
                  rw [Finset.sum_comm]
              _ = ∑ a : Fin d → cor147Atom N k, ∑ u : ZMod N,
                  ∑ b : Fin d → cor147Atom N k, ∑ r : ZMod N,
                    (∏ i, cor147FourierTerm B phi h u r (a i)) *
                      star (∏ i, cor147FourierTerm B phi h u r (b i)) := by
                    rw [Finset.sum_comm]
              _ = ∑ a : Fin d → cor147Atom N k,
                  ∑ b : Fin d → cor147Atom N k,
                    ∑ u : ZMod N, ∑ r : ZMod N,
                      (∏ i, cor147FourierTerm B phi h u r (a i)) *
                        star (∏ i, cor147FourierTerm B phi h u r (b i)) := by
                  apply Finset.sum_congr rfl
                  intro a _
                  rw [Finset.sum_comm]
      _ = ∑ h : Point N k,
          ∑ a : Fin d → cor147Atom N k,
            ∑ b : Fin d → cor147Atom N k,
              if cor147Good B phi h (a, b) then (N : Complex) ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro h _
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            exact cor147_pair_orthogonality B phi h a b
      _ = ∑ hp : Point N k × cor147PairFamily N k d,
          if cor147Good B phi hp.1 hp.2 then (N : Complex) ^ 2 else 0 := by
            rw [cor147_sum_pair]
            apply Finset.sum_congr rfl
            intro h _
            rw [cor147_sum_pair]
      _ = (((N : Real) ^ 2 * countWhere
          (fun hp : Point N k × cor147PairFamily N k d ↦
            cor147Good B phi hp.1 hp.2) : Real) : Complex) := by
            push_cast
            exact cor147_sum_ite _ _
  rw [cor147_good_count_eq B phi] at hcomplex
  exact Complex.ofReal_injective hcomplex

private lemma cor147_phase_norm_le {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (u x : ZMod N) :
    ‖cor147Phase B phi h u x‖ ≤ (N : Real) ^ k := by
  classical
  calc
    ‖cor147Phase B phi h u x‖ ≤
        ∑ y : Point N k,
          ‖if cor147CubeIn B h (y, x) then
              exponential (cor147CubeValue phi h (y, x) * u)
            else 0‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _y : Point N k, (1 : Real) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : cor147CubeIn B h (y, x) <;>
        simp [hy, cor147_norm_exponential]
    _ = (N : Real) ^ k := by simp [Point]

private lemma cor147_phase_norm_sq_sum_le {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (h : Point N k) (u : ZMod N) :
    (∑ x : ZMod N, ‖cor147Phase B phi h u x‖ ^ 2) ≤
      (N : Real) ^ (2 * k + 1) := by
  calc
    (∑ x : ZMod N, ‖cor147Phase B phi h u x‖ ^ 2) ≤
        ∑ _x : ZMod N, ((N : Real) ^ k) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      gcongr
      exact cor147_phase_norm_le B phi h u x
    _ = (N : Real) * ((N : Real) ^ k) ^ 2 := by simp
    _ = (N : Real) ^ (2 * k + 1) := by
      rw [← pow_mul]
      have hmul : k * 2 = 2 * k := by omega
      rw [hmul, pow_succ]
      ring

private lemma cor147_second_moment_le {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    (∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
      ‖fourier (cor147Phase B phi h u) r‖ ^ 2) ≤
      (N : Real) ^ (3 * k + 3) := by
  have hN : 0 ≤ (N : Real) := by positivity
  calc
    (∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (cor147Phase B phi h u) r‖ ^ 2) =
      ∑ h : Point N k, ∑ u : ZMod N,
        (N : Real) * ∑ x : ZMod N, ‖cor147Phase B phi h u x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro h _
          apply Finset.sum_congr rfl
          intro u _
          exact identity_2_3_holds N (cor147Phase B phi h u)
    _ ≤ ∑ _h : Point N k, ∑ _u : ZMod N,
        (N : Real) * (N : Real) ^ (2 * k + 1) := by
          apply Finset.sum_le_sum
          intro h _
          apply Finset.sum_le_sum
          intro u _
          exact mul_le_mul_of_nonneg_left
            (cor147_phase_norm_sq_sum_le B phi h u) hN
    _ = (N : Real) ^ (3 * k + 3) := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card,
        Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      have hcombine :
          (N : Real) ^ k *
              ((N : Real) ^ 1 *
                ((N : Real) ^ 1 * (N : Real) ^ (2 * k + 1))) =
            (N : Real) ^ (3 * k + 3) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega
      simpa only [pow_one] using hcombine

private lemma cor147_interpolation {X : Type*} [Fintype X]
    (a : X → Real) (_ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ 4) ^ 7 ≤
      (∑ i, a i ^ 2) ^ 6 * (∑ i, a i ^ 16) := by
  have h := Real.inner_le_weight_mul_Lp_of_nonneg
    (s := (Finset.univ : Finset X)) (p := (7 : Real)) (by norm_num)
    (fun i ↦ a i ^ 2) (fun i ↦ a i ^ 2)
    (fun i ↦ sq_nonneg (a i)) (fun i ↦ sq_nonneg (a i))
  have hfour : (∑ i, a i ^ 2 * a i ^ 2) = ∑ i, a i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfour] at h
  norm_num [Real.rpow_natCast] at h
  ring_nf at h
  have hleft : 0 ≤ ∑ i, a i ^ 4 :=
    Finset.sum_nonneg fun i _ ↦ by positivity
  have htwo : 0 ≤ ∑ i, a i ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ by positivity
  have hsixteen : 0 ≤ ∑ i, a i ^ 16 :=
    Finset.sum_nonneg fun i _ ↦ by positivity
  have hpow := pow_le_pow_left₀ hleft h 7
  calc
    (∑ i, a i ^ 4) ^ 7 ≤
        (((∑ i, a i ^ 2) ^ ((6 : Real) / 7)) *
          ((∑ i, a i ^ 16) ^ ((1 : Real) / 7))) ^ 7 := hpow
    _ = (∑ i, a i ^ 2) ^ 6 * (∑ i, a i ^ 16) := by
      rw [mul_pow, ← Real.rpow_mul_natCast htwo,
        ← Real.rpow_mul_natCast hsixteen]
      norm_num [Real.rpow_natCast]

private def cor147Spectrum {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (z : Point N k × (ZMod N × ZMod N)) : Real :=
  ‖fourier (cor147Phase B phi z.1 z.2.1) z.2.2‖

private lemma cor147_spectrum_sum_pow {N k m : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    (∑ z : Point N k × (ZMod N × ZMod N),
      cor147Spectrum B phi z ^ m) =
      ∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (cor147Phase B phi h u) r‖ ^ m := by
  rw [cor147_sum_pair]
  apply Finset.sum_congr rfl
  intro h _
  rw [cor147_sum_pair]
  rfl

private lemma cor147_moment_interpolation {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    (∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
      ‖fourier (cor147Phase B phi h u) r‖ ^ 4) ^ 7 ≤
      (∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (cor147Phase B phi h u) r‖ ^ 2) ^ 6 *
      (∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (cor147Phase B phi h u) r‖ ^ 16) := by
  have h := cor147_interpolation (cor147Spectrum B phi) fun z ↦ norm_nonneg _
  simpa only [cor147_spectrum_sum_pow] using h

theorem lemma_14_7_holds : lemma_14_7 := by
  intro N k _ theta B phi htheta hpairs
  let S2 : Real :=
    ∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
      ‖fourier (cor147Phase B phi h u) r‖ ^ 2
  let S4 : Real :=
    ∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
      ‖fourier (cor147Phase B phi h u) r‖ ^ 4
  let S16 : Real :=
    ∑ h : Point N k, ∑ u : ZMod N, ∑ r : ZMod N,
      ‖fourier (cor147Phase B phi h u) r‖ ^ 16
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hS2 : S2 ≤ (N : Real) ^ (3 * k + 3) := by
    dsimp only [S2]
    exact cor147_second_moment_le B phi
  have hS4eq :
      S4 = (N : Real) ^ 2 * respectedGeneralArrangementCount 2 B phi := by
    dsimp only [S4]
    simpa using cor147_moment_eq_count (d := 2) B phi
  have hS16eq :
      S16 = (N : Real) ^ 2 * respectedGeneralArrangementCount 8 B phi := by
    dsimp only [S16]
    simpa using cor147_moment_eq_count (d := 8) B phi
  have hinterpolation : S4 ^ 7 ≤ S2 ^ 6 * S16 := by
    dsimp only [S4, S2, S16]
    exact cor147_moment_interpolation B phi
  have hS4lower : theta * (N : Real) ^ (5 * k + 5) ≤ S4 := by
    calc
      theta * (N : Real) ^ (5 * k + 5) =
          (N : Real) ^ 2 * (theta * (N : Real) ^ (5 * k + 3)) := by
        rw [show 5 * k + 5 = 2 + (5 * k + 3) by omega, pow_add]
        ring
      _ ≤ (N : Real) ^ 2 * respectedGeneralArrangementCount 2 B phi :=
        mul_le_mul_of_nonneg_left hpairs (by positivity)
      _ = S4 := hS4eq.symm
  have hS2nonneg : 0 ≤ S2 := by
    dsimp only [S2]
    positivity
  have hS16nonneg : 0 ≤ S16 := by
    dsimp only [S16]
    positivity
  have hmain :
      (theta * (N : Real) ^ (5 * k + 5)) ^ 7 ≤
        ((N : Real) ^ (3 * k + 3)) ^ 6 * S16 := by
    calc
      (theta * (N : Real) ^ (5 * k + 5)) ^ 7 ≤ S4 ^ 7 :=
        pow_le_pow_left₀ (by positivity) hS4lower 7
      _ ≤ S2 ^ 6 * S16 := hinterpolation
      _ ≤ ((N : Real) ^ (3 * k + 3)) ^ 6 * S16 := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hS2nonneg hS2 6) hS16nonneg
  have hfactor : 0 < (N : Real) ^ (18 * k + 20) := pow_pos hN _
  apply le_of_mul_le_mul_right ?_ hfactor
  have hlowerPower :
      (theta ^ 7 * (N : Real) ^ (17 * k + 15)) *
          (N : Real) ^ (18 * k + 20) =
        (theta * (N : Real) ^ (5 * k + 5)) ^ 7 := by
    have hcombine :
        (N : Real) ^ (17 * k + 15) * (N : Real) ^ (18 * k + 20) =
          (N : Real) ^ ((5 * k + 5) * 7) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (theta ^ 7 * (N : Real) ^ (17 * k + 15)) *
          (N : Real) ^ (18 * k + 20) =
        theta ^ 7 *
          ((N : Real) ^ (17 * k + 15) * (N : Real) ^ (18 * k + 20)) := by
            ring
      _ = theta ^ 7 * (N : Real) ^ ((5 * k + 5) * 7) := by rw [hcombine]
      _ = (theta * (N : Real) ^ (5 * k + 5)) ^ 7 := by
        rw [mul_pow, pow_mul]
  have hupperPower :
      ((N : Real) ^ (3 * k + 3)) ^ 6 * S16 =
        (respectedGeneralArrangementCount 8 B phi : Real) *
          (N : Real) ^ (18 * k + 20) := by
    have hcombine :
        (N : Real) ^ ((3 * k + 3) * 6) * (N : Real) ^ 2 =
          (N : Real) ^ (18 * k + 20) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      ((N : Real) ^ (3 * k + 3)) ^ 6 * S16 =
          (N : Real) ^ ((3 * k + 3) * 6) *
            ((N : Real) ^ 2 *
              respectedGeneralArrangementCount 8 B phi) := by
        rw [pow_mul, hS16eq]
      _ = (respectedGeneralArrangementCount 8 B phi : Real) *
          ((N : Real) ^ ((3 * k + 3) * 6) * (N : Real) ^ 2) := by ring
      _ = (respectedGeneralArrangementCount 8 B phi : Real) *
          (N : Real) ^ (18 * k + 20) := by rw [hcombine]
  calc
    (theta ^ 7 * (N : Real) ^ (17 * k + 15)) *
        (N : Real) ^ (18 * k + 20) =
      (theta * (N : Real) ^ (5 * k + 5)) ^ 7 := hlowerPower
    _ ≤ ((N : Real) ^ (3 * k + 3)) ^ 6 * S16 := hmain
    _ = (respectedGeneralArrangementCount 8 B phi : Real) *
        (N : Real) ^ (18 * k + 20) := hupperPower

end LeanProofs.GowersSzemeredi
