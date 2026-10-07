import OAI.Combinatorics.Progressions.Geometry.ProgressionCoordinateResampling
import OAI.Combinatorics.Progressions.Sampling.BooleanProductSampler

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def booleanBlockValue {G α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (a : G → Option α → ℝ) (t : Finset α) : ℝ :=
  ∏ g, ∑ r, (booleanFeature r t : ℝ)*a g r

noncomputable def booleanBlockPhase {G α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (ξ : Finset α → ℝ) (a : G → Option α → ℝ) : ℝ :=
  ∑ s, ξ s * booleanCoefficient (booleanBlockValue a) s

theorem booleanBlockValue_eq_polynomial {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (a : G → Option α → ℝ) (t : Finset α) :
    booleanBlockValue a t =
      MvPolynomial.eval (fun z : BlockParameter Unit G α => a z.2.1 z.2.2)
        (booleanBlockPolynomial (F := G) () t) := by
  simp only [booleanBlockValue, booleanBlockPolynomial, map_prod, booleanAffinePolynomial_eval]

def frozenBooleanConstant {G α : Type*} [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (t : Finset α) (g : G) : ℝ :=
  ∑ r ∈ Finset.univ.erase (label g), (booleanFeature r t : ℝ)*c g r

theorem booleanAffine_resample {G α : Type*} [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (x : G → ℝ) (t : Finset α) (g : G) :
    (∑ r, (booleanFeature r t : ℝ)*resampleGroupCoordinates label c x g r) =
      (booleanFeature (label g) t : ℝ)*x g + frozenBooleanConstant label c t g := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (label g))]
  rw [resampleGroupCoordinates_selected]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [resampleGroupCoordinates, Function.update_of_ne (Finset.ne_of_mem_erase hr)]

theorem booleanBlockValue_resample {G α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (x : G → ℝ) (t : Finset α) :
    booleanBlockValue (resampleGroupCoordinates label c x) t =
      ∏ g, ((booleanFeature (label g) t : ℝ)*x g + frozenBooleanConstant label c t g) := by
  simp only [booleanBlockValue, booleanAffine_resample]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_degreeOf_le {α ι : Type*} [DecidableEq α]
    (f : Finset α → MvPolynomial ι ℝ) (s : Finset α) (j : ι) (d : ℕ)
    (hf : ∀ t ∈ s.powerset, (f t).degreeOf j ≤ d) :
    (booleanCoefficient f s).degreeOf j ≤ d := by
  classical
  unfold booleanCoefficient
  apply (MvPolynomial.degreeOf_sum_le j s.powerset _).trans
  apply Finset.sup_le
  intro t ht
  have hc : (-1 : MvPolynomial ι ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [hc]
  exact (MvPolynomial.degreeOf_C_mul_le _ j _).trans (hf t ht)

theorem booleanSelectedColumn_degreeOf_le {B F α : Type*} [Fintype F] [Fintype α]
    [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α) (j : BlockParameter B F α) :
    (booleanSelectedColumn c b v r s).degreeOf j ≤ Fintype.card F - 1 := by
  unfold booleanSelectedColumn
  apply (MvPolynomial.degreeOf_C_mul_le _ j _).trans
  apply booleanCoefficient_degreeOf_le
  intro t _
  apply (MvPolynomial.degreeOf_C_mul_le _ j _).trans
  apply (MvPolynomial.degreeOf_prod_le j (Finset.univ.erase v) _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.univ.erase v, (1 : ℕ) :=
      Finset.sum_le_sum (fun k _ => booleanAffinePolynomial_degreeOf_le b k t j)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem booleanBlockJet_eq_sampler {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (a : G → Option α → ℝ) (s : Finset α) :
    booleanCoefficient (booleanBlockValue a) s =
      MvPolynomial.eval (fun z : BlockParameter Unit G α => a z.2.1 z.2.2)
        (booleanSamplerPolynomial (F := G) (fun _ : Unit => 1) s) := by
  rw [booleanSamplerPolynomial, booleanCoefficient_map]
  congr 1
  funext t
  simp only [map_sum, map_mul, MvPolynomial.eval_C, one_mul]
  simpa using booleanBlockValue_eq_polynomial a t

theorem booleanBlockPhase_eq_sampler {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (ξ : Finset α → ℝ) (a : G → Option α → ℝ) :
    booleanBlockPhase ξ a = ∑ s, ξ s *
      MvPolynomial.eval (fun z : BlockParameter Unit G α => a z.2.1 z.2.2)
        (booleanSamplerPolynomial (F := G) (fun _ : Unit => 1) s) := by
  simp only [booleanBlockPhase, booleanBlockJet_eq_sampler]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def frozenBooleanFactor {G α : Type*} [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (t : Finset α) (g : G) : MvPolynomial G ℝ :=
  MvPolynomial.C (booleanFeature (label g) t : ℝ)*MvPolynomial.X g +
    MvPolynomial.C (frozenBooleanConstant label c t g)

noncomputable def frozenBooleanPhasePolynomial {G α : Type*} [Fintype G]
    [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (ξ : Finset α → ℝ) : MvPolynomial G ℝ :=
  ∑ s, MvPolynomial.C (ξ s) * booleanCoefficient (fun t => ∏ g, frozenBooleanFactor label c t g) s

theorem frozenBooleanFactor_degree {G α : Type*} [DecidableEq G] [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (t : Finset α) (g j : G) :
    (frozenBooleanFactor label c t g).degreeOf j ≤ if g=j then 1 else 0 := by
  unfold frozenBooleanFactor
  apply (MvPolynomial.degreeOf_add_le _ _ _).trans
  apply max_le
  · apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
    simp only [MvPolynomial.degreeOf_X, eq_comm]
    exact le_rfl
  · simp only [MvPolynomial.degreeOf_C]
    split_ifs <;> omega

theorem frozenBooleanProduct_degree {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (label : G → Option α) (c : G → Option α → ℝ)
    (t : Finset α) (j : G) : (∏ g, frozenBooleanFactor label c t g).degreeOf j ≤ 1 := by
  apply (MvPolynomial.degreeOf_prod_le j Finset.univ _).trans
  apply (Finset.sum_le_sum (fun g _ => frozenBooleanFactor_degree label c t g j)).trans
  simp

theorem frozenBooleanPhasePolynomial_degree {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (label : G → Option α) (c : G → Option α → ℝ)
    (ξ : Finset α → ℝ) (j : G) : (frozenBooleanPhasePolynomial label c ξ).degreeOf j ≤ 1 := by
  unfold frozenBooleanPhasePolynomial
  apply (MvPolynomial.degreeOf_sum_le j Finset.univ _).trans
  apply Finset.sup_le
  intro s _
  apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
  exact booleanCoefficient_degreeOf_le _ s j 1
    (fun t _ => frozenBooleanProduct_degree label c t j)

theorem frozenBooleanPhasePolynomial_eval {G α : Type*} [Fintype G] [Fintype α]
    [DecidableEq α] (label : G → Option α) (c : G → Option α → ℝ)
    (ξ : Finset α → ℝ) (x : G → ℝ) :
    MvPolynomial.eval x (frozenBooleanPhasePolynomial label c ξ) =
      booleanBlockPhase ξ (resampleGroupCoordinates label c x) := by
  simp only [frozenBooleanPhasePolynomial, booleanBlockPhase, map_sum, map_mul,
    MvPolynomial.eval_C, booleanCoefficient_map, map_prod, frozenBooleanFactor,
    map_add, MvPolynomial.eval_X]
  have he : booleanBlockValue (resampleGroupCoordinates label c x) =
      (fun t => ∏ g, ((booleanFeature (label g) t : ℝ)*x g + frozenBooleanConstant label c t g)) := by
    funext t
    exact booleanBlockValue_resample label c x t
  rw [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem booleanBlock_scaled_jet_eq_sampler {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (a : G → Option α → ℝ) (b : ℝ) (s : Finset α) :
    b*booleanCoefficient (booleanBlockValue a) s =
      MvPolynomial.eval (fun z : BlockParameter Unit G α => a z.2.1 z.2.2)
        (booleanSamplerPolynomial (F := G) (fun _ : Unit => b) s) := by
  rw [booleanSamplerPolynomial, booleanCoefficient_map]
  have he : (fun t => MvPolynomial.eval
      (fun z : BlockParameter Unit G α => a z.2.1 z.2.2)
      (∑ i : Unit, MvPolynomial.C b * booleanBlockPolynomial (F := G) i t)) =
      (fun t => b*booleanBlockValue a t) := by
    funext t
    simp only [map_sum, map_mul, MvPolynomial.eval_C]
    simp [← booleanBlockValue_eq_polynomial]
  rw [he, booleanCoefficient_const_mul]

theorem booleanBlock_scaled_phase_eq_sampler {G α : Type*} [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] (ξ : Finset α → ℝ) (a : G → Option α → ℝ) (b : ℝ) :
    b*booleanBlockPhase ξ a = ∑ s, ξ s *
      MvPolynomial.eval (fun z : BlockParameter Unit G α => a z.2.1 z.2.2)
        (booleanSamplerPolynomial (F := G) (fun _ : Unit => b) s) := by
  simp only [booleanBlockPhase, Finset.mul_sum, ← booleanBlock_scaled_jet_eq_sampler]
  apply Finset.sum_congr rfl
  intro s _
  ring

end Erdos3

end

end OAI
