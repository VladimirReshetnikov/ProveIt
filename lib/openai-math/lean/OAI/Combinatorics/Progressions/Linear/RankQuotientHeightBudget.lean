/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.LinearAlgebra.Basis.VectorSpace
import OAI.Combinatorics.Progressions.Dynamics.SparseGeneratorBudget
import OAI.Combinatorics.Progressions.Estimates.BoundedQuotientFunctional
import OAI.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
import OAI.Combinatorics.Progressions.Geometry.SubmoduleQuotientCoordinates
import OAI.Combinatorics.Progressions.Polynomial.FreeDegreeRankAdaptedBounds

namespace OAI

section

namespace Erdos3

open Module

variable {ι κ V : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]

theorem exists_bounded_submodule_quotient_basis (b : Basis ι ℚ V) (U : Submodule ℚ V)
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∃ t : ℕ, t ≤ Fintype.card κ ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ f : Basis (Fin d) ℚ (V ⧸ U),
        ∀ i j, RationalHeightLE (f.repr (U.mkQ (b j)) i) (rationalKernelHeight t H) := by
  classical
  let A : Matrix ι κ ℚ := fun i j => b.repr (v j) i
  have hA : LinearMap.range A.mulVecLin = U.map b.equivFun.toLinearMap := by
    rw [Matrix.range_mulVecLin, ← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  obtain ⟨t, ht, d, hd, D, hsurj, hker, hD⟩ :=
    exists_bounded_image_equations A hH (fun i j => hv j i)
  have hkerD := hker.trans hA
  let f := submoduleQuotientCoordinateBasis b U D hkerD hsurj
  have hf : LinearMap.toMatrix b f U.mkQ = D :=
    submoduleQuotientCoordinateBasis_matrix b U D hkerD hsurj
  refine ⟨t, ht, d, hd, f, fun i j => ?_⟩
  have hij := congrFun (congrFun hf i) j
  rw [LinearMap.toMatrix_apply] at hij
  rw [hij]
  exact hD i j

theorem exists_submodule_quotient_basis_exp (b : Basis ι ℚ V) (U : Submodule ℚ V)
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hm : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
      ∃ d : ℕ, d ≤ Fintype.card ι ∧ ∃ f : Basis (Fin d) ℚ (V ⧸ U),
        ∀ i j, RationalHeightLE (f.repr (U.mkQ (b j)) i) H' := by
  obtain ⟨t, ht, d, hd, f, hf⟩ := exists_bounded_submodule_quotient_basis b U v hspan hH hv
  exact ⟨rationalKernelHeight t H, rationalKernelHeight_pos t hH,
    rationalKernelHeight_le_budget t H hp ((Nat.cast_le.mpr ht).trans hm) hHp,
    d, hd, f, hf⟩

end Erdos3

end

section

namespace Erdos3

open Module

variable {ν L : Type*} [AddCommGroup L] [Module ℚ L] [FiniteDimensional ℚ L]
  (e : Basis ν ℚ L) (H : ℕ)

noncomputable def chosenBoundedSubmoduleBasis (U : Submodule ℚ L) :
    Basis (Fin (finrank ℚ U)) ℚ U := by
  classical
  exact if h : ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ j k, RationalHeightLE (e.repr (b j).val k) H then h.choose else Module.finBasis ℚ U

theorem chosenBoundedSubmoduleBasis_height (U : Submodule ℚ L)
    (h : ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ j k, RationalHeightLE (e.repr (b j).val k) H) (j k) :
    RationalHeightLE (e.repr (chosenBoundedSubmoduleBasis e H U j).val k) H := by
  classical
  unfold chosenBoundedSubmoduleBasis
  rw [dite_eq_left h]
  exact h.choose_spec j k

theorem chosenBoundedSubmoduleBasis_range {U V : Submodule ℚ L} (h : U = V) :
    Set.range (fun j => (chosenBoundedSubmoduleBasis e H U j).val) =
      Set.range (fun j => (chosenBoundedSubmoduleBasis e H V j).val) := by
  subst V
  rfl

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_submodule_basis_from_spanning
    {L μ κ : Type*} [AddCommGroup L] [Module ℚ L] [Fintype μ]
    (b : Basis μ ℚ L) (V : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = V) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H) :
    ∃ e : Basis (Fin (Module.finrank ℚ V)) ℚ V,
      ∀ i j, RationalHeightLE (b.repr (e i : L) j) H := by
  classical
  let : FiniteDimensional ℚ L := b.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro i j
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz i
  rw [← hk]
  exact hv k j

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype υ] [Fintype χ] [Fintype κ] [Fintype ν]

theorem exists_stepDrop_bounded_basis (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H B : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (hbr : ∀ i j z, RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) B) :
    ∃ r : ℕ, r ≤ Fintype.card (StepDropRow υ χ κ ν) ∧
      ∃ e : Basis (Fin (Module.finrank ℚ (stepDropSubmodule b w U V K)))
        ℚ (stepDropSubmodule b w U V K),
        ∀ i j, RationalHeightLE (b.repr (e i : L) j)
          ((Fintype.card μ + 1) * rationalKernelHeight r (max H B) ^ Fintype.card μ) := by
  classical
  let P := stepDropSystem b w U V K fU fK fV eK
  have hP : ∀ i j, RationalHeightLE ((Pi.basisFun ℚ (StepDropRow υ χ κ ν)).repr (P (b i)) j) (max H B) := by
    intro i j
    change RationalHeightLE (P (b i) j) _
    exact stepDropSystem_basis_height b w U V K fU fK fV eK hH hU hK hV hbr j i
  obtain ⟨r, hr, v, hspan, hv⟩ := exists_bounded_span_kernel_generators b
    (Pi.basisFun ℚ (StepDropRow υ χ κ ν)) P b
    (hH.trans (Nat.le_max_left H B)) (basis_repr_height_one b) hP
  have hspan' : Submodule.span ℚ (Set.range v) = stepDropSubmodule b w U V K := by
    simpa only [b.span_eq, top_inf_eq, P, stepDropSystem_ker] using hspan
  have hv' : ∀ i j, RationalHeightLE (b.repr (v i) j)
      ((Fintype.card μ + 1) * rationalKernelHeight r (max H B) ^ Fintype.card μ) := by
    simpa only [mul_one] using hv
  obtain ⟨e, he⟩ := exists_bounded_submodule_basis_from_spanning b _ v hspan' hv'
  exact ⟨r, hr, e, he⟩

def stepDropBracketHeight (n H : ℕ) : ℕ :=
  (n + 1) * (((n ^ 2 + 1) * (H * H) ^ (n ^ 2)) * H) ^ n

omit [Fintype κ] [Fintype ν] in
theorem stepDrop_bracket_height (b : Basis μ ℚ L) (V K : Submodule ℚ L)
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H : ℕ}
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (heK : ∀ i j, RationalHeightLE (b.repr (eK j : L) i) H)
    (hstructure : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) (i : ν) (j : μ) (z : κ) :
    RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) (stepDropBracketHeight (Fintype.card μ) H) := by
  have hbr := lie_bracket_coordinate_height b hstructure (b j) (eK z : L)
    (basis_repr_height_one b j) (fun k => heK k z)
  have h := linearMap_coordinate_height b fV V.mkQ (fun a c => hV c a) _ hbr i
  simpa only [stepDropBracketHeight, mul_one] using h

theorem stepDrop_basis_height_budget (n r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (((n + 1) * rationalKernelHeight r H ^ n : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
  have hkernel := rationalKernelHeight_le_budget r H hp hr hH
  have hfront : (n + 1 : ℝ) ≤ Real.exp n := Real.add_one_le_exp n
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (rationalKernelHeight r H)) hkernel n
  rw [← Real.exp_nat_mul] at hpower
  have h : (((n + 1) * rationalKernelHeight r H ^ n : ℕ) : ℝ) ≤
      Real.exp ((n : ℝ) + n * (p + 2) ^ 7) := by
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul hfront hpower (by positivity) (Real.exp_nonneg _)
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have ht : (1 : ℝ) ≤ p + 2 := by linarith
  have hpow : p + 2 ≤ (p + 2) ^ 8 := by
    simpa only [pow_one] using pow_le_pow_right₀ ht (by decide : 1 ≤ 8)
  calc
    (n : ℝ) + n * (p + 2) ^ 7 ≤ p + p * (p + 2) ^ 7 := by gcongr
    _ ≤ (p + 2) + (p + 2) * (p + 2) ^ 7 := by gcongr <;> linarith
    _ = (p + 2) + (p + 2) ^ 8 := by ring
    _ ≤ 2 * (p + 2) ^ 8 := by linarith
    _ ≤ (p + 2) * (p + 2) ^ 8 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (p + 2) ^ 9 := by ring

theorem exists_stepDrop_basis_exp_height (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (hbr : ∀ i j z, RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hrows : (Fintype.card (StepDropRow υ χ κ ν) : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ e : Basis (Fin (Module.finrank ℚ (stepDropSubmodule b w U V K)))
      ℚ (stepDropSubmodule b w U V K), ∀ i j,
      (((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 9)) ∧
      (((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + 2) ^ 9)) := by
  obtain ⟨r, hr, e, he⟩ := exists_stepDrop_bounded_basis b w U V K fU fK fV eK hH hU hK hV hbr
  have hrp : (r : ℝ) ≤ p := (Nat.cast_le.mpr hr).trans hrows
  have hb := stepDrop_basis_height_budget (Fintype.card μ) r H hp hμ hrp hHp
  refine ⟨e, fun i j => ?_⟩
  have hij : RationalHeightLE (b.repr (e i : L) j)
      ((Fintype.card μ + 1) * rationalKernelHeight r H ^ Fintype.card μ) := by
    simpa only [max_self] using he i j
  exact ⟨(Nat.cast_le.mpr hij.1).trans hb, (Nat.cast_le.mpr hij.2).trans hb⟩

end Erdos3

end

section

namespace Erdos3

open Module

noncomputable def preimageBasisBudget (p : ℝ) : ℝ :=
  sparseGeneratorBudget (p + (p + (p + 3) ^ 7 + 2) ^ 4 + 1)

theorem preimageBasisBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ preimageBasisBudget p := by
  apply sparseGeneratorBudget_nonneg
  positivity

theorem exists_preimage_basis_logHeight
    {V W μ ν ι κ : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [Fintype μ] [Fintype ν] [Fintype ι] [Fintype κ]
    (e : Basis μ ℚ V) (f : Basis ν ℚ W) (U : Submodule ℚ V) (K : Submodule ℚ W)
    (T : V →ₗ[ℚ] W) (u : ι → V) (v : κ → W)
    (hu : Submodule.span ℚ (Set.range u) = U)
    (hv : Submodule.span ℚ (Set.range v) = K)
    {p : ℝ} (hp : 0 ≤ p) (hν : (Fintype.card ν : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (huH : ∀ a i, rationalLogHeight (e.repr (u a) i) ≤ p)
    (hvH : ∀ a i, rationalLogHeight (f.repr (v a) i) ≤ p)
    (hTu : ∀ a i, rationalLogHeight (f.repr (T (u a)) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (U ⊓ K.comap T : Submodule ℚ V))) ℚ
        (U ⊓ K.comap T : Submodule ℚ V),
      ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ preimageBasisBudget p := by
  obtain ⟨H, _, hH, d, hd, g, hg⟩ := exists_submodule_quotient_basis_exp f K v hv
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hvH a i))
    (show 0 ≤ p + 1 by linarith) (hκ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
  have hgH (i : ν) (j : Fin d) :
      rationalLogHeight (g.repr (K.mkQ (f i)) j) ≤ (p + 3) ^ 7 := by
    have h := rationalLogHeight_le_of_height (hg j i) hH
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  let q := p + (p + 3) ^ 7
  have hpq : p ≤ q := le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp.trans hpq
  have hquot (a : ι) (j : Fin d) :
      rationalLogHeight (g.repr (K.mkQ (T (u a))) j) ≤ (q + 2) ^ 4 :=
    linearMap_coordinate_logHeight f g K.mkQ hq (hν.trans hpq)
      (fun i j => (hgH i j).trans (le_add_of_nonneg_left hp))
      (T (u a)) (fun i => (hTu a i).trans hpq) j
  let Q := p + (q + 2) ^ 4
  have hpQ : p ≤ Q := le_add_of_nonneg_right (by positivity)
  have hQ : 0 ≤ Q := hp.trans hpQ
  let B := ⌈Real.exp Q⌉₊
  obtain ⟨t, ht, z, hz, hzH⟩ := exists_bounded_span_kernel_generators e g
    (K.mkQ.comp T) u (one_le_ceil_exp Q)
    (fun a i => rationalHeightLE_ceil_exp ((huH a i).trans hpQ))
    (fun a i => rationalHeightLE_ceil_exp
      ((hquot a i).trans (le_add_of_nonneg_left hp)))
  have hker : LinearMap.ker (K.mkQ.comp T) = K.comap T := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hu, hker] at hz
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e _ z hz hzH
  have ht' : (t : ℝ) ≤ p := by
    exact (Nat.cast_le.mpr ((show t ≤ d by simpa only [Fintype.card_fin] using ht).trans hd)).trans hν
  have hcost : (((Fintype.card ι + 1) * (rationalKernelHeight t B * B) ^
      Fintype.card ι : ℕ) : ℝ) ≤ Real.exp (preimageBasisBudget p) :=
    sparseGeneratorHeight_bound (show 0 ≤ Q + 1 by linarith) t (Fintype.card ι) B
      (ht'.trans (hpQ.trans (by linarith))) (hι.trans (hpQ.trans (by linarith)))
      (ceil_exp_le_exp_add_one hQ)
  exact ⟨b, fun a i => rationalLogHeight_le_of_height (hb a i) hcost⟩

end Erdos3

end

section

namespace Erdos3

open Module

def rankQuotientLayerHeight (n m H : ℕ) : ℕ :=
  (n + 1) * (H * rationalKernelHeight m H) ^ n

def rankQuotientFrequencyHeight (n m u H : ℕ) : ℕ :=
  (u + 1) * (rationalSolveHeight u (rankQuotientLayerHeight n m H) *
    ((n + 1) * (H * H) ^ n)) ^ u

def rankQuotientHeight (n m q u H : ℕ) : ℕ :=
  max 1 (max (rationalKernelHeight m H)
    (max (rationalLieStructureHeight n (max H (max (rationalKernelHeight m H)
      (rationalSolveHeight q (rationalKernelHeight m H)))))
      (max (rankQuotientLayerHeight n m H) (rankQuotientFrequencyHeight n m u H))))

theorem exists_bounded_rank_quotient_data
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n t : ℕ}
    (F : DegreeRankLieFiltration L s r) (e : Basis (Fin n) ℚ L)
    (b : ∀ i : Fin (s + 1), Basis (Fin (finrank ℚ (F.associatedDegree.layer (i.val + 1))))
      ℚ (F.associatedDegree.layer (i.val + 1)))
    (c : ∀ i j : Fin (s + 1), Basis (Fin (finrank ℚ (F.layer i.val j.val)))
      ℚ (F.layer i.val j.val))
    (I : LieIdeal ℚ L) (a : Basis (Fin t) ℚ I)
    (η : L →ₗ[ℚ] ℚ) (hann : F.layer s r ⊓ I.toSubmodule ≤ η.ker)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (ha : ∀ i j, RationalHeightLE (e.repr (a i).val j) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hη : ∀ i, RationalHeightLE (η (e i)) H) :
    ∃ m : ℕ, m ≤ t ∧ ∃ q : ℕ, q ≤ n ∧ ∃ u : ℕ, u ≤ q ∧
      ∃ f : Basis (Fin q) ℚ (L ⧸ I),
        (∀ i j, RationalHeightLE (f.repr (lieQuotientMap I (e j)) i)
          (rankQuotientHeight n m q u H)) ∧
        (∀ i j k, RationalHeightLE (lieStructureConstants f i j k)
          (rankQuotientHeight n m q u H)) ∧
        (∀ i : Fin (s + 1), ∃ b' : Basis
            (Fin (finrank ℚ ((F.associatedDegree.layer (i.val + 1)).map (lieQuotientMap I).toLinearMap)))
            ℚ ((F.associatedDegree.layer (i.val + 1)).map (lieQuotientMap I).toLinearMap),
          ∀ a j, RationalHeightLE (f.repr (b' a).val j) (rankQuotientHeight n m q u H)) ∧
        (∀ i j : Fin (s + 1), ∃ c' : Basis
            (Fin (finrank ℚ ((F.layer i.val j.val).map (lieQuotientMap I).toLinearMap)))
            ℚ ((F.layer i.val j.val).map (lieQuotientMap I).toLinearMap),
          ∀ a k, RationalHeightLE (f.repr (c' a).val k) (rankQuotientHeight n m q u H)) ∧
        ∃ ξ : (L ⧸ I) →ₗ[ℚ] ℚ,
          (∀ x ∈ F.layer s r, ξ (lieQuotientMap I x) = η x) ∧
          ∀ i, RationalHeightLE (ξ (f i)) (rankQuotientHeight n m q u H) := by
  classical
  obtain ⟨m, hm, q, hq, f, A, _, hmatrix, _, hA, _, hstructure⟩ :=
    exists_bounded_lie_quotient_with_structure e I (fun i => (a i).val)
      (span_submodule_basis I.toSubmodule a) hH (fun i j => ha j i) hbracket
  have hm' : m ≤ t := by simpa only [Fintype.card_fin] using hm
  have hq' : q ≤ n := by simpa only [Fintype.card_fin] using hq
  let π := (lieQuotientMap I).toLinearMap
  let Q := rationalKernelHeight m H
  let E := rankQuotientLayerHeight n m H
  have hQ : 1 ≤ Q := rationalKernelHeight_pos m hH
  have hE : 1 ≤ E := by
    have : 0 < H := by omega
    have : 0 < Q := by omega
    change 1 ≤ (n + 1) * (H * Q) ^ n
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hproj (i j) : RationalHeightLE (f.repr (π (e j)) i) Q := by
    have h := hA i j
    rw [← hmatrix, LinearMap.toMatrix_apply] at h
    exact h
  have himage (P : Submodule ℚ L)
      (bP : Basis (Fin (finrank ℚ P)) ℚ P)
      (hP : ∀ i j, RationalHeightLE (e.repr (bP i).val j) H) :
      ∃ b' : Basis (Fin (finrank ℚ (P.map π))) ℚ (P.map π),
        ∀ i j, RationalHeightLE (f.repr (b' i).val j) E := by
    have hspan : Submodule.span ℚ (Set.range (fun i => π (bP i).val)) = P.map π := by
      change Submodule.span ℚ (Set.range (π ∘ (fun i => (bP i).val))) = _
      rw [Set.range_comp, ← Submodule.map_span, span_submodule_basis]
    apply exists_bounded_submodule_basis_from_spanning f _ (fun i => π (bP i).val) hspan
    intro i j
    simpa only [Fintype.card_fin, E, Q, rankQuotientLayerHeight] using
      linearMap_coordinate_height e f π (fun i j => hproj j i) (bP i).val (hP i) j
  let u := finrank ℚ ((F.layer s r).map π)
  let _ : FiniteDimensional ℚ (L ⧸ I) := f.finiteDimensional_of_finite
  have hu : u ≤ q := by
    have hfq : finrank ℚ (L ⧸ I) = q := by
      simpa only [Fintype.card_fin] using finrank_eq_card_basis f
    exact (Submodule.finrank_le _).trans_eq hfq
  let cs := c ⟨s, Nat.lt_succ_self s⟩ ⟨r, Nat.lt_succ_of_le F.rank_le_degree⟩
  obtain ⟨ξ, hξ, hξH⟩ := exists_bounded_quotient_functional (F.layer s r) I.toSubmodule f
    (fun i => (cs i).val) (span_submodule_basis _ cs) η hann hE
    (fun i j => by
      change RationalHeightLE (f.repr (π (cs i).val) j) E
      simpa only [Fintype.card_fin, E, Q, rankQuotientLayerHeight] using linearMap_coordinate_height e f π
        (fun i j => hproj j i) (cs i).val (hc _ _ i) j)
    (fun i => by
      simpa only [Fintype.card_fin] using
        linearFunctional_coordinate_height e η hη (cs i).val (hc _ _ i))
  let K := rankQuotientHeight n m q u H
  have hQK : Q ≤ K := by dsimp only [K, rankQuotientHeight, Q]; omega
  have hEK : E ≤ K := by dsimp only [K, rankQuotientHeight, E]; omega
  have hSK : rationalLieStructureHeight n
      (max H (max Q (rationalSolveHeight q Q))) ≤ K := by
    dsimp only [K, rankQuotientHeight, Q]; omega
  have hFK : rankQuotientFrequencyHeight n m u H ≤ K := by
    dsimp only [K, rankQuotientHeight]; omega
  refine ⟨m, hm', q, hq', u, hu, f, fun i j => (hproj i j).mono hQK,
    ?_, ?_, ?_, ξ, hξ, fun i => (hξH i).mono hFK⟩
  · intro i j k
    have h : RationalHeightLE (lieStructureConstants f i j k)
        (rationalLieStructureHeight n (max H (max Q (rationalSolveHeight q Q)))) := by
      simpa only [Fintype.card_fin] using hstructure i j k
    exact h.mono hSK
  · intro i
    obtain ⟨b', hb'⟩ := himage _ (b i) (hb i)
    exact ⟨b', fun a j => (hb' a j).mono hEK⟩
  · intro i j
    obtain ⟨c', hc'⟩ := himage _ (c i j) (hc i j)
    exact ⟨c', fun a k => (hc' a k).mono hEK⟩

end Erdos3

end

section

namespace Erdos3

open Module

variable {ν L : Type*} [AddCommGroup L] [Module ℚ L] [FiniteDimensional ℚ L]

theorem chosenBasis_smul_coordinate_height (e : Basis ν ℚ L) (H : ℕ)
    (U V : Submodule ℚ L) (hUV : U = V)
    (j : Fin (finrank ℚ U)) (v : V) (q : ℚ) {K : ℕ}
    (hq : RationalHeightLE q K)
    (hv : v.val = q • (chosenBoundedSubmoduleBasis e H U j).val)
    (k : Fin (finrank ℚ V)) :
    RationalHeightLE ((chosenBoundedSubmoduleBasis e H V).repr v k) K := by
  subst V
  have he : v = q • chosenBoundedSubmoduleBasis e H U j := Subtype.ext hv
  rw [he, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hb : RationalHeightLE ((chosenBoundedSubmoduleBasis e H U).repr
      (chosenBoundedSubmoduleBasis e H U j) k) 1 := by
    classical
    rw [Basis.repr_self]
    by_cases hkj : k = j <;> simp [hkj, RationalHeightLE]
  simpa only [Nat.mul_one] using hq.mul hb

end Erdos3

end

section

namespace Erdos3

open Module

variable {L μ υ ν : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def homogeneousIntersectionSystem (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule ℚ L) (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V)) :
    L →ₗ[ℚ] (υ ⊕ ν ⊕ μ → ℚ) :=
  LinearMap.pi fun
    | .inl i => (fU.coord i).comp U.mkQ
    | .inr (.inl i) => (fV.coord i).comp V.mkQ
    | .inr (.inr i) => (b.coord i).comp (basisGradeProjection b w j - LinearMap.id)

theorem homogeneousIntersectionSystem_ker (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule ℚ L) (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V)) :
    LinearMap.ker (homogeneousIntersectionSystem b w j U V fU fV) = homogeneousIntersection b w j U V := by
  ext x
  rw [LinearMap.mem_ker, mem_homogeneousIntersection]
  constructor
  · intro hx
    refine ⟨(stepDrop_quotient_mem_iff U fU x).mpr (fun i => congrFun hx (.inl i)),
      (stepDrop_quotient_mem_iff V fV x).mpr (fun i => congrFun hx (.inr (.inl i))), ?_⟩
    apply sub_eq_zero.mp
    apply b.repr.injective
    ext i
    have hi := congrFun hx (.inr (.inr i))
    change b.repr (basisGradeProjection b w j x - x) i = 0 at hi
    simpa only [map_zero, Finsupp.zero_apply] using hi
  · rintro ⟨hU, hV, hj⟩
    funext i
    rcases i with i | i | i
    · exact (stepDrop_quotient_mem_iff U fU x).mp hU i
    · exact (stepDrop_quotient_mem_iff V fV x).mp hV i
    · change b.repr (basisGradeProjection b w j x - x) i = 0
      rw [hj, sub_self, map_zero]
      rfl

theorem homogeneousIntersectionSystem_basis_height (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule ℚ L) (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V))
    {H : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i k, RationalHeightLE (fU.repr (U.mkQ (b k)) i) H)
    (hV : ∀ i k, RationalHeightLE (fV.repr (V.mkQ (b k)) i) H)
    (i : υ ⊕ ν ⊕ μ) (k : μ) :
    RationalHeightLE (homogeneousIntersectionSystem b w j U V fU fV (b k) i) H := by
  classical
  rcases i with i | i | i
  · exact hU i k
  · exact hV i k
  · change RationalHeightLE (b.repr (basisGradeProjection b w j (b k) - b k) i) H
    have hp : basisGradeProjection b w j (b k) = if w k = j then b k else 0 :=
      basisCoordinateProjection_basis b {i | w i = j} k
    rw [hp]
    split_ifs
    · simpa only [sub_self, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
    · simpa only [zero_sub, map_neg, Finsupp.neg_apply] using (basis_repr_height_one b k i).neg.mono hH

def homogeneousIntersectionBasisHeight (n r H : ℕ) : ℕ :=
  (n + 1) * rationalKernelHeight r H ^ n

theorem exists_homogeneousIntersection_basis [Fintype μ] [Fintype υ] [Fintype ν]
    (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ) (U V : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V)) {H r : ℕ}
    (hH : 1 ≤ H) (hr : Fintype.card υ + Fintype.card ν + Fintype.card μ ≤ r)
    (hU : ∀ i k, RationalHeightLE (fU.repr (U.mkQ (b k)) i) H)
    (hV : ∀ i k, RationalHeightLE (fV.repr (V.mkQ (b k)) i) H) :
    ∃ e : Basis (Fin (Module.finrank ℚ (homogeneousIntersection b w j U V)))
      ℚ (homogeneousIntersection b w j U V), ∀ i k,
      RationalHeightLE (b.repr (e i : L) k) (homogeneousIntersectionBasisHeight (Fintype.card μ) r H) := by
  classical
  let P := homogeneousIntersectionSystem b w j U V fU fV
  have hP : ∀ i k, RationalHeightLE ((Pi.basisFun ℚ (υ ⊕ ν ⊕ μ)).repr (P (b i)) k) H := by
    intro i k
    change RationalHeightLE (P (b i) k) H
    exact homogeneousIntersectionSystem_basis_height b w j U V fU fV hH hU hV k i
  obtain ⟨t, ht, v, hspan, hv⟩ := exists_bounded_span_kernel_generators b
    (Pi.basisFun ℚ (υ ⊕ ν ⊕ μ)) P b hH (basis_repr_height_one b) hP
  have htr : t ≤ r := by
    simp only [Fintype.card_sum] at ht
    omega
  have hspan' : Submodule.span ℚ (Set.range v) = homogeneousIntersection b w j U V := by
    simpa only [b.span_eq, top_inf_eq, P, homogeneousIntersectionSystem_ker] using hspan
  have hv' : ∀ i k, RationalHeightLE (b.repr (v i) k)
      (homogeneousIntersectionBasisHeight (Fintype.card μ) r H) := by
    intro i k
    apply (hv i k).mono
    simp only [homogeneousIntersectionBasisHeight, mul_one]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (rationalKernelHeight_mono hH htr) _)
  exact exists_bounded_submodule_basis_from_spanning b _ v hspan' hv'

end Erdos3

end

section

namespace Erdos3

theorem rankQuotientHeight_le_exp (n m q u H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hu : (u : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rankQuotientHeight n m q u H : ℝ) ≤ Real.exp ((p + 2) ^ 424) := by
  let Q := rationalKernelHeight m H
  let E := rankQuotientLayerHeight n m H
  let V := (n + 1) * (H * H) ^ n
  let P := (p + 2) ^ 51
  have hpP : p ≤ P := le_power_budget hp (by decide : 1 ≤ 51)
  have hP : 0 ≤ P := hp.trans hpP
  have hbase : 1 ≤ p + 2 := by linarith
  have hQ : (Q : ℝ) ≤ Real.exp ((p + 2) ^ 7) := rationalKernelHeight_le_budget m H hp hm hH
  have hH7 : (H : ℝ) ≤ Real.exp ((p + 2) ^ 7) :=
    hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide)))
  have hprod {A B : ℕ} (hA : (A : ℝ) ≤ Real.exp ((p + 2) ^ 7))
      (hB : (B : ℝ) ≤ Real.exp ((p + 2) ^ 7)) :
      ((A * B : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 8) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 7) * Real.exp ((p + 2) ^ 7) :=
        mul_le_mul hA hB (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * (p + 2) ^ 7) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        calc
          _ ≤ (p + 2) * (p + 2) ^ 7 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by ring)
  have hE10 : (E : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
    exact rational_sum_cost_le_exp n (H * Q) hp 8 1 (hprod hH7 hQ)
      (by simpa only [pow_one] using hn.trans (show p ≤ p + 2 by linarith))
  have hV10 : (V : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
    exact rational_sum_cost_le_exp n (H * H) hp 8 1 (hprod hH7 hH7)
      (by simpa only [pow_one] using hn.trans (show p ≤ p + 2 by linarith))
  have hEP : (E : ℝ) ≤ Real.exp P :=
    hE10.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 10 ≤ 51)))
  have hVP : (V : ℝ) ≤ Real.exp P :=
    hV10.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 10 ≤ 51)))
  have hfreq0 := embedding_coordinate_height_budget u u E V hP
    (hu.trans hpP) (hu.trans hpP) hEP hVP
  have hfreq : (rankQuotientFrequencyHeight n m u H : ℝ) ≤ Real.exp ((p + 2) ^ 424) :=
    exponential_budget_comp hp hP 51 8 le_rfl hfreq0
  have h51 : P ≤ (p + 2) ^ 424 := pow_le_pow_right₀ hbase (by decide : 51 ≤ 424)
  have hstructure := rationalLieQuotientStructureHeight_le_exp n m q H hp hn hm hq hH
  simp only [rankQuotientHeight, Nat.cast_max, Nat.cast_one]
  refine max_le (Real.one_le_exp (by positivity)) (max_le ?_ (max_le ?_ (max_le ?_ hfreq)))
  · exact hQ.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 7 ≤ 424)))
  · exact hstructure.trans (Real.exp_le_exp.mpr h51)
  · exact hEP.trans (Real.exp_le_exp.mpr h51)

theorem dependentQuotientHeight_le_exp (s n m q u H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hu : (u : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rankQuotientHeight n m q u (lieTreeHeight n H s) : ℝ) ≤
      Real.exp ((p + 2) ^ ((6 * s + 4) * 424)) := by
  let P := (p + 2) ^ (6 * s + 2)
  have hpP : p ≤ P := le_power_budget hp (by omega : 1 ≤ 6 * s + 2)
  have hP : 0 ≤ P := hp.trans hpP
  have h := rankQuotientHeight_le_exp n m q u (lieTreeHeight n H s) hP
    (hn.trans hpP) (hm.trans hpP) (hq.trans hpP) (hu.trans hpP)
    (lieTreeHeight_le_exp n H s hp hn hH)
  have hc := exponential_budget_comp hp hP (6 * s + 2) 424 le_rfl h
  simpa only [show 6 * s + 2 + 2 = 6 * s + 4 by omega] using hc

end Erdos3

end

end OAI
