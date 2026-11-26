import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelCompactName
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactZeroWidth

/-!
# Actual unit-kernel compact panel additivity

Native containment derives every subpanel's original compact source at
the same denominator, margin and parameter. Positive widths use the
original compact additivity theorem. Literal zero-width observations and
the actual normalized addition laws handle both degenerate splits.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelPanelAdditivity

open_ipra
open GaussianEulerUnitKernelCompactName (source nameF data evaluatorF fixedData lipschitz compact_input name_regular)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl cross_to_diagonal)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameRingLaws (zeroF zero_fast)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem subpanel_source (z R B a C a' C' E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G)
    (hl : Γ ⊢[PRAAx] le a a') (hr : Γ ⊢[PRAAx] le (a'+C') (a+C)) : Γ ⊢[PRAAx]
    source z R B a' C' E G := by
  have lower := le_trans h.andE₂.andE₂.andE₁
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl G) hl)
  have upper := le_trans (add_le_add₂ (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl G) hr) (le_refl E)) h.andE₂.andE₂.andE₂
  exact .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI lower upper))

theorem left_source (z R B a C1 C2 E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a (C1+C2) E G) : Γ ⊢[PRAAx]
    source z R B a C1 E G :=
  subpanel_source z R B a (C1+C2) a C1 E G h (le_refl a)
    (le_of_eq_add (d := C2) (by ipra_ring))

theorem right_source (z R B a C1 C2 E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a (C1+C2) E G) : Γ ⊢[PRAAx]
    source z R B (a+C1) C2 E G :=
  subpanel_source z R B a (C1+C2) (a+C1) C2 E G h (le_add_right a C1) (le_of_eq_add (d := zero) (by ipra_ring))

theorem data_congr (z R B a C a' C' E G : PTm n) (ha : Γ ⊢[PRAAx] a ≐ a') (hC : Γ ⊢[PRAAx] C ≐ C') : Γ ⊢[PRAAx]
    data z R B a C E G ≐ data z R B a' C' E G := by
  have e1 : Γ ⊢[PRAAx] data z R B a C E G ≐ data z R B a' C E G := by
    simpa only [GaussianEulerUnitKernelCompactName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0) (Syn.shift C) (Syn.shift E) (Syn.shift G)) ha
  have e2 : Γ ⊢[PRAAx] data z R B a' C E G ≐ data z R B a' C' E G := by
    simpa only [GaussianEulerUnitKernelCompactName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a') (var 0) (Syn.shift E) (Syn.shift G)) hC
  exact e1.eqTrans e2

private theorem exact_data_cross (F : PR 2) (x y : PTm n)
    (hx : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN F x) (hy : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN F y)
    (he : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] crossEquivalent F F x y := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ hx hy
  have es : Γ.map Fm.shift ⊢[PRAAx] Syn.shift x ≐ Syn.shift y := by simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using congrAp2 F (.eqRefl (var 0)) es

private theorem cross_data_congr (F H : PR 2) (x y x' y' : PTm n)
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') (h : Γ ⊢[PRAAx] crossEquivalent F H x y) :
    Γ ⊢[PRAAx] crossEquivalent F H x' y' := by
  simpa using Prf.eqSubst (crossEquivalent F H (var 0) (var 1) : Fm PTm 2) ![x,y] ![x',y']
    (fun i => by fin_cases i; exact hx; exact hy) (by simpa using h)

def addedData (z R B a C1 C2 E G : PTm n) : PTm n :=
  addData (data z R B a C1 E G) (data z R B (a+C1) C2 E G)
ipra_subst addedData

theorem addedData_congr (z R B a C1 C2 D1 D2 E G : PTm n)
    (h1 : Γ ⊢[PRAAx] C1 ≐ D1) (h2 : Γ ⊢[PRAAx] C2 ≐ D2) : Γ ⊢[PRAAx]
    addedData z R B a C1 C2 E G ≐ addedData z R B a D1 D2 E G :=
  congrPairT (.eqRefl two) (congrPairT (data_congr z R B a C1 a D1 E G (.eqRefl _) h1)
    (data_congr z R B (a+C1) C2 (a+D1) D2 E G (congrAdd (.eqRefl _) h1) h2))

private theorem zero_left (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a (zero+C) E G) : Γ ⊢[PRAAx]
    crossEquivalent nameF (addF nameF nameF) (data z R B a (zero+C) E G) (addedData z R B a zero C E G) := by
  let x := data z R B a (zero+C) E G
  let y := data z R B a zero E G
  let w := data z R B (a+zero) C E G
  have hf := name_regular z R B a (zero+C) E G h
  have hl := name_regular z R B a zero E G (left_source _ _ _ _ _ _ _ _ h)
  have hr := name_regular z R B (a+zero) C E G (right_source _ _ _ _ _ _ _ _ h)
  have hz := GaussianCompactZeroWidth.name_zero evaluatorF a E (lipschitz R G) one (fixedData z B) x
    (compact_input z R B a zero E G (left_source _ _ _ _ _ _ _ _ h))
  have he : Γ ⊢[PRAAx] w ≐ x := data_congr z R B (a+zero) C a (zero+C) E G (by ipra_ring) (by ipra_ring)
  have hw := exact_data_cross nameF w x hr hf he
  have sums := GaussianNameArithmetic.add_equivalent nameF zeroF nameF nameF y x w x hl (zero_fast x) hr hf
    (cross_to_diagonal _ _ _ _ hz) (cross_to_diagonal _ _ _ _ hw)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ sums (GaussianNameRingLaws.add_zero_left nameF x hf))

private theorem zero_right (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a (C+zero) E G) : Γ ⊢[PRAAx]
    crossEquivalent nameF (addF nameF nameF) (data z R B a (C+zero) E G) (addedData z R B a C zero E G) := by
  let x := data z R B a (C+zero) E G
  let y := data z R B a C E G
  let w := data z R B (a+C) zero E G
  have hf := name_regular z R B a (C+zero) E G h
  have hl := name_regular z R B a C E G (left_source _ _ _ _ _ _ _ _ h)
  have hr := name_regular z R B (a+C) zero E G (right_source _ _ _ _ _ _ _ _ h)
  have hz := GaussianCompactZeroWidth.name_zero evaluatorF (a+C) E (lipschitz R G) one (fixedData z B) x
    (compact_input z R B (a+C) zero E G (right_source _ _ _ _ _ _ _ _ h))
  have he : Γ ⊢[PRAAx] y ≐ x := data_congr z R B a C a (C+zero) E G (.eqRefl _) (by ipra_ring)
  have hy := exact_data_cross nameF y x hl hf he
  have sums := GaussianNameArithmetic.add_equivalent nameF nameF nameF zeroF y x w x hl hf hr (zero_fast x)
    (cross_to_diagonal _ _ _ _ hy) (cross_to_diagonal _ _ _ _ hz)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ sums (GaussianNameRingLaws.add_zero nameF x hf))

theorem positive_additivity_input (z R B a C1 C2 E G : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a (C1+C2) E G) (h1 : Γ ⊢[PRAAx] le one C1) (h2 : Γ ⊢[PRAAx] le one C2) : Γ ⊢[PRAAx]
    GaussianCompactNamedAdditivity.input evaluatorF a C1 C2 E (lipschitz R G) one (fixedData z B) := by
  have original := compact_input z R B a (C1+C2) E G h
  exact .andI original.andE₁ (.andI original.andE₂.andE₁ (.andI h1 (.andI h2 (.andI original.andE₂.andE₂.andE₁ original.andE₂.andE₂.andE₂))))

theorem original_additivity (z R B a C1 C2 E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a (C1+C2) E G) : Γ ⊢[PRAAx]
    crossEquivalent nameF (addF nameF nameF) (data z R B a (C1+C2) E G) (addedData z R B a C1 C2 E G) := by
  refine .orE (zero_or_succ C1) ?_ ?_
  · have hs : (C1 ≐ zero) :: Γ ⊢[PRAAx] source z R B a (zero+C2) E G := by
      exact subpanel_source z R B a (C1+C2) a (zero+C2) E G h.wk (le_refl a)
        (le_of_eq_add (d := C1) (by ipra_ring))
    have law := zero_left z R B a C2 E G hs
    exact cross_data_congr _ _ _ _ _ _
      (data_congr z R B a (zero+C2) a (C1+C2) E G (.eqRefl _) (congrAdd Prf.hyp0.eqSymm (.eqRefl _)))
      (addedData_congr z R B a zero C2 C1 C2 E G Prf.hyp0.eqSymm (.eqRefl _)) law
  · refine .orE (zero_or_succ C2) ?_ ?_
    · have hs : (C2 ≐ zero) :: (C1 ≐ ConciseIPRA.PTm.succ (pred C1)) :: Γ ⊢[PRAAx] source z R B a (C1+zero) E G :=
        subpanel_source z R B a (C1+C2) a (C1+zero) E G h.wk.wk (le_refl a)
          (le_of_eq_add (d := C2) (by ipra_ring))
      have law := zero_right z R B a C1 E G hs
      exact cross_data_congr _ _ _ _ _ _
        (data_congr z R B a (C1+zero) a (C1+C2) E G (.eqRefl _) (congrAdd (.eqRefl _) Prf.hyp0.eqSymm))
        (addedData_congr z R B a C1 zero C1 C2 E G (.eqRefl _) Prf.hyp0.eqSymm) law
    · have h1 : (C2 ≐ ConciseIPRA.PTm.succ (pred C2)) :: (C1 ≐ ConciseIPRA.PTm.succ (pred C1)) :: Γ ⊢[PRAAx] le one C1 :=
        le_congr (.eqRefl _) Prf.hyp1.eqSymm (zero_lt_succ (pred C1))
      have h2 : (C2 ≐ ConciseIPRA.PTm.succ (pred C2)) :: (C1 ≐ ConciseIPRA.PTm.succ (pred C1)) :: Γ ⊢[PRAAx] le one C2 :=
        le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred C2))
      exact GaussianCompactNamedAdditivity.name_additivity evaluatorF a C1 C2 E (lipschitz R G) one (fixedData z B)
        (positive_additivity_input z R B a C1 C2 E G h.wk.wk h1 h2)

def threeData (z R B a C1 C2 C3 E G : PTm n) : PTm n := addData (data z R B a C1 E G)
  (addData (data z R B (a+C1) C2 E G) (data z R B ((a+C1)+C2) C3 E G))
ipra_subst threeData

/-- The actual normalized sum is right-associated. Every panel retains
the same native denominator, margin, evaluator and parameter datum. -/
theorem original_three_split (z R B a C1 C2 C3 E G : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a (C1+(C2+C3)) E G) : Γ ⊢[PRAAx]
    crossEquivalent nameF (addF nameF (addF nameF nameF))
      (data z R B a (C1+(C2+C3)) E G) (threeData z R B a C1 C2 C3 E G) := by
  have left := left_source z R B a C1 (C2+C3) E G h
  have tail := right_source z R B a C1 (C2+C3) E G h
  have middle := left_source z R B (a+C1) C2 C3 E G tail
  have right := right_source z R B (a+C1) C2 C3 E G tail
  have first := original_additivity z R B a C1 (C2+C3) E G h
  have second := original_additivity z R B (a+C1) C2 C3 E G tail
  have hl := name_regular z R B a C1 E G left
  have ht := name_regular z R B (a+C1) (C2+C3) E G tail
  have summed := add_fast nameF nameF _ _ (name_regular z R B (a+C1) C2 E G middle)
    (name_regular z R B ((a+C1)+C2) C3 E G right)
  have lift := GaussianNameArithmetic.add_equivalent nameF nameF nameF (addF nameF nameF)
    (data z R B a C1 E G) (data z R B a C1 E G) (data z R B (a+C1) (C2+C3) E G)
    (addedData z R B (a+C1) C2 C3 E G) hl hl ht summed
    (GaussianNameEquivalence.diagonal_refl _ _) (cross_to_diagonal _ _ _ _ second)
  exact cross_trans _ _ _ _ _ _ first lift

theorem original_three_observations (p q z R B a C1 C2 C3 E G : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a (C1+(C2+C3)) E G) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 nameF p (data z R B a (C1+(C2+C3)) E G))
      (ap2 (addF nameF (addF nameF nameF)) q (threeData z R B a C1 C2 C3 E G))
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  GaussianNameEquivalence.cross_at _ _ _ _ p q (original_three_split z R B a C1 C2 C3 E G h)

theorem actual_original_unit_kernel_zero_safe_additivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4+var 5) (var 6) (var 7) ⟶
      crossEquivalent nameF (addF nameF nameF) (data (var 0) (var 1) (var 2) (var 3) (var 4+var 5) (var 6) (var 7))
        (addedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (original_additivity _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_unit_kernel_zero_safe_three_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4+(var 5+var 6)) (var 7) (var 8) ⟶
      crossEquivalent nameF (addF nameF (addF nameF nameF))
        (data (var 0) (var 1) (var 2) (var 3) (var 4+(var 5+var 6)) (var 7) (var 8))
        (threeData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (original_three_split _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelPanelAdditivity
