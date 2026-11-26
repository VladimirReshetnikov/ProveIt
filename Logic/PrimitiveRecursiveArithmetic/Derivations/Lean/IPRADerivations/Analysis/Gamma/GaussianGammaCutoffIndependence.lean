import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaAdjacentCutoff
import IPRADerivations.Core.CongruenceTactic

/-!
# Independence of every valid numerical cutoff in the original C7 name

At a fixed requested precision, genuine QF induction accumulates the
actual adjacent-name distance with bound 2j/2^p. The resulting computed
constant 2D is removed by the existing finite-envelope theorem. The
induction never uses a quantified name equivalence as its invariant.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCutoffIndependence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCutoffName (nameF data sample)
open GaussianGammaCanonicalTailName (source)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem source_after (z R B N j : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] source z R B (N+j) :=
  .andI h.andE₁ (.andI (le_trans h.andE₂.andE₁ (le_add_right N j))
    (.andI h.andE₂.andE₂.andE₁ (le_trans h.andE₂.andE₂.andE₂ (le_add_right N j))))

theorem data_cutoff_congr (z R B : PTm n) {N M : PTm n} (h : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] data z R B N ≐ data z R B M := by
  ipra_congr (data (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl z, .eqRefl R, .eqRefl B, h]
theorem sample_cutoff_congr (p z R B : PTm n) {N M : PTm n} (h : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] sample p z R B N ≐ sample p z R B M :=
  congrAp2 nameF (.eqRefl p) (data_cutoff_congr z R B h)

def prefixLaw (p z R B N j : PTm n) : Fm PTm n :=
  distanceBounded (sample p z R B N) (sample p z R B (N+j)) (two*j) (unit p)
@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (p z R B N j : PTm n) :
    (prefixLaw p z R B N j).subst σ = prefixLaw (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ j) := by simp [prefixLaw]

theorem prefix_zero (p z R B N : PTm n) : Γ ⊢[PRAAx] prefixLaw p z R B N zero :=
  distance_congr (.eqRefl _) (sample_cutoff_congr p z R B (by ipra_ring)) (by ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero (sample p z R B N) (unit p) (unit_positive p))

theorem prefix_step (p z R B N j : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (ih : Γ ⊢[PRAAx] prefixLaw p z R B N j) : Γ ⊢[PRAAx] prefixLaw p z R B N (succ j) := by
  have next := GaussianNameEquivalence.diagonal_at nameF nameF (data z R B (N+j)) (data z R B (succ (N+j))) p
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _
      (GaussianGammaAdjacentCutoff.adjacent_cutoff_equivalent z R B (N+j) (source_after z R B N j h)))
  exact distance_congr (.eqRefl _) (sample_cutoff_congr p z R B (by ipra_ring)) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) ih next)

/-- The invariant is one atomic rational metric comparison at fixed p.
All cutoff data and all adjacent inputs are the actual original programs. -/
theorem prefix_distance (p z R B N D : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] prefixLaw p z R B N D := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift p) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ (by unfold prefixLaw GaussianRationalMetric.distanceBounded GaussianRationalMetric.bounded RationalArgmin.rationalLE; exact le_QF _ _) ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero (Γ := Γ) p z R B N
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact prefix_step _ _ _ _ _ _ hs.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE D

theorem cutoff_envelope (z R B N D : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal nameF nameF (data z R B N) (data z R B (N+D)) (two*D) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,prefixLaw,sample,Syn.shift,
    GaussianGammaCutoffName.subst_data,PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    prefix_distance (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) (Syn.shift D) hs

/-- Arbitrary numerical offset D, obtained without induction on a
quantified equivalence or an unbounded semantic predicate. -/
theorem offset_equivalence (z R B N D : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z R B N) (data z R B (N+D)) :=
  GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (two*D)
    (GaussianGammaCutoffName.name_regular z R B N h)
    (GaussianGammaCutoffName.name_regular z R B (N+D) (source_after z R B N D h)) (cutoff_envelope z R B N D h)

theorem ordered_equivalence (z R B N M : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (hNM : Γ ⊢[PRAAx] le N M) : Γ ⊢[PRAAx] crossEquivalent nameF nameF (data z R B N) (data z R B M) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  have hm : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift M)) := by
    simpa [Fm.shift,Syn.shift] using hNM.shift.shift
  have bound := GaussianNameEquivalence.cross_at nameF nameF _ _ (var 1) (var 0)
    (offset_equivalence _ _ _ _ (monus (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift N))) hs)
  simpa only [crossEquivalent,Syn.shift,GaussianGammaCutoffName.subst_data] using
    distance_congr (.eqRefl _) (congrAp2 nameF (.eqRefl _)
      (data_cutoff_congr _ _ _ (eq_add_of_le hm).eqSymm)) (.eqRefl _) (.eqRefl _) bound

theorem valid_cutoffs_equivalent (z R B N M : PTm n) (hN : Γ ⊢[PRAAx] source z R B N)
    (hM : Γ ⊢[PRAAx] source z R B M) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z R B N) (data z R B M) :=
  .orE (le_total N M) (ordered_equivalence z R B N M hN.wk Prf.hyp0)
    (cross_symm _ _ _ _ (ordered_equivalence z R B M N hM.wk Prf.hyp0))

/-- The actual original C7 name at 2R agrees with every sufficiently
large numerical cutoff in the original source disk. -/
theorem original_C7_cutoff_equivalent (z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) (hN : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF nameF (GaussianGammaC7Name.data z R B) (data z R B N) :=
  ordered_equivalence z R B (two*R) N (GaussianGammaCanonicalExponent.tail_source z R B h) hN

/-! Actual numerical supplier, retaining both data and the proved budget. -/
def output (z R B N D : PTm n) : PTm n := pairT (data z R B N) (pairT (data z R B (N+D)) (two*D))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (z R B N D : PTm n) : PTm n := PTm.app outputF ![z,R,B,N,D]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (z R B N D : PTm n) :
    Syn.subst σ (output z R B N D) = output (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ D) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (z R B N D : PTm n) :
    Syn.subst σ (run z R B N D) = run (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ D) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (z R B N D : PTm n) : Γ ⊢[PRAAx] run z R B N D ≐ output z R B N D := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![z,R,B,N,D]
theorem returned_first (z R B N D : PTm n) : Γ ⊢[PRAAx] fstT (run z R B N D) ≐ data z R B N :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (z R B N D : PTm n) : Γ ⊢[PRAAx] sndT (run z R B N D) ≐ pairT (data z R B (N+D)) (two*D) :=
  (congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_second (z R B N D : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run z R B N D)) ≐ data z R B (N+D) :=
  (congrFst (returned_tail _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_budget (z R B N D : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run z R B N D)) ≐ two*D :=
  (congrSnd (returned_tail _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_equivalence (z R B N D : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (fstT (run z R B N D)) (fstT (sndT (run z R B N D))) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  have bound := GaussianNameEquivalence.cross_at nameF nameF _ _ (var 1) (var 0)
    (offset_equivalence _ _ _ _ (Syn.shift (Syn.shift D)) hs)
  simpa only [crossEquivalent,Syn.shift,subst_run,subst_fstT,subst_sndT] using
    distance_congr (congrAp2 nameF (.eqRefl _) (returned_first _ _ _ _ _).eqSymm)
      (congrAp2 nameF (.eqRefl _) (returned_second _ _ _ _ _).eqSymm) (.eqRefl _) (.eqRefl _) bound

theorem original_fixed_precision_cutoff_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) ⟶ prefixLaw (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (prefix_distance _ _ _ _ _ _ Prf.hyp0))
theorem original_numerical_cutoff_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ GaussianValueNormalizerExtensionality.rawDiagonal nameF nameF
      (data (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3+var 4)) (two*var 4)) :=
  closeUniv 5 (.impI (cutoff_envelope _ _ _ _ _ Prf.hyp0))
theorem original_numerical_cutoff_independence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF nameF
      (data (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3+var 4))) :=
  closeUniv 5 (.impI (offset_equivalence _ _ _ _ _ Prf.hyp0))
theorem original_any_valid_cutoffs_independence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ source (var 0) (var 1) (var 2) (var 4) ⟶ crossEquivalent nameF nameF
      (data (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (valid_cutoffs_equivalent _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_C7_all_cutoffs_specialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ le (two*var 1) (var 3) ⟶
      crossEquivalent GaussianGammaC7Name.nameF nameF (GaussianGammaC7Name.data (var 0) (var 1) (var 2))
        (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (original_C7_cutoff_equivalent _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cutoff_independence_supplier_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_cutoff_independence_returned_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ two*var 4) :=
  closeUniv 5 (returned_budget _ _ _ _ _)
theorem original_returned_all_cutoffs_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF nameF
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.impI (returned_equivalence _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCutoffIndependence
