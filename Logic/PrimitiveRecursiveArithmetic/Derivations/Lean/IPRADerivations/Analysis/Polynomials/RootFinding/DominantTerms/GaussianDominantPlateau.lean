import IPRADerivations.Algebra.DescentPigeonhole
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantSelector

/-!
# An actual bounded search for three equal dominant indices

The odd-center search tests equality of the two even endpoints. The
positive finite count is obtained from the actual dominant-index bounds
and monotonicity. A failed bounded search would force every counted bit
to zero, contradicting that positive count. Thus the actual returned
center and all three actual neighboring indices are certified, without
an incoming search-success, plateau or monotonicity premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantPlateau

open_ipra
open LeanProofs.IPRA.Algebra
open LeanProofs.IPRA.Algebra.DescentPigeonhole (eB)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (input subst_input)
open LeanProofs.IPRA.Analysis.GaussianDominantSelector (index indexData subst_index subst_indexData)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Zero means that this odd center has equal even endpoints. -/
def centerBody (k : PTm 2) : PTm 2 := monus one (eB k)
def searchSlot (k : PTm 2) (N x : PTm n) : PTm n := Search.mu (centerBody k) N x

@[simp] theorem subst_searchSlot (k : PTm 2) {m : ℕ} (σ : Fin n → PTm m) (N x : PTm n) :
    Syn.subst σ (searchSlot k N x) = searchSlot k (Syn.subst σ N) (Syn.subst σ x) := by
  simp only [searchSlot,subst_ap2]

theorem center_body_at (k : PTm 2) (s x : PTm n) :
    inst2 (centerBody k) s x = monus one (inst2 (eB k) s x) := by
  simp only [centerBody,inst2,PTm.subst_monus,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]

theorem indicator_boolean (k : PTm 2) (s x : PTm n) : Γ ⊢[PRAAx]
    (inst2 (eB k) s x ≐ zero) ⋎ (inst2 (eB k) s x ≐ one) := by
  simpa only [DescentPigeonhole.inst2_e] using
    eqb_cases (Γ := Γ) (inst2 k (succ (succ (two*s))) x) (inst2 k (two*s) x)

theorem found_indicator (k : PTm 2) (s x : PTm n)
    (hf : Γ ⊢[PRAAx] inst2 (centerBody k) s x ≐ zero) : Γ ⊢[PRAAx]
    inst2 (eB k) s x ≐ one := by
  refine .orE (indicator_boolean k s x) ?_ Prf.hyp0
  have nz : (inst2 (eB k) s x ≐ zero)::Γ ⊢[PRAAx] one ≐ zero :=
    ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero one)).eqSymm.eqTrans
      (by simpa only [center_body_at] using hf.wk)
  exact succ_ne_zero' _ nz

theorem before_default_zero (k : PTm 2) (N x i : PTm n)
    (hDefault : Γ ⊢[PRAAx] searchSlot k N x ≐ N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    inst2 (eB k) i x ≐ zero := by
  have minimal : Γ ⊢[PRAAx] neg (inst2 (centerBody k) i x ≐ zero) :=
    Search.search_minimal (lt_congr (.eqRefl _) hDefault.eqSymm hi)
  refine .orE (indicator_boolean k i x) Prf.hyp0 ?_
  have zeroTest : (inst2 (eB k) i x ≐ one)::Γ ⊢[PRAAx] inst2 (centerBody k) i x ≐ zero := by
    rw [center_body_at]
    exact (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self one)
  exact .botE _ (.impE minimal.wk zeroTest)

/-- Failure of the actual search forces the actual counted finite sum
to vanish. This is an object proof about every tested original bit. -/
theorem default_count_zero (k : PTm 2) (N x : PTm n)
    (hDefault : Γ ⊢[PRAAx] searchSlot k N x ≐ N) : Γ ⊢[PRAAx]
    ap2 (sumF (eB k)) N x ≐ zero := by
  apply sum_zero_of_bounded (eB k) x N
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] searchSlot k (Syn.shift N) (Syn.shift x) ≐ Syn.shift N := by
    simpa only [Fm.shift,Fm.subst_eq,subst_searchSlot,Syn.shift] using hDefault.shift
  exact before_default_zero k (Syn.shift N) (Syn.shift x) (var 0) hs.wk Prf.hyp0

/-- A derived positive count guarantees this bounded program succeeds;
the count is a transparent generic-helper premise only. -/
theorem positive_count_search (k : PTm 2) (N x : PTm n)
    (hCount : Γ ⊢[PRAAx] le one (ap2 (sumF (eB k)) N x)) : Γ ⊢[PRAAx]
    lt (searchSlot k N x) N ⋏ inst2 (eB k) (searchSlot k N x) x ≐ one := by
  have spec := Search.search_spec (Γ := Γ) (f := centerBody k) N zero x
  refine .orE (lt_or_eq_of_le (Prf.andE₁ spec)) ?_ ?_
  · exact .andI Prf.hyp0 (found_indicator k _ _ (.impE (Prf.andE₁ (Prf.andE₂ spec)).wk Prf.hyp0))
  · have countZero := default_count_zero k N x (Prf.hyp0 : (searchSlot k N x ≐ N)::Γ ⊢[PRAAx] searchSlot k N x ≐ N)
    exact not_succ_le_self zero _ (le_congr (.eqRefl _) countZero hCount.wk)

/-! The actual source selector is fixed syntax. Only the original list,
degree, scale index and search counters are numerical input data. -/
def indexBody : PTm 2 := ap2 GaussianDominantSelector.indexF (var 0) (var 1)
def count (C N : PTm n) : PTm n := ap2 (sumF (eB indexBody)) N (indexData C N)
def centerSlot (C N : PTm n) : PTm n := searchSlot indexBody N (indexData C N)
def center (C N : PTm n) : PTm n := succ (two*centerSlot C N)
def winner (C N : PTm n) : PTm n := index C N (center C N)
def leftIndex (C N : PTm n) : PTm n := index C N (two*centerSlot C N)
def rightIndex (C N : PTm n) : PTm n := index C N (succ (center C N))

ipra_subst count
ipra_subst centerSlot
ipra_subst center
ipra_subst winner
ipra_subst leftIndex
ipra_subst rightIndex

theorem index_body_at (C N h : PTm n) : Γ ⊢[PRAAx]
    inst2 indexBody h (indexData C N) ≐ index C N h := by
  simpa only [indexBody,inst2,subst_ap2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    GaussianDominantSelector.index_at (Γ := Γ) C N h

/-- Both adjacent monotonicity comparisons are derived from the actual
maximizing selector, rather than assumed as a sequence contract. -/
theorem derived_mono (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    .all (DescentPigeonhole.Mono indexBody N (indexData C N)) := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  have first : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx]
      le (index (Syn.shift C) (Syn.shift N) (succ (two*var 0)))
        (index (Syn.shift C) (Syn.shift N) (two*var 0)) :=
    GaussianDominantSelector.index_monotone_step (Syn.shift C) (Syn.shift N) (two*var 0) hs.wk
  have second : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx]
      le (index (Syn.shift C) (Syn.shift N) (succ (succ (two*var 0))))
        (index (Syn.shift C) (Syn.shift N) (succ (two*var 0))) :=
    GaussianDominantSelector.index_monotone_step (Syn.shift C) (Syn.shift N) (succ (two*var 0)) hs.wk
  have pair := Prf.andI
    (le_congr (index_body_at (Syn.shift C) (Syn.shift N) (succ (two*var 0))).eqSymm
      (index_body_at (Syn.shift C) (Syn.shift N) (two*var 0)).eqSymm first)
    (le_congr (index_body_at (Syn.shift C) (Syn.shift N) (succ (succ (two*var 0)))).eqSymm
      (index_body_at (Syn.shift C) (Syn.shift N) (succ (two*var 0))).eqSymm second)
  simpa only [Syn.shift,subst_indexData] using pair

theorem positive_center_count (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] le one (count C N) := by
  have initial := Prf.andE₂ (GaussianDominantSelector.index_bounds C N (two*zero) h)
  have terminal := Prf.andE₁ (GaussianDominantSelector.index_bounds C N (two*N) h)
  exact DescentPigeonhole.good_center indexBody (derived_mono C N h)
    (le_congr (index_body_at C N (two*zero)).eqSymm (.eqRefl _) initial)
    (le_congr (.eqRefl _) (index_body_at C N (two*N)).eqSymm terminal)

theorem center_search_success (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    lt (centerSlot C N) N ⋏ inst2 (eB indexBody) (centerSlot C N) (indexData C N) ≐ one :=
  positive_count_search indexBody N (indexData C N) (positive_center_count C N h)

theorem slot_bounded (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] lt (centerSlot C N) N :=
  Prf.andE₁ (center_search_success C N h)

theorem center_positive (C N : PTm n) : Γ ⊢[PRAAx] le one (center C N) := zero_lt_succ _

theorem center_bounded (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] lt (center C N) (two*N) :=
  le_congr (DescentPigeonhole.two_succ (centerSlot C N)) (.eqRefl _)
    (le_mul_mono (le_refl two) (slot_bounded C N h))

theorem before_center (C N : PTm n) : Γ ⊢[PRAAx] PTm.pred (center C N) ≐ two*centerSlot C N := pred_succ _

/-- The two endpoint equality bit and the genuine selector monotonicity
derive equality of all three actually selected original coefficient indices. -/
theorem triple_indices (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    leftIndex C N ≐ winner C N ⋏ winner C N ≐ rightIndex C N := by
  have mono := Prf.allE (centerSlot C N) (derived_mono C N h)
  simp only [Fm.subst_imp,Fm.subst_and,subst_lt,subst_le,subst_inst2,subst_indexData,Syn.subst_var,
    Syn.inst_zero,Syn.subst_inst_shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,PTm.subst_mul] at mono
  have actual := DescentPigeonhole.triple_of_center indexBody
    (.impE mono (slot_bounded C N h)) (Prf.andE₂ (center_search_success C N h))
  exact .andI
    ((index_body_at C N (two*centerSlot C N)).eqSymm.eqTrans
      ((Prf.andE₁ actual).eqTrans (index_body_at C N (center C N))))
    ((index_body_at C N (center C N)).eqSymm.eqTrans
      ((Prf.andE₂ actual).eqTrans (index_body_at C N (succ (center C N)))))

theorem winner_bounds (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    le one (winner C N) ⋏ le (winner C N) N :=
  GaussianDominantSelector.index_bounds C N (center C N) h

def certificate (C N : PTm n) : Fm PTm n := lt (centerSlot C N) N ⋏
  (le one (center C N) ⋏ (lt (center C N) (two*N) ⋏
    ((le one (winner C N) ⋏ le (winner C N) N) ⋏
      (leftIndex C N ≐ winner C N ⋏ winner C N ≐ rightIndex C N))))

ipra_subst certificate

theorem plateau_correct (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] certificate C N :=
  .andI (slot_bounded C N h) (.andI (center_positive C N) (.andI (center_bounded C N h)
    (.andI (winner_bounds C N h) (triple_indices C N h))))

/-! The actual PR2 output carries the center, winning coefficient index,
two neighboring actual indices, and the bounded odd-center slot. -/
def output (C N : PTm n) : PTm n := pairT (center C N)
  (pairT (winner C N) (pairT (leftIndex C N) (pairT (rightIndex C N) (centerSlot C N))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (C N : PTm n) : PTm n := ap2 outputF C N

ipra_subst output
ipra_subst run

theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] run C N ≐ output C N := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![C,N]

theorem returned_center (C N : PTm n) : Γ ⊢[PRAAx] fstT (run C N) ≐ center C N :=
  (program_at C N).fstE
theorem returned_winner (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N)) ≐ winner C N :=
  (program_at C N).sndE.fstE
theorem returned_left (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N))) ≐ leftIndex C N :=
  (program_at C N).sndE.sndE.fstE
theorem returned_right (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run C N)))) ≐ rightIndex C N :=
  (program_at C N).sndE.sndE.sndE.fstE
theorem returned_slot (C N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run C N)))) ≐ centerSlot C N :=
  (program_at C N).sndE.sndE.sndE.sndE

theorem returned_triple (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run C N))) ≐ fstT (sndT (run C N)) ⋏
      fstT (sndT (run C N)) ≐ fstT (sndT (sndT (sndT (run C N)))) :=
  .andI ((returned_left C N).eqTrans ((Prf.andE₁ (triple_indices C N h)).eqTrans (returned_winner C N).eqSymm))
    ((returned_winner C N).eqTrans ((Prf.andE₂ (triple_indices C N h)).eqTrans (returned_right C N).eqSymm))

theorem positive_count_search_closed (k : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (ap2 (sumF (eB k)) (var 0) (var 1)) ⟶
      (lt (searchSlot k (var 0) (var 1)) (var 0) ⋏
        inst2 (eB k) (searchSlot k (var 0) (var 1)) (var 1) ≐ one)) :=
  closeUniv 2 (.impI (positive_count_search k _ _ Prf.hyp0))

theorem derived_index_mono_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ .all (DescentPigeonhole.Mono indexBody (var 1) (indexData (var 0) (var 1)))) :=
  closeUniv 2 (.impI (derived_mono _ _ Prf.hyp0))

theorem positive_center_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ le one (count (var 0) (var 1))) :=
  closeUniv 2 (.impI (positive_center_count _ _ Prf.hyp0))

theorem dominant_plateau_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (plateau_correct _ _ Prf.hyp0))

theorem dominant_plateau_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run (var 0) (var 1) ≐ output (var 0) (var 1)) ⋏
      ((fstT (run (var 0) (var 1)) ≐ center (var 0) (var 1)) ⋏
        ((fstT (sndT (run (var 0) (var 1))) ≐ winner (var 0) (var 1)) ⋏
          ((fstT (sndT (sndT (run (var 0) (var 1)))) ≐ leftIndex (var 0) (var 1)) ⋏
            ((fstT (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ rightIndex (var 0) (var 1)) ⋏
              sndT (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ centerSlot (var 0) (var 1)))))) :=
  closeUniv 2 (.andI (program_at _ _) (.andI (returned_center _ _) (.andI (returned_winner _ _)
    (.andI (returned_left _ _) (.andI (returned_right _ _) (returned_slot _ _))))))

theorem returned_dominant_triple_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶
      (fstT (sndT (sndT (run (var 0) (var 1)))) ≐ fstT (sndT (run (var 0) (var 1))) ⋏
        fstT (sndT (run (var 0) (var 1))) ≐ fstT (sndT (sndT (sndT (run (var 0) (var 1))))))) :=
  closeUniv 2 (.impI (returned_triple _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianDominantPlateau
