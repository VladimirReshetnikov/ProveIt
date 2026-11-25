import IPRADerivations.Foundations.ApproximateWitness
import IPRADerivations.Foundations.FiniteQueryDemand
import IPRADerivations.Foundations.SequenceComposition
import IPRADerivations.Core.CommonLemmas

/-!
# Actual finite nearest-neighbor and Hausdorff scans

Finite-demand packet, `lem:aggregate-calculus` and equation `eq:finite-cover`.
Distances are natural numerators in a common rational scale. The metric
program and its laws are fixed before proof generation; list codes, lengths,
points, parameters and error numerators are internal. Rational/vector
representations require their explicit metric/scale adapter.

The nearest neighbor is the actual least argmin, directed distance is an
actual maximum fold of minima, and the symmetric distance is their maximum.
Nonempty-list guards are retained wherever a minimum needs an entry.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteHausdorff

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.ApproximateWitness (argmin argmin_spec)
open LeanProofs.IPRA.Foundations.FiniteQueryDemand
  (finiteMaximum finiteMaximum_zero finiteMaximum_succ finiteMaximum_at)
open LeanProofs.IPRA.Foundations.DemandClosure
  (maximum subst_maximum maximum_left maximum_right maximum_le)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Probability.FiniteLaws (Mn mn_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def distance (d : PR 3) (x y p : PTm n) : PTm n := ap3 d x y p

@[simp] theorem subst_distance {m : ℕ} (σ : Fin n → PTm m) (d : PR 3) (x y p : PTm n) :
    Syn.subst σ (distance d x y p) =
      distance d (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ p) := subst_ap3 _ _ _ _ _

def pointData (z T p : PTm n) : PTm n := pairT z (pairT T p)

def score (d : PR 3) : PTm 2 :=
  distance d (fstT (var 1)) (entry (fstT (sndT (var 1))) (var 0)) (sndT (sndT (var 1)))

def nearest (d : PR 3) (z T p : PTm n) : PTm n :=
  argmin (score d) (pred (length T)) (pointData z T p)

def distanceTo (d : PR 3) (z T p : PTm n) : PTm n :=
  Mn (score d) (pred (length T)) (pointData z T p)

@[simp] theorem subst_pointData {m : ℕ} (σ : Fin n → PTm m) (z T p : PTm n) :
    Syn.subst σ (pointData z T p) = pointData (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ p) := by
  simp only [pointData, subst_pairT]

@[simp] theorem subst_nearest {m : ℕ} (σ : Fin n → PTm m) (d : PR 3) (z T p : PTm n) :
    Syn.subst σ (nearest d z T p) = nearest d (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ p) := by
  simp only [nearest, ApproximateWitness.subst_argmin, PTm.subst_pred,
    SequenceComposition.subst_length, subst_pointData]

@[simp] theorem subst_distanceTo {m : ℕ} (σ : Fin n → PTm m) (d : PR 3) (z T p : PTm n) :
    Syn.subst σ (distanceTo d z T p) = distanceTo d (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ p) := by
  simp only [distanceTo, subst_ap2, PTm.subst_pred, SequenceComposition.subst_length, subst_pointData]

theorem score_at (d : PR 3) (z T p i : PTm n) :
    Γ ⊢[PRAAx] inst2 (score d) i (pointData z T p) ≐ distance d z (entry T i) p := by
  have h := Prf.eqCongr (Γ := Γ) (distance d (var 0) (entry (var 1) (var 3)) (var 2) : PTm 4)
    (σ := ![fstT (pointData z T p), fstT (sndT (pointData z T p)),
      sndT (sndT (pointData z T p)), i]) (σ' := ![z, T, p, i])
    (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa [score, inst2, pointData] using h

alias positive_length := Common.pos_of_one_le

theorem index_le_pred {i L : PTm n} (hi : Γ ⊢[PRAAx] lt i L) :
    Γ ⊢[PRAAx] le i (pred L) := by
  have pos : Γ ⊢[PRAAx] le one L := le_trans ((succ_monus_succ zero i).eqTrans (zero_le i)) hi
  have bound := lt_congr (.eqRefl i) (positive_length pos) hi
  exact (succ_monus_succ _ _).eqSymm.eqTrans bound

theorem index_lt {i L : PTm n} (hL : Γ ⊢[PRAAx] le one L)
    (hi : Γ ⊢[PRAAx] le i (pred L)) : Γ ⊢[PRAAx] lt i L :=
  lt_congr (.eqRefl i) (positive_length hL).eqSymm ((succ_monus_succ _ _).eqTrans hi)

/-- The actual selected list index and distance, with deterministic ties. -/
theorem nearest_spec (d : PR 3) (z T p : PTm n) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] lt (nearest d z T p) (length T) ⋏
      (distance d z (entry T (nearest d z T p)) p ≐ distanceTo d z T p) := by
  have a := argmin_spec (Γ := Γ) (score d) (pred (length T)) (pointData z T p)
  exact .andI (index_lt hT (.andE₁ a))
    ((score_at d z T p (nearest d z T p)).eqSymm.eqTrans (.andE₂ a))

theorem distanceTo_le (d : PR 3) (z T p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T)) :
    Γ ⊢[PRAAx] le (distanceTo d z T p) (distance d z (entry T i) p) :=
  le_congr (.eqRefl _) (score_at d z T p i) (mn_le (score d) (index_le_pred hi))

/-- A proved finite-maximum upper bound, including its empty case. -/
theorem maximum_bound (body : PTm 2) (N x r : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 body (var 0) (Syn.shift x)) (Syn.shift r))) :
    Γ ⊢[PRAAx] le (finiteMaximum body N x) r := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      le (finiteMaximum body (var 0) (Syn.shift x)) (Syn.shift r)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, FiniteQueryDemand.subst_finiteMaximum,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .impI (le_congr (finiteMaximum_zero body x).eqSymm (.eqRefl _) (zero_le r))
    · simp only [Fm.subst_imp, subst_le, FiniteQueryDemand.subst_finiteMaximum,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶
          le (finiteMaximum body (var 0) (Syn.shift x)) (Syn.shift r)) :: Γ.map Fm.shift
      have old : Δ ⊢[PRAAx] le (finiteMaximum body (var 0) (Syn.shift x)) (Syn.shift r) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self (var 0)) Prf.hyp0)
      have next : Δ ⊢[PRAAx] le (inst2 body (var 0) (Syn.shift x)) (Syn.shift r) :=
        Prf.impE h.allOpen.wk.wk Prf.hyp0
      exact le_congr (finiteMaximum_succ body (var 0) (Syn.shift x)).eqSymm
        (.eqRefl _) (maximum_le old next)
  have atN := Prf.allE N all
  have result : Γ ⊢[PRAAx] le N N ⟶ le (finiteMaximum body N x) r := by
    simpa only [Fm.subst_imp, subst_le, FiniteQueryDemand.subst_finiteMaximum,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using atN
  exact .impE result (le_refl N)

def directedBody (d : PR 3) : PTm 2 :=
  distanceTo d (entry (fstT (var 1)) (var 0)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))

def directed (d : PR 3) (S T p : PTm n) : PTm n :=
  finiteMaximum (directedBody d) (length S) (pointData S T p)

def hausdorff (d : PR 3) (S T p : PTm n) : PTm n :=
  maximum (directed d S T p) (directed d T S p)

@[simp] theorem subst_directed {m : ℕ} (σ : Fin n → PTm m) (d : PR 3) (S T p : PTm n) :
    Syn.subst σ (directed d S T p) = directed d (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ p) := by
  simp only [directed, FiniteQueryDemand.subst_finiteMaximum,
    SequenceComposition.subst_length, subst_pointData]

@[simp] theorem subst_hausdorff {m : ℕ} (σ : Fin n → PTm m) (d : PR 3) (S T p : PTm n) :
    Syn.subst σ (hausdorff d S T p) = hausdorff d (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ p) := by
  simp only [hausdorff, subst_maximum, subst_directed]

theorem directedBody_at (d : PR 3) (S T p i : PTm n) :
    Γ ⊢[PRAAx] inst2 (directedBody d) i (pointData S T p) ≐ distanceTo d (entry S i) T p := by
  have h := Prf.eqCongr (Γ := Γ) (distanceTo d (entry (var 0) (var 3)) (var 1) (var 2) : PTm 4)
    (σ := ![fstT (pointData S T p), fstT (sndT (pointData S T p)),
      sndT (sndT (pointData S T p)), i]) (σ' := ![S, T, p, i])
    (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa [directedBody, inst2, pointData] using h

theorem distanceTo_le_directed (d : PR 3) (S T p i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] le (distanceTo d (entry S i) T p) (directed d S T p) :=
  le_congr (directedBody_at d S T p i) (.eqRefl _) (finiteMaximum_at (directedBody d) hi)

theorem nearest_error (d : PR 3) (S T p i : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] le (distance d (entry S i) (entry T (nearest d (entry S i) T p)) p)
      (directed d S T p) :=
  le_congr (Prf.andE₂ (nearest_spec d (entry S i) T p hT)).eqSymm (.eqRefl _)
    (distanceTo_le_directed d S T p i hi)

/-- The actual bounded two-sided cover syntax is reflected by BoundedSyntax. -/
def coverSyntax (d : PR 3) : BoundedSyntax.BFm 4 :=
  .all (length (var 0)) (.ex (length (var 2))
    (.le (distance d (entry (var 2) (var 1)) (entry (var 3) (var 0)) (var 5)) (var 4)))

def cover (d : PR 3) (S T r p : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift S)) ⟶
    .ex (lt (var 0) (length (Syn.shift (Syn.shift T))) ⋏
      le (distance d (entry (Syn.shift (Syn.shift S)) (var 1))
        (entry (Syn.shift (Syn.shift T)) (var 0)) (Syn.shift (Syn.shift p))) (Syn.shift (Syn.shift r))))

@[simp] theorem subst_cover {m : ℕ} (σ : Fin n → PTm m) (d : PR 3) (S T r p : PTm n) :
    (cover d S T r p).subst σ =
      cover d (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ r) (Syn.subst σ p) := by
  simp only [cover, Fm.subst_all, Fm.subst_imp, Fm.subst_ex, Fm.subst_and, subst_lt,
    subst_le, subst_distance, MasterCertificate.subst_entry, SequenceComposition.subst_length,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst,
    Syn.up_one, Syn.shift_var, Fin.succ_zero_eq_one]

theorem coverSyntax_at (d : PR 3) (S T r p : PTm n) :
    (BoundedSyntax.formula (coverSyntax d)).subst ![S, T, r, p] = cover d S T r p := by
  simp [coverSyntax, BoundedSyntax.formula, BoundedSyntax.BFm.le, cover, distance,
    Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, le, Syn.up]

def coverF (d : PR 3) : PR 4 := BoundedSyntax.bitF (coverSyntax d)

theorem cover_reflection (d : PR 3) (S T r p : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (FiniteQueryDemand.apply4 (coverF d) S T r p ≐ one) (cover d S T r p) := by
  have prog := BoundedSyntax.program_correct (Γ := Γ) (coverSyntax d) ![S, T, r, p]
  have reflect := BoundedSyntax.bounded_reflection (Γ := Γ) (coverSyntax d) ![S, T, r, p]
  rw [coverSyntax_at] at reflect
  refine (Prf.iffI (.impI (prog.eqSymm.wk.eqTrans Prf.hyp0))
    (.impI (prog.wk.eqTrans Prf.hyp0))).iffTrans reflect

/-- One bounded nearest-neighbor witness. -/
def hit (d : PR 3) (z T r p : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (length (Syn.shift T)) ⋏
    le (distance d (Syn.shift z) (entry (Syn.shift T) (var 0)) (Syn.shift p)) (Syn.shift r))

theorem hit_intro (d : PR 3) (z T r p j : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length T))
    (hd : Γ ⊢[PRAAx] le (distance d z (entry T j) p) r) :
    Γ ⊢[PRAAx] hit d z T r p := by
  refine .exI j ?_
  simpa [hit] using Prf.andI hj hd

theorem cover_at (d : PR 3) {S T r p i : PTm n}
    (h : Γ ⊢[PRAAx] cover d S T r p) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] hit d (entry S i) T r p := by
  have atI := Prf.allE i h
  simp only [cover, Fm.subst_imp, Fm.subst_ex, Fm.subst_and, subst_lt, subst_le,
    subst_distance, MasterCertificate.subst_entry, SequenceComposition.subst_length,
    Syn.subst_var, Syn.inst_zero, Syn.up_zero, Syn.up_one,
    BoundedFormulas.subst_up_shift', Syn.subst_inst_shift] at atI
  have result : Γ ⊢[PRAAx] lt i (length S) ⟶ hit d (entry S i) T r p := by
    simpa only [hit, Syn.shift, MasterCertificate.subst_entry] using atI
  exact .impE result hi

theorem minimum_of_hit (d : PR 3) {z T r p : PTm n} (h : Γ ⊢[PRAAx] hit d z T r p) :
    Γ ⊢[PRAAx] le (distanceTo d z T p) r := by
  refine .exE h ?_
  let A : Fm PTm (n + 1) := lt (var 0) (length (Syn.shift T)) ⋏
    le (distance d (Syn.shift z) (entry (Syn.shift T) (var 0)) (Syn.shift p)) (Syn.shift r)
  have index : (A :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (length (Syn.shift T)) := .andE₁ Prf.hyp0
  have bound : (A :: Γ.map Fm.shift) ⊢[PRAAx]
      le (distanceTo d (Syn.shift z) (Syn.shift T) (Syn.shift p)) (Syn.shift r) :=
    le_trans (distanceTo_le d _ _ _ _ index) (.andE₂ Prf.hyp0)
  simpa only [A, Fm.shift, subst_le, subst_distanceTo, Syn.shift] using bound

theorem hit_of_minimum (d : PR 3) {z T r p : PTm n}
    (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] le (distanceTo d z T p) r) : Γ ⊢[PRAAx] hit d z T r p := by
  have near := nearest_spec d z T p hT
  exact hit_intro d z T r p (nearest d z T p) (.andE₁ near)
    (le_congr (Prf.andE₂ near).eqSymm (.eqRefl _) h)

theorem directed_bound (d : PR 3) (S T r p : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (length (Syn.shift S)) ⟶
      le (distanceTo d (entry (Syn.shift S) (var 0)) (Syn.shift T) (Syn.shift p)) (Syn.shift r))) :
    Γ ⊢[PRAAx] le (directed d S T p) r := by
  apply maximum_bound
  refine .allI (.impI ?_)
  have point := Prf.impE h.allOpen.wk Prf.hyp0
  have eq := directedBody_at (Γ := lt (var 0) (length (Syn.shift S)) :: Γ.map Fm.shift)
    d (Syn.shift S) (Syn.shift T) (Syn.shift p) (var 0)
  simpa only [Syn.shift, subst_pointData, SequenceComposition.subst_length] using le_congr eq.eqSymm (.eqRefl _) point

theorem directed_of_cover (d : PR 3) {S T r p : PTm n} (h : Γ ⊢[PRAAx] cover d S T r p) :
    Γ ⊢[PRAAx] le (directed d S T p) r := by
  apply directed_bound
  refine .allI (.impI ?_)
  have hc : Γ.map Fm.shift ⊢[PRAAx]
      cover d (Syn.shift S) (Syn.shift T) (Syn.shift r) (Syn.shift p) := by
    simpa only [Fm.shift, subst_cover, Syn.shift] using h.shift
  exact minimum_of_hit d (cover_at d hc.wk Prf.hyp0)

theorem cover_of_directed (d : PR 3) {S T r p : PTm n}
    (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] le (directed d S T p) r) : Γ ⊢[PRAAx] cover d S T r p := by
  refine .allI (.impI ?_)
  have target : Γ.map Fm.shift ⊢[PRAAx] le one (length (Syn.shift T)) := by
    simpa only [Fm.shift, subst_le, SequenceComposition.subst_length, Syn.shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] using hT.shift
  have bound : Γ.map Fm.shift ⊢[PRAAx]
      le (directed d (Syn.shift S) (Syn.shift T) (Syn.shift p)) (Syn.shift r) := by
    simpa only [Fm.shift, subst_le, subst_directed, Syn.shift] using h.shift
  simpa [hit, Syn.shift] using hit_of_minimum d target.wk
    (le_trans (distanceTo_le_directed d _ _ _ (var 0) Prf.hyp0) bound.wk)

def close (d : PR 3) (S T r p : PTm n) : Fm PTm n :=
  cover d S T r p ⋏ cover d T S r p

def closeSyntax (d : PR 3) : BoundedSyntax.BFm 4 :=
  .and (coverSyntax d) ((coverSyntax d).subst ![var 1, var 0, var 2, var 3])

def closeF (d : PR 3) : PR 4 := BoundedSyntax.bitF (closeSyntax d)

theorem closeSyntax_at (d : PR 3) (S T r p : PTm n) :
    (BoundedSyntax.formula (closeSyntax d)).subst ![S, T, r, p] = close d S T r p := by
  simp only [closeSyntax, BoundedSyntax.formula, Fm.subst_and, BoundedSyntax.formula_subst,
    Fm.subst_subst]
  have swap : (fun i => Syn.subst (![S, T, r, p] : Fin 4 → PTm n)
      ((![var 1, var 0, var 2, var 3] : Fin 4 → PTm 4) i)) = ![T, S, r, p] := by
    funext i
    fin_cases i <;> rfl
  rw [swap, coverSyntax_at, coverSyntax_at]
  rfl

theorem close_reflection (d : PR 3) (S T r p : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (FiniteQueryDemand.apply4 (closeF d) S T r p ≐ one) (close d S T r p) := by
  have prog := BoundedSyntax.program_correct (Γ := Γ) (closeSyntax d) ![S, T, r, p]
  have reflect := BoundedSyntax.bounded_reflection (Γ := Γ) (closeSyntax d) ![S, T, r, p]
  rw [closeSyntax_at] at reflect
  exact (Prf.iffI (.impI (prog.eqSymm.wk.eqTrans Prf.hyp0))
    (.impI (prog.wk.eqTrans Prf.hyp0))).iffTrans reflect

theorem close_of_bound (d : PR 3) {S T r p : PTm n}
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] le (hausdorff d S T p) r) : Γ ⊢[PRAAx] close d S T r p :=
  .andI (cover_of_directed d hT (le_trans (maximum_left _ _) h))
    (cover_of_directed d hS (le_trans (maximum_right _ _) h))

theorem bound_of_close (d : PR 3) {S T r p : PTm n} (h : Γ ⊢[PRAAx] close d S T r p) :
    Γ ⊢[PRAAx] le (hausdorff d S T p) r :=
  maximum_le (directed_of_cover d (.andE₁ h)) (directed_of_cover d (.andE₂ h))

/-- Actual finite numerical scan equals the two-sided bounded cover condition. -/
theorem finite_hausdorff_checker (d : PR 3) (S T r p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] Fm.iff (FiniteQueryDemand.apply4 (closeF d) S T r p ≐ one)
      (le (hausdorff d S T p) r) :=
  (close_reflection d S T r p).iffTrans
    (.iffI (.impI (bound_of_close d Prf.hyp0))
      (.impI (close_of_bound d hS.wk hT.wk Prf.hyp0)))

alias sum_mono := Common.add_le_add

def triangleLaw (d : PR 3) (p : PTm n) : Fm PTm n :=
  .all (.all (.all (le (distance d (var 2) (var 0) (Syn.shift (Syn.shift (Syn.shift p))))
    (distance d (var 2) (var 1) (Syn.shift (Syn.shift (Syn.shift p))) +
      distance d (var 1) (var 0) (Syn.shift (Syn.shift (Syn.shift p)))))))

@[simp] theorem subst_triangleLaw {m : ℕ} (σ : Fin n → PTm m) (d : PR 3) (p : PTm n) :
    (triangleLaw d p).subst σ = triangleLaw d (Syn.subst σ p) := by
  simp [triangleLaw, Syn.up, Syn.subst_shift, ← Syn.shift_subst]

theorem triangle_at (d : PR 3) {p : PTm n} (h : Γ ⊢[PRAAx] triangleLaw d p) (x y z : PTm n) :
    Γ ⊢[PRAAx] le (distance d x z p) (distance d x y p + distance d y z p) := by
  simpa [triangleLaw, Syn.up, Syn.subst_shift, Syn.subst_subst] using
    Prf.allE z (Prf.allE y (Prf.allE x h))

/-- The composite nearest-neighbor route yields a concrete two-edge cover. -/
theorem directed_triangle (d : PR 3) (S T U p : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hU : Γ ⊢[PRAAx] le one (length U))
    (ht : Γ ⊢[PRAAx] triangleLaw d p) :
    Γ ⊢[PRAAx] le (directed d S U p) (directed d S T p + directed d T U p) := by
  apply directed_bound
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift S)) :: Γ.map Fm.shift
  let x := entry (Syn.shift S) (var 0)
  let j := nearest d x (Syn.shift T) (Syn.shift p)
  let y := entry (Syn.shift T) j
  let k := nearest d y (Syn.shift U) (Syn.shift p)
  have hpT : Δ ⊢[PRAAx] le one (length (Syn.shift T)) := by
    simpa only [Fm.shift, subst_le, SequenceComposition.subst_length, Syn.shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] using hT.shift.wk
  have hpU : Δ ⊢[PRAAx] le one (length (Syn.shift U)) := by
    simpa only [Fm.shift, subst_le, SequenceComposition.subst_length, Syn.shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] using hU.shift.wk
  have tri : Δ ⊢[PRAAx] triangleLaw d (Syn.shift p) := by
    simpa only [Fm.shift, subst_triangleLaw, Syn.shift] using ht.shift.wk
  have rangeJ : Δ ⊢[PRAAx] lt j (length (Syn.shift T)) := .andE₁ (nearest_spec d _ _ _ hpT)
  have rangeK : Δ ⊢[PRAAx] lt k (length (Syn.shift U)) := .andE₁ (nearest_spec d _ _ _ hpU)
  have e1 := nearest_error d (Syn.shift S) (Syn.shift T) (Syn.shift p) (var 0) hpT
    (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift S)))
  have e2 := nearest_error d (Syn.shift T) (Syn.shift U) (Syn.shift p) j hpU rangeJ
  have point : Δ ⊢[PRAAx]
      le (distanceTo d x (Syn.shift U) (Syn.shift p))
        (directed d (Syn.shift S) (Syn.shift T) (Syn.shift p) +
          directed d (Syn.shift T) (Syn.shift U) (Syn.shift p)) :=
    le_trans (distanceTo_le d x (Syn.shift U) (Syn.shift p) k rangeK)
      (le_trans (triangle_at d tri x y (entry (Syn.shift U) k)) (sum_mono e1 e2))
  simpa only [Δ, x, Syn.shift, PTm.subst_add, subst_directed] using point

theorem hausdorff_triangle (d : PR 3) (S T U p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hU : Γ ⊢[PRAAx] le one (length U)) (ht : Γ ⊢[PRAAx] triangleLaw d p) :
    Γ ⊢[PRAAx] le (hausdorff d S U p) (hausdorff d S T p + hausdorff d T U p) := by
  apply maximum_le
  · exact le_trans (directed_triangle d S T U p hT hU ht)
      (sum_mono (maximum_left _ _) (maximum_left _ _))
  · have reverse := directed_triangle d U T S p hT hS ht
    exact le_trans reverse (le_congr (.eqRefl _) (add_comm _ _)
      (sum_mono (maximum_right _ _) (maximum_right _ _)))

theorem hausdorff_symm (d : PR 3) (S T p : PTm n) :
    Γ ⊢[PRAAx] hausdorff d S T p ≐ hausdorff d T S p :=
  le_antisymm (maximum_le (maximum_right _ _) (maximum_left _ _))
    (maximum_le (maximum_right _ _) (maximum_left _ _))

theorem checker_closed (d : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
        Fm.iff (FiniteQueryDemand.apply4 (closeF d) (var 0) (var 1) (var 2) (var 3) ≐ one)
          (le (hausdorff d (var 0) (var 1) (var 3)) (var 2))) :=
  closeUniv 4 (.impI (.impI (finite_hausdorff_checker d _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem triangle_closed (d : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (length (var 2)) ⟶
        triangleLaw d (var 3) ⟶
          le (hausdorff d (var 0) (var 2) (var 3))
            (hausdorff d (var 0) (var 1) (var 3) + hausdorff d (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (hausdorff_triangle d _ _ _ _
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

#print axioms nearest_spec
#print axioms maximum_bound
#print axioms nearest_error
#print axioms cover_reflection
#print axioms directed_of_cover
#print axioms finite_hausdorff_checker
#print axioms hausdorff_triangle
#print axioms checker_closed
#print axioms triangle_closed

end LeanProofs.IPRA.Foundations.FiniteHausdorff
