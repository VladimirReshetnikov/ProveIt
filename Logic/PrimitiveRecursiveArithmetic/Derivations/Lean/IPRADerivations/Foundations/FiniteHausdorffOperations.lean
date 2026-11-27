import IPRADerivations.Foundations.FiniteHausdorff

/-!
# Images and distance observations of actual finite aggregates

Finite-demand `lem:aggregate-calculus`. All lists, lengths, error numerators,
Lipschitz constants and persistent data are internal. These proofs concern the
actual nearest/minimum/Hausdorff scans, not supplied set-distance estimates.
The metric-law premises are local mathematical interface laws, while image
lists are constructed by an actual PR map. Distances use a common rational
scale as in `FiniteHausdorff`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.FiniteHausdorffOperations

open_ipra exports
open LeanProofs.IPRA.Foundations.FiniteHausdorff
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.DemandClosure (maximum maximum_left maximum_right maximum_le)
open LeanProofs.IPRA.Probability.Variance (ad)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mapBody (f : PR 2) : PTm 2 := ap2 f (entry (fstT (var 1)) (var 0)) (sndT (var 1))

def mapList (f : PR 2) (S p : PTm n) : PTm n :=
  sequence (mapBody f) (length S) (pairT S p)

@[simp] theorem subst_mapList {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (S p : PTm n) :
    Syn.subst σ (mapList f S p) = mapList f (Syn.subst σ S) (Syn.subst σ p) := by
  simp only [mapList, MasterCertificate.subst_sequence, SequenceComposition.subst_length, subst_pairT]

theorem map_length (f : PR 2) (S p : PTm n) :
    Γ ⊢[PRAAx] length (mapList f S p) ≐ length S := sequence_length _ _ _

theorem mapBody_at (f : PR 2) (S p i : PTm n) :
    Γ ⊢[PRAAx] inst2 (mapBody f) i (pairT S p) ≐ ap2 f (entry S i) p := by
  simp only [mapBody, inst2, subst_ap2, MasterCertificate.subst_entry, subst_fstT,
    subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact congrAp2 f (SequenceComposition.entry_congr (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

theorem map_lookup (f : PR 2) (S p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] entry (mapList f S p) i ≐ ap2 f (entry S i) p :=
  (sequence_decode (mapBody f) hi).eqTrans (mapBody_at f S p i)

def imageLaw (d e : PR 3) (f : PR 2) (L p : PTm n) : Fm PTm n :=
  .all (.all (le
    (distance e (ap2 f (var 1) (Syn.shift (Syn.shift p)))
      (ap2 f (var 0) (Syn.shift (Syn.shift p))) (Syn.shift (Syn.shift p)))
    (Syn.shift (Syn.shift L) * distance d (var 1) (var 0) (Syn.shift (Syn.shift p)))))

@[simp] theorem subst_imageLaw {m : ℕ} (σ : Fin n → PTm m) (d e : PR 3)
    (f : PR 2) (L p : PTm n) :
    (imageLaw d e f L p).subst σ = imageLaw d e f (Syn.subst σ L) (Syn.subst σ p) := by
  simp [imageLaw, Syn.up, Syn.subst_shift, ← Syn.shift_subst]

theorem imageLaw_at (d e : PR 3) (f : PR 2) {L p : PTm n}
    (h : Γ ⊢[PRAAx] imageLaw d e f L p) (x y : PTm n) :
    Γ ⊢[PRAAx] le (distance e (ap2 f x p) (ap2 f y p) p) (L * distance d x y p) := by
  simpa [imageLaw, Syn.up, Syn.subst_shift, Syn.subst_subst] using Prf.allE y (Prf.allE x h)

private theorem mul_mono_left (L : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (L * a) (L * b) :=
  mul_le_mul_left L h

/-- Directed image distance is bounded using the actual source nearest index. -/
theorem directed_image (d e : PR 3) (f : PR 2) (S T L p : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hf : Γ ⊢[PRAAx] imageLaw d e f L p) :
    Γ ⊢[PRAAx] le (directed e (mapList f S p) (mapList f T p) p) (L * directed d S T p) := by
  apply directed_bound
  refine .allI (.impI ?_)
  let Δ : List (Fm PTm (n + 1)) :=
    lt (var 0) (length (Syn.shift (mapList f S p))) :: Γ.map Fm.shift
  have sourceLength : Δ ⊢[PRAAx]
      length (Syn.shift (mapList f S p)) ≐ length (Syn.shift S) := by
    simpa only [Fm.shift, Fm.subst_eq, SequenceComposition.subst_length, Syn.shift] using
      (map_length (Γ := Γ) f S p).shift.wk
  have rangeI : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift S)) :=
    lt_congr (.eqRefl _) sourceLength Prf.hyp0
  have nonemptyT : Δ ⊢[PRAAx] le one (length (Syn.shift T)) := by
    simpa only [Fm.shift, subst_le, SequenceComposition.subst_length, Syn.shift,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using hT.shift.wk
  have law : Δ ⊢[PRAAx] imageLaw d e f (Syn.shift L) (Syn.shift p) := by
    simpa only [Fm.shift, subst_imageLaw, Syn.shift] using hf.shift.wk
  let x := entry (Syn.shift S) (var 0)
  let j := nearest d x (Syn.shift T) (Syn.shift p)
  have rangeJ : Δ ⊢[PRAAx] lt j (length (Syn.shift T)) := .andE₁ (nearest_spec d _ _ _ nonemptyT)
  have rangeMapJ : Δ ⊢[PRAAx] lt j (length (mapList f (Syn.shift T) (Syn.shift p))) :=
    lt_congr (.eqRefl _) (map_length f _ _).eqSymm rangeJ
  have sourceEntry := map_lookup f (Syn.shift S) (Syn.shift p) (var 0) rangeI
  have targetEntry := map_lookup f (Syn.shift T) (Syn.shift p) j rangeJ
  have lipschitz := imageLaw_at d e f law x (entry (Syn.shift T) j)
  have bounded : Δ ⊢[PRAAx]
      le (distance e (entry (mapList f (Syn.shift S) (Syn.shift p)) (var 0))
        (entry (mapList f (Syn.shift T) (Syn.shift p)) j) (Syn.shift p))
        (Syn.shift L * directed d (Syn.shift S) (Syn.shift T) (Syn.shift p)) :=
    le_congr (congrAp3 e sourceEntry targetEntry (.eqRefl _)).eqSymm (.eqRefl _)
      (le_trans lipschitz (mul_mono_left _ (nearest_error d _ _ _ _ nonemptyT rangeI)))
  have point := le_trans (distanceTo_le e _ _ _ j rangeMapJ) bounded
  simpa only [Δ, Syn.shift, subst_mapList, PTm.subst_mul, subst_directed] using point

theorem hausdorff_image (d e : PR 3) (f : PR 2) (S T L p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hf : Γ ⊢[PRAAx] imageLaw d e f L p) :
    Γ ⊢[PRAAx] le (hausdorff e (mapList f S p) (mapList f T p) p) (L * hausdorff d S T p) :=
  maximum_le (le_trans (directed_image d e f S T L p hT hf) (mul_mono_left _ (maximum_left _ _)))
    (le_trans (directed_image d e f T S L p hS hf) (mul_mono_left _ (maximum_right _ _)))

def symmetryLaw (d : PR 3) (p : PTm n) : Fm PTm n :=
  .all (.all (distance d (var 1) (var 0) (Syn.shift (Syn.shift p)) ≐
    distance d (var 0) (var 1) (Syn.shift (Syn.shift p))))

theorem symmetry_at (d : PR 3) {p : PTm n} (h : Γ ⊢[PRAAx] symmetryLaw d p) (x y : PTm n) :
    Γ ⊢[PRAAx] distance d x y p ≐ distance d y x p := by
  simpa [symmetryLaw, Syn.up, Syn.subst_shift, Syn.subst_subst] using Prf.allE y (Prf.allE x h)

/-- The two actual nearest-neighbor choices prove the one-sided variation bound. -/
theorem distanceTo_upper (d : PR 3) (z w S T p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (ht : Γ ⊢[PRAAx] triangleLaw d p) :
    Γ ⊢[PRAAx] le (distanceTo d z S p)
      (distanceTo d w T p + (distance d z w p + hausdorff d S T p)) := by
  let j := nearest d w T p
  let y := entry T j
  let i := nearest d y S p
  have jRange : Γ ⊢[PRAAx] lt j (length T) := .andE₁ (nearest_spec d w T p hT)
  have iRange : Γ ⊢[PRAAx] lt i (length S) := .andE₁ (nearest_spec d y S p hS)
  have last := nearest_error d T S p j hS jRange
  have first := Prf.andE₂ (nearest_spec (Γ := Γ) d w T p hT)
  have path := le_trans (triangle_at d ht z w (entry S i))
    (sum_mono (le_refl _) (triangle_at d ht w y (entry S i)))
  have middle : Γ ⊢[PRAAx]
      le (distance d z (entry S i) p)
        (distance d z w p + (distanceTo d w T p + hausdorff d S T p)) :=
    le_trans path (sum_mono (le_refl _) (sum_mono
      (le_congr (.eqRefl _) first (le_refl _)) (le_trans last (maximum_right _ _))))
  exact le_congr (.eqRefl _) (by ipra_ring)
    (le_trans (distanceTo_le d z S p i iRange) middle)

private theorem abs_bound {a b r : PTm n} (ha : Γ ⊢[PRAAx] le a (b + r))
    (hb : Γ ⊢[PRAAx] le b (a + r)) : Γ ⊢[PRAAx] le (ad a b) r := by
  refine .orE (le_total a b) ?_ ?_
  · have split := eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le a b))
    have bound : (le a b :: Γ) ⊢[PRAAx] le (monus b a) r :=
      le_of_add_le_add_right (le_congr (split.eqTrans (add_comm _ _)) (add_comm _ _) hb.wk)
    exact le_congr ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (zero_add _)).eqSymm (.eqRefl _) bound
  · have split := eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le b a))
    have bound : (le b a :: Γ) ⊢[PRAAx] le (monus a b) r :=
      le_of_add_le_add_right (le_congr (split.eqTrans (add_comm _ _)) (add_comm _ _) ha.wk)
    exact le_congr ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)).eqSymm (.eqRefl _) bound

theorem distanceTo_variation (d : PR 3) (z w S T p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (ht : Γ ⊢[PRAAx] triangleLaw d p) (hs : Γ ⊢[PRAAx] symmetryLaw d p) :
    Γ ⊢[PRAAx] le (ad (distanceTo d z S p) (distanceTo d w T p))
      (distance d z w p + hausdorff d S T p) := by
  apply abs_bound (distanceTo_upper d z w S T p hS hT ht)
  have reverse := distanceTo_upper d w z T S p hT hS ht
  exact le_congr (.eqRefl _) (congrAdd (.eqRefl _)
    (congrAdd (symmetry_at d hs w z) (hausdorff_symm d T S p))) reverse

theorem image_closed (d e : PR 3) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ imageLaw d e f (var 2) (var 3) ⟶
        le (hausdorff e (mapList f (var 0) (var 3)) (mapList f (var 1) (var 3)) (var 3))
          (var 2 * hausdorff d (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (hausdorff_image d e f _ _ _ _
    (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0))))

theorem distance_variation_closed (d : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (length (var 2)) ⟶ le one (length (var 3)) ⟶ triangleLaw d (var 4) ⟶
        symmetryLaw d (var 4) ⟶
          le (ad (distanceTo d (var 0) (var 2) (var 4)) (distanceTo d (var 1) (var 3) (var 4)))
            (distance d (var 0) (var 1) (var 4) + hausdorff d (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (distanceTo_variation d _ _ _ _ _
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

#print axioms map_lookup
#print axioms hausdorff_image
#print axioms distanceTo_variation
#print axioms image_closed
#print axioms distance_variation_closed

end LeanProofs.IPRA.Foundations.FiniteHausdorffOperations
