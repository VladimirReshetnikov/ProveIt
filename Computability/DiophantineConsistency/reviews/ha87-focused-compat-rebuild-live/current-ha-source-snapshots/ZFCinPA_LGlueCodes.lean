import ZFCinPA.LDriver
import ZFCinPA.ModelCodedSpecialization
import ZFCinPA.ModelCodedBindFree

set_option autoImplicit false
noncomputable section

/-!
# Code identities for the `relativize` glue

The glue between the driver (`envForm`) and Foundation's `relativize` runs by
induction over formulas through `free`, as the Tait rule for `∀` does. Under
`free`, a bound variable becomes the free variable `&0` and every free
variable is shifted up by one. `envForm` reads bound `#k` from environment slot
`k` and free `&i` from slot `d + i` at depth `d`, so freeing a level-`(n+1)`
formula at depth `n` reads exactly the same slots as the original at depth
`n + 1`:

`envForm n (subst (openVec n) (shift p)) = envForm (n + 1) p`
(`envForm_open`), with `openVec n = #0, …, #(n-1), &0`. At `n = 0` this is
`envForm 0 (free p) = envForm 1 p` (`envForm_free`).
-/

namespace LeanProofs.ZFCinPA.LGlueCodes

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.ModelCodedSpecialization
open LeanProofs.ZFCinPA.ModelCodedBindFree
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The opening vector `#0, …, #(n-1), &0`. -/
def openVec (n : V) : V := qVecIter ℒₛₑₜ n (^&0 ∷ 0)

instance openVec_definable : 𝚺₁-Function₁ (openVec : V → V) := by
  unfold openVec
  definability

lemma openVec_bvar {n i : V} (hi : i < n) : (openVec n).[i] = ^#i :=
  (qVecIter_free_spec (L := ℒₛₑₜ) n 0).1 i hi

lemma openVec_last (n : V) : (openVec n).[n] = ^&0 :=
  (qVecIter_free_spec (L := ℒₛₑₜ) n 0).2

lemma openVec_isSemitermVec (n : V) : IsSemitermVec ℒₛₑₜ (n + 1) n (openVec n) := by
  have h := qVecIter_isSemitermVec (L := ℒₛₑₜ)
    (show IsSemitermVec (V := V) ℒₛₑₜ 1 0 (^&0 ∷ 0) by simp) n
  simpa [openVec, add_comm] using h

lemma openVec_succ (n : V) : qVec ℒₛₑₜ (openVec n) = openVec (n + 1) := by
  simp [openVec]

/-- Terms of `ℒₛₑₜ` are variables. -/
lemma semiterm_cases {n t : V} (ht : IsSemiterm ℒₛₑₜ n t) :
    (∃ z < n, t = ^#z) ∨ ∃ x, t = ^&x := by
  rcases IsSemiterm.case_iff.mp ht with h | h | ⟨k, f, _, hf, -, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hf (SetRelativization.set_not_isFunc k f)

lemma idx_open {n t : V} (ht : IsSemiterm ℒₛₑₜ (n + 1) t) :
    idx n (termSubst ℒₛₑₜ (openVec n) (termShift ℒₛₑₜ t)) = idx (n + 1) t := by
  rcases semiterm_cases ht with ⟨z, hz, rfl⟩ | ⟨x, rfl⟩
  · rw [termShift_bvar, termSubst_bvar, idx_bvar]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hz) with hz' | rfl
    · rw [openVec_bvar hz', idx_bvar]
    · rw [openVec_last, idx_fvar]
      simp
  · rw [termShift_fvar, termSubst_fvar, idx_fvar, idx_fvar, ← add_assoc, add_right_comm]

/-- **`envForm` commutes with freeing at every depth.** -/
theorem envForm_open {m p : V} (hp : IsSemiformula ℒₛₑₜ m p) :
    m ≠ 0 → envForm (m - 1) (subst ℒₛₑₜ (openVec (m - 1)) (shift ℒₛₑₜ p)) = envForm m p := by
  refine IsSemiformula.sigma1_structural_induction (L := ℒₛₑₜ)
    (P := fun m p ↦ m ≠ 0 →
      envForm (m - 1) (subst ℒₛₑₜ (openVec (m - 1)) (shift ℒₛₑₜ p)) = envForm m p)
    (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro m k R v hR hv hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    obtain ⟨rfl, -⟩ := LDriver.isRel_set hR
    have hsv : IsSemitermVec ℒₛₑₜ 2 n (termSubstVec ℒₛₑₜ 2 (openVec n) (termShiftVec ℒₛₑₜ 2 v)) :=
      IsSemitermVec.termSubstVec (openVec_isSemitermVec n) hv.termShiftVec
    simp only [add_tsub_cancel_right]
    rw [shift_rel hR hv.isUTerm, substs_rel hR hv.isUTerm.termShiftVec,
      envForm_rel hR hsv.isUTerm, envForm_rel hR hv.isUTerm, atomOf, atomOf,
      nth_termSubstVec hv.isUTerm.termShiftVec (by simp),
      nth_termSubstVec hv.isUTerm.termShiftVec (by simp),
      nth_termShiftVec hv.isUTerm (by simp), nth_termShiftVec hv.isUTerm (by simp),
      idx_open (hv.nth (by simp)), idx_open (hv.nth (by simp))]
  · intro m k R v hR hv hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    obtain ⟨rfl, -⟩ := LDriver.isRel_set hR
    have hsv : IsSemitermVec ℒₛₑₜ 2 n (termSubstVec ℒₛₑₜ 2 (openVec n) (termShiftVec ℒₛₑₜ 2 v)) :=
      IsSemitermVec.termSubstVec (openVec_isSemitermVec n) hv.termShiftVec
    simp only [add_tsub_cancel_right]
    rw [shift_nrel hR hv.isUTerm, substs_nrel hR hv.isUTerm.termShiftVec,
      envForm_nrel hR hsv.isUTerm, envForm_nrel hR hv.isUTerm, atomOf, atomOf,
      nth_termSubstVec hv.isUTerm.termShiftVec (by simp),
      nth_termSubstVec hv.isUTerm.termShiftVec (by simp),
      nth_termShiftVec hv.isUTerm (by simp), nth_termShiftVec hv.isUTerm (by simp),
      idx_open (hv.nth (by simp)), idx_open (hv.nth (by simp))]
  · intro m _
    simp
  · intro m _
    simp
  · intro m p q hp hq ihp ihq hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    have ihp' := ihp hm
    have ihq' := ihq hm
    simp only [add_tsub_cancel_right] at ihp' ihq' ⊢
    rw [shift_and hp.isUFormula hq.isUFormula,
      substs_and hp.isUFormula.shift hq.isUFormula.shift,
      envForm_and (hp.shift.subst (openVec_isSemitermVec n)).isUFormula
        (hq.shift.subst (openVec_isSemitermVec n)).isUFormula,
      envForm_and hp.isUFormula hq.isUFormula, ihp', ihq']
  · intro m p q hp hq ihp ihq hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    have ihp' := ihp hm
    have ihq' := ihq hm
    simp only [add_tsub_cancel_right] at ihp' ihq' ⊢
    rw [shift_or hp.isUFormula hq.isUFormula,
      substs_or hp.isUFormula.shift hq.isUFormula.shift,
      envForm_or (hp.shift.subst (openVec_isSemitermVec n)).isUFormula
        (hq.shift.subst (openVec_isSemitermVec n)).isUFormula,
      envForm_or hp.isUFormula hq.isUFormula, ihp', ihq']
  · intro m p hp ih hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    have ih' := ih (by simp)
    simp only [add_tsub_cancel_right] at ih' ⊢
    rw [shift_all hp.isUFormula, substs_all hp.isUFormula.shift, openVec_succ,
      envForm_all (hp.shift.subst (openVec_isSemitermVec (n + 1))).isUFormula, ih',
      envForm_all hp.isUFormula]
  · intro m p hp ih hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    have ih' := ih (by simp)
    simp only [add_tsub_cancel_right] at ih' ⊢
    rw [shift_exs hp.isUFormula, substs_ex hp.isUFormula.shift, openVec_succ,
      envForm_exs (hp.shift.subst (openVec_isSemitermVec (n + 1))).isUFormula, ih',
      envForm_exs hp.isUFormula]

/-- At depth zero: `envForm 0 (free p) = envForm 1 p`. -/
theorem envForm_free {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    envForm 0 (free ℒₛₑₜ p) = envForm 1 p := by
  have h := envForm_open hp _root_.one_ne_zero
  simpa [free, substs1, openVec] using h

/-! ## The free-variable bound -/

lemma bind_open {n t : V} (ht : IsSemiterm ℒₛₑₜ (n + 1) t) :
    termBindFreeAt ℒₛₑₜ n (termSubst ℒₛₑₜ (openVec n) (termShift ℒₛₑₜ t)) =
      termBindFreeAt ℒₛₑₜ (n + 1) t := by
  rcases semiterm_cases ht with ⟨z, hz, rfl⟩ | ⟨x, rfl⟩
  · rw [termShift_bvar, termSubst_bvar, termBindFreeAt_bvar]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hz) with hz' | rfl
    · rw [openVec_bvar hz', termBindFreeAt_bvar]
    · rw [openVec_last, termBindFreeAt_fvar]
      simp
  · rw [termShift_fvar, termSubst_fvar, termBindFreeAt_fvar, termBindFreeAt_fvar, ← add_assoc,
      add_right_comm]

lemma bindVec_open {n v : V} (hv : IsSemitermVec ℒₛₑₜ 2 (n + 1) v) :
    termBindFreeVecAt ℒₛₑₜ n 2 (termSubstVec ℒₛₑₜ 2 (openVec n) (termShiftVec ℒₛₑₜ 2 v)) =
      termBindFreeVecAt ℒₛₑₜ (n + 1) 2 v := by
  have hsv : IsUTermVec ℒₛₑₜ 2 (termSubstVec ℒₛₑₜ 2 (openVec n) (termShiftVec ℒₛₑₜ 2 v)) :=
    (IsSemitermVec.termSubstVec (openVec_isSemitermVec n) hv.termShiftVec).isUTerm
  apply nth_ext' (2 : V) (termBindFreeVecAt_lh _ hsv) (termBindFreeVecAt_lh _ hv.isUTerm)
  intro i hi
  rw [nth_termBindFreeVecAt _ hsv hi, nth_termBindFreeVecAt _ hv.isUTerm hi,
    nth_termSubstVec hv.isUTerm.termShiftVec hi, nth_termShiftVec hv.isUTerm hi,
    bind_open (hv.nth hi)]

/-- **`bindFreeAt` commutes with freeing at every depth.** -/
theorem bindFreeAt_open {m p : V} (hp : IsSemiformula ℒₛₑₜ m p) :
    m ≠ 0 → bindFreeAt ℒₛₑₜ (m - 1) (subst ℒₛₑₜ (openVec (m - 1)) (shift ℒₛₑₜ p)) =
      bindFreeAt ℒₛₑₜ m p := by
  refine IsSemiformula.sigma1_structural_induction (L := ℒₛₑₜ)
    (P := fun m p ↦ m ≠ 0 → bindFreeAt ℒₛₑₜ (m - 1)
      (subst ℒₛₑₜ (openVec (m - 1)) (shift ℒₛₑₜ p)) = bindFreeAt ℒₛₑₜ m p)
    (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro m k R v hR hv hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    obtain ⟨rfl, -⟩ := LDriver.isRel_set hR
    have hsv : IsSemitermVec ℒₛₑₜ 2 n (termSubstVec ℒₛₑₜ 2 (openVec n) (termShiftVec ℒₛₑₜ 2 v)) :=
      IsSemitermVec.termSubstVec (openVec_isSemitermVec n) hv.termShiftVec
    simp only [add_tsub_cancel_right]
    rw [shift_rel hR hv.isUTerm, substs_rel hR hv.isUTerm.termShiftVec,
      bindFreeAt_rel _ hR hsv.isUTerm, bindFreeAt_rel _ hR hv.isUTerm, bindVec_open hv]
  · intro m k R v hR hv hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    obtain ⟨rfl, -⟩ := LDriver.isRel_set hR
    have hsv : IsSemitermVec ℒₛₑₜ 2 n (termSubstVec ℒₛₑₜ 2 (openVec n) (termShiftVec ℒₛₑₜ 2 v)) :=
      IsSemitermVec.termSubstVec (openVec_isSemitermVec n) hv.termShiftVec
    simp only [add_tsub_cancel_right]
    rw [shift_nrel hR hv.isUTerm, substs_nrel hR hv.isUTerm.termShiftVec,
      bindFreeAt_nrel _ hR hsv.isUTerm, bindFreeAt_nrel _ hR hv.isUTerm, bindVec_open hv]
  · intro m _
    simp
  · intro m _
    simp
  · intro m p q hp hq ihp ihq hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    have ihp' := ihp hm
    have ihq' := ihq hm
    simp only [add_tsub_cancel_right] at ihp' ihq' ⊢
    rw [shift_and hp.isUFormula hq.isUFormula,
      substs_and hp.isUFormula.shift hq.isUFormula.shift,
      bindFreeAt_and _ (hp.shift.subst (openVec_isSemitermVec n)).isUFormula
        (hq.shift.subst (openVec_isSemitermVec n)).isUFormula,
      bindFreeAt_and _ hp.isUFormula hq.isUFormula, ihp', ihq']
  · intro m p q hp hq ihp ihq hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    have ihp' := ihp hm
    have ihq' := ihq hm
    simp only [add_tsub_cancel_right] at ihp' ihq' ⊢
    rw [shift_or hp.isUFormula hq.isUFormula,
      substs_or hp.isUFormula.shift hq.isUFormula.shift,
      bindFreeAt_or _ (hp.shift.subst (openVec_isSemitermVec n)).isUFormula
        (hq.shift.subst (openVec_isSemitermVec n)).isUFormula,
      bindFreeAt_or _ hp.isUFormula hq.isUFormula, ihp', ihq']
  · intro m p hp ih hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    have ih' := ih (by simp)
    simp only [add_tsub_cancel_right] at ih' ⊢
    rw [shift_all hp.isUFormula, substs_all hp.isUFormula.shift, openVec_succ,
      bindFreeAt_all _ (hp.shift.subst (openVec_isSemitermVec (n + 1))).isUFormula, ih',
      bindFreeAt_all _ hp.isUFormula]
  · intro m p hp ih hm
    rcases zero_or_succ m with rfl | ⟨n, rfl⟩
    · exact absurd rfl hm
    have ih' := ih (by simp)
    simp only [add_tsub_cancel_right] at ih' ⊢
    rw [shift_exs hp.isUFormula, substs_ex hp.isUFormula.shift, openVec_succ,
      bindFreeAt_exs _ (hp.shift.subst (openVec_isSemitermVec (n + 1))).isUFormula, ih',
      bindFreeAt_exs _ hp.isUFormula]

/-- All free variables of the formula `q` are below `j`. -/
def FvLt (j q : V) : Prop := IsSemiformula ℒₛₑₜ j (bindFreeAt ℒₛₑₜ 0 q)

lemma fvLt_free {j p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (h : FvLt j (^∀ p)) :
    FvLt (j + 1) (free ℒₛₑₜ p) := by
  have h1 := bindFreeAt_open hp _root_.one_ne_zero
  simp only [show (1 : V) - 1 = 0 by simp] at h1
  have h2 : FvLt (j + 1) (free ℒₛₑₜ p) ↔ IsSemiformula ℒₛₑₜ (j + 1) (bindFreeAt ℒₛₑₜ 1 p) := by
    unfold FvLt
    rw [← h1]
    simp [free, substs1, openVec]
  rw [h2]
  unfold FvLt at h
  rw [bindFreeAt_all _ hp.isUFormula] at h
  simpa using h

lemma fvLt_free_ex {j p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (h : FvLt j (^∃ p)) :
    FvLt (j + 1) (free ℒₛₑₜ p) := by
  have h1 := bindFreeAt_open hp _root_.one_ne_zero
  simp only [show (1 : V) - 1 = 0 by simp] at h1
  have h2 : FvLt (j + 1) (free ℒₛₑₜ p) ↔ IsSemiformula ℒₛₑₜ (j + 1) (bindFreeAt ℒₛₑₜ 1 p) := by
    unfold FvLt
    rw [← h1]
    simp [free, substs1, openVec]
  rw [h2]
  unfold FvLt at h
  rw [bindFreeAt_exs _ hp.isUFormula] at h
  simpa using h

lemma fvLt_and {j p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q)
    (h : FvLt j (p ^⋏ q)) : FvLt j p ∧ FvLt j q := by
  unfold FvLt at h ⊢
  rw [bindFreeAt_and _ hp hq] at h
  simpa using h

lemma fvLt_or {j p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q)
    (h : FvLt j (p ^⋎ q)) : FvLt j p ∧ FvLt j q := by
  unfold FvLt at h ⊢
  rw [bindFreeAt_or _ hp hq] at h
  simpa using h

/-- At an atom of a formula, every argument is a free variable below the bound. -/
lemma fvLt_atom {j R v : V} (hR : (ℒₛₑₜ).IsRel 2 R) (hv : IsSemitermVec ℒₛₑₜ 2 0 v)
    (h : FvLt j (^rel 2 R v)) {i : V} (hi : i < 2) : ∃ a < j, v.[i] = ^&a := by
  unfold FvLt at h
  rw [bindFreeAt_rel _ hR hv.isUTerm] at h
  have h' := ((IsSemiformula.rel.mp h).2).nth hi
  rw [nth_termBindFreeVecAt _ hv.isUTerm hi] at h'
  rcases semiterm_cases (hv.nth hi) with ⟨z, hz, -⟩ | ⟨x, hx⟩
  · simp at hz
  · rw [hx, termBindFreeAt_fvar] at h'
    exact ⟨x, by simpa using h', hx⟩

end LeanProofs.ZFCinPA.LGlueCodes
