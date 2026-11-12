import ConciseIPRA.RoundTripScalar
import ConciseIPRA.NativeBiInterpretation

/-!
# Erasing the zero computation from term syntax

This is the module delivered in the package `Research/zero_normal`
(`formal/ZeroNormalization.lean`); it compiled unchanged.

`nf` contracts only `I(0,a;u.h) = a`, recursively under every binder.
It does not evaluate successor iterations. Its normal terms are exactly
those with no iterator whose counter is literally zero.

This module establishes normalization, idempotence, renaming and
substitution coherence, and provable equality to the original term in
`T_eq`. The body-congruence step in the last theorem uses the existing
equation-induction theorem `Q.iter_congr`; it is not justified by ordinary
free-variable congruence alone.

The module does not define or verify the new proof-certificate checker.
-/

namespace LeanProofs.ConciseIPRA.ZeroNormalization

open Syn
open Tm (zero succ iter)
open scoped Fm

variable {n m k : ℕ}

/-- A constructor that immediately erases a literal-zero counter. -/
def smartI (c a : Tm n) (h : Tm (n + 1)) : Tm n :=
  match c with
  | .zero => a
  | _ => iter c a h

/-- Bottom-up normalization for the zero computation alone. -/
def nf : {n : ℕ} → Tm n → Tm n
  | _, .var i => .var i
  | _, .zero => .zero
  | _, .succ t => .succ (nf t)
  | _, .iter c a h => smartI (nf c) (nf a) (nf h)

/-- The explicit canonical-input condition. -/
def Normal : {n : ℕ} → Tm n → Prop
  | _, .var _ => True
  | _, .zero => True
  | _, .succ t => Normal t
  | _, .iter c a h => c ≠ zero ∧ Normal c ∧ Normal a ∧ Normal h

@[simp] theorem smartI_zero (a : Tm n) (h : Tm (n + 1)) : smartI zero a h = a := rfl

theorem smartI_of_ne {c : Tm n} (hc : c ≠ zero) (a : Tm n) (h : Tm (n + 1)) :
    smartI c a h = iter c a h := by
  cases c <;> first | rfl | exact (hc rfl).elim

theorem normal_smartI {c a : Tm n} {h : Tm (n + 1)}
    (hc : Normal c) (ha : Normal a) (hh : Normal h) : Normal (smartI c a h) := by
  cases c with
  | zero => exact ha
  | var i => exact ⟨(by intro e; cases e), hc, ha, hh⟩
  | succ c => exact ⟨(by intro e; cases e), hc, ha, hh⟩
  | iter c b k => exact ⟨(by intro e; cases e), hc, ha, hh⟩

theorem nf_normal (t : Tm n) : Normal (nf t) := by
  induction t with
  | var i => trivial
  | zero => trivial
  | succ t ih => exact ih
  | iter c a h ihc iha ihh => exact normal_smartI ihc iha ihh

theorem nf_of_normal (t : Tm n) (ht : Normal t) : nf t = t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | succ t ih => exact congrArg succ (ih ht)
  | iter c a h ihc iha ihh =>
    rcases ht with ⟨hc, hcn, han, hhn⟩
    simp only [nf, ihc hcn, iha han, ihh hhn]
    exact smartI_of_ne hc a h

@[simp] theorem nf_idempotent (t : Tm n) : nf (nf t) = nf t :=
  nf_of_normal _ (nf_normal t)

theorem normal_iff_fixed (t : Tm n) : Normal t ↔ nf t = t := by
  constructor
  · exact nf_of_normal t
  · intro e
    rw [← e]
    exact nf_normal t

@[simp] theorem nf_smartI (c a : Tm n) (h : Tm (n + 1)) :
    nf (smartI c a h) = smartI (nf c) (nf a) (nf h) := by
  cases c <;> rfl

theorem ren_smartI (ξ : Fin n → Fin m) (c a : Tm n) (h : Tm (n + 1)) :
    Tm.ren ξ (smartI c a h) =
      smartI (Tm.ren ξ c) (Tm.ren ξ a) (Tm.ren (Tm.upRen ξ) h) := by
  cases c <;> rfl

/-- In particular, normalization does not introduce free variables. -/
theorem nf_ren (t : Tm n) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    nf (Tm.ren ξ t) = Tm.ren ξ (nf t) := by
  induction t with
  | var i => intro m ξ; rfl
  | zero => intro m ξ; rfl
  | succ t ih => intro m ξ; simp only [Tm.ren, nf, ih]
  | iter c a h ihc iha ihh =>
    intro m ξ
    simp only [Tm.ren, nf, ihc, iha, ihh, ren_smartI]

@[simp] theorem nf_shift (t : Tm n) : nf (Syn.shift t) = Syn.shift (nf t) := by
  simpa only [Tm.shift_eq_ren] using nf_ren t Fin.succ

theorem nf_upS (σ : Fin n → Tm m) :
    (fun i => nf (Tm.upS σ i)) = Tm.upS (fun i => nf (σ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Tm.upS_succ, nf_ren]

theorem nf_up (σ : Fin n → Tm m) :
    (fun i => nf (Syn.up σ i)) = Syn.up (fun i => nf (σ i)) := by
  simpa only [Tm.up_eq_upS] using nf_upS σ

/-- A substituted smart node agrees with rebuilding and normalizing its fields. -/
theorem nf_sub_smartI (σ : Fin n → Tm m) (c a : Tm n) (h : Tm (n + 1)) :
    nf (Tm.sub σ (smartI c a h)) =
      smartI (nf (Tm.sub σ c)) (nf (Tm.sub σ a)) (nf (Tm.sub (Tm.upS σ) h)) := by
  cases c <;> rfl

/-- Contracting zero redexes before substitution does not change the final normal form. -/
theorem nf_sub_nf (t : Tm n) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    nf (Tm.sub σ (nf t)) = nf (Tm.sub σ t) := by
  induction t with
  | var i => intro m σ; rfl
  | zero => intro m σ; rfl
  | succ t ih => intro m σ; simp only [nf, Tm.sub, ih]
  | iter c a h ihc iha ihh =>
    intro m σ
    simp only [nf, nf_sub_smartI, Tm.sub, ihc, iha, ihh]

/-- Normalizing the entries of a substitution does not change the final normal form. -/
theorem nf_sub_map (t : Tm n) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    nf (Tm.sub (fun i => nf (σ i)) t) = nf (Tm.sub σ t) := by
  induction t with
  | var i => intro m σ; exact nf_idempotent (σ i)
  | zero => intro m σ; rfl
  | succ t ih => intro m σ; simp only [Tm.sub, nf, ih]
  | iter c a h ihc iha ihh =>
    intro m σ
    have hh : nf (Tm.sub (Tm.upS (fun i => nf (σ i))) h) =
        nf (Tm.sub (Tm.upS σ) h) := by
      simpa only [nf_upS] using ihh (Tm.upS σ)
    simp only [Tm.sub, nf, ihc, iha, hh]

/-- The strict substitution law of the normalization translation. -/
theorem nf_subst (t : Tm n) (σ : Fin n → Tm m) :
    nf (Syn.subst (fun i => nf (σ i)) (nf t)) = nf (Syn.subst σ t) :=
  (nf_sub_nf t (fun i => nf (σ i))).trans (nf_sub_map t σ)

/-- Hereditary substitution in the normal syntax. -/
def hsub (σ : Fin n → Tm m) (t : Tm n) : Tm m := nf (Syn.subst σ t)

theorem hsub_comp (t : Tm n) (σ : Fin n → Tm m) (τ : Fin m → Tm k) :
    hsub τ (hsub σ t) = hsub (fun i => hsub τ (σ i)) t := by
  unfold hsub
  change nf (Tm.sub τ (nf (Tm.sub σ t))) =
    nf (Tm.sub (fun i => nf (Tm.sub τ (σ i))) t)
  rw [nf_sub_nf, Tm.sub_sub]
  exact (nf_sub_map t (fun i => Syn.subst τ (σ i))).symm

theorem hsub_id (t : Tm n) : hsub Syn.var t = nf t := by
  simp only [hsub, Syn.subst_id]

/-- One smart contraction is a theorem of the original scalar theory. -/
theorem smartI_correct (c a : Tm n) (h : Tm (n + 1)) :
    ([] : List (Fm Tm n)) ⊢[TeqAx] iter c a h ≐ smartI c a h := by
  cases c <;> dsimp [smartI]
  all_goals first | exact Teq.iterZero _ _ | exact Prf.eqRefl _

/-- Normalization preserves the numerical value, including reductions under binders. -/
theorem nf_correct (t : Tm n) : ([] : List (Fm Tm n)) ⊢[TeqAx] t ≐ nf t := by
  induction t with
  | var i => exact Prf.eqRefl _
  | zero => exact Prf.eqRefl _
  | succ t ih =>
    refine Q.exact ?_
    exact congrArg Q.succ (Q.sound ih)
  | iter c a h ihc iha ihh =>
    exact Prf.eqTrans (Q.iter_congr ihc iha ihh) (smartI_correct (nf c) (nf a) (nf h))

/-- Inclusion into the raw syntax respects substitution up to provable equality. -/
theorem inclusion_subst_coherent (t : Tm n) (σ : Fin n → Tm m) :
    ([] : List (Fm Tm m)) ⊢[TeqAx]
      Syn.subst σ (nf t) ≐ nf (Syn.subst σ t) := by
  have h := nf_correct (Syn.subst σ (nf t))
  rw [show nf (Syn.subst σ (nf t)) = nf (Syn.subst σ t) from nf_sub_nf t σ] at h
  exact h

/-- Normalize the numerical terms in a native formula, preserving both binders. -/
def fnf : {n : ℕ} → NFm n → NFm n
  | _, .eq s t => .eq (nf s) (nf t)
  | _, .Q B => .Q (fnf B)
  | _, .D B => .D (fnf B)

@[simp] theorem fnf_idempotent (A : NFm n) : fnf (fnf A) = fnf A := by
  induction A with
  | eq s t => simp only [fnf, nf_idempotent]
  | Q B ih => exact congrArg NFm.Q ih
  | D B ih => exact congrArg NFm.D ih

/-- The formula translation respects hereditary substitution under Q and D. -/
theorem fnf_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    fnf ((fnf A).subst (fun i => nf (σ i))) = fnf (A.subst σ) := by
  induction A with
  | eq s t =>
    intro m σ
    simp only [fnf, NFm.subst_eq, nf_subst]
  | Q B ih =>
    intro m σ
    have h : fnf ((fnf B).subst (Syn.up (fun i => nf (σ i)))) =
        fnf (B.subst (Syn.up σ)) := by
      simpa only [nf_up] using ih (Syn.up σ)
    exact congrArg NFm.Q h
  | D B ih =>
    intro m σ
    have h : fnf ((fnf B).subst (Syn.up (Syn.up (fun i => nf (σ i))))) =
        fnf (B.subst (Syn.up (Syn.up σ))) := by
      simpa only [nf_up] using ih (Syn.up (Syn.up σ))
    exact congrArg NFm.D h

/-- A closed equivalence of matrices gives an equivalence of conditional closures. -/
theorem closure_iff {A B : Fm Tm (n + 1)}
    (h : ([] : List (Fm Tm (n + 1))) ⊢[TeqAx] Fm.iff A B) :
    ([] : List (Fm Tm n)) ⊢[TeqAx]
      Fm.iff (A.subst (inst zero) ⟶ Fm.all A) (B.subst (inst zero) ⟶ Fm.all B) := by
  have h0 : ([] : List (Fm Tm n)) ⊢[TeqAx]
      Fm.iff (A.subst (inst zero)) (B.subst (inst zero)) := by
    simpa [Fm.iff] using h.subst (inst zero)
  exact Prf.iffImp h0 (Prf.iffAll h)

/-- The complete raw formula is provably equivalent to its zero-normal form. -/
theorem fnf_correct (A : NFm n) :
    ([] : List (Fm Tm n)) ⊢[TeqAx] Fm.iff A.toFm (fnf A).toFm := by
  induction A with
  | eq s t => exact Prf.eqIff (nf_correct s) (nf_correct t)
  | Q B ih => exact closure_iff ih
  | D B ih => exact Prf.iffEx (closure_iff ih)

/-- The same formula equivalence holds in the original native calculus. -/
theorem fnf_native_roundTrip (A : NFm n) :
    NPrf [A] (fnf A) ∧ NPrf [fnf A] A := by
  constructor
  · exact NPrf.iff_teq.mpr (Prf.iffMp (fnf_correct A).ofNil Prf.hyp0)
  · exact NPrf.iff_teq.mpr (Prf.iffMpr (fnf_correct A).ofNil Prf.hyp0)

end LeanProofs.ConciseIPRA.ZeroNormalization
