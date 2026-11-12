import ConciseIPRA.NativeLogic

/-!
# Equality without a template

`TPrf` is the kernel with its transport rule replaced by the rule of the
package `Research/template_free`:

  from `s = t` and `u = v` infer `v = R(u)`,

where `R = Tm.rep s t` replaces every occurrence of the term `s` in `u` by `t`,
root first and in one pass: inserted copies of `t` are not visited again.
Under the binder of an iterator the source and the target are weakened, so the
replacement is capture-free.  No template, position or context is supplied.

`tprf_iff_nprf` proves that `TPrf` derives the same sequents as the kernel.

* Soundness is `NPrf.repEq`: from `s = t` the kernel proves `u = R(u)`, by
  induction on `u`; under a binder this needs congruence of the iterator in its
  step term, which is an equation induction (`NPrf.iterBody`).
* Completeness recovers transport in a chosen template `h` from the rule,
  which cannot choose: with the marker `M = I(0, s; u.K)`, where the numeral
  `K` is larger than `h`, the term `h(M)` contains `M` at the template
  positions and nowhere else (`Tm.rep_marker`), so replacing `M` in the
  reflexivity `h(M) = h(M)` gives `h(M) = h(s)` and `h(M) = h(t)`.  Symmetry
  uses the same idea with the marker `I(0, p; u.0)`, which is larger than `p`.
  No induction is used.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m k : ℕ}

namespace Tm

/-- The number of nodes of a term. -/
def sz : {n : ℕ} → Tm n → ℕ
  | _, .var _ => 1
  | _, .zero => 1
  | _, .succ t => sz t + 1
  | _, .iter c a h => sz c + sz a + sz h + 1

theorem sz_ren (t : Tm n) : ∀ {m : ℕ} (ξ : Fin n → Fin m), sz (ren ξ t) = sz t := by
  induction t with
  | var i => intro m ξ; rfl
  | zero => intro m ξ; rfl
  | succ t ih => intro m ξ; show sz (ren ξ t) + 1 = sz t + 1; rw [ih]
  | iter c a h ihc iha ihh =>
    intro m ξ
    show sz (ren ξ c) + sz (ren ξ a) + sz (ren (upRen ξ) h) + 1 = sz c + sz a + sz h + 1
    rw [ihc, iha, ihh]

theorem sz_shift (t : Tm n) : sz (Syn.shift t) = sz t := by rw [shift_eq_ren, sz_ren]

theorem ne_of_sz_lt {u s : Tm n} (h : sz u < sz s) : u ≠ s := fun e => by
  rw [e] at h; exact lt_irrefl _ h

section Rep

open Classical

/-- Replacement of every occurrence of `s` by `t`, root first and in one
pass. -/
noncomputable def rep : {n : ℕ} → Tm n → Tm n → Tm n → Tm n
  | _, s, t, .var i => if Tm.var i = s then t else .var i
  | _, s, t, .zero => if Tm.zero = s then t else .zero
  | _, s, t, .succ a => if Tm.succ a = s then t else .succ (rep s t a)
  | _, s, t, .iter c a h =>
    if Tm.iter c a h = s then t
    else .iter (rep s t c) (rep s t a) (rep (Syn.shift s) (Syn.shift t) h)

theorem rep_var (s t : Tm n) (i : Fin n) :
    rep s t (Tm.var i) = if Tm.var i = s then t else Tm.var i := by rw [rep]

theorem rep_zero (s t : Tm n) : rep s t Tm.zero = if Tm.zero = s then t else Tm.zero := by
  rw [rep]

theorem rep_succ (s t a : Tm n) :
    rep s t (Tm.succ a) = if Tm.succ a = s then t else Tm.succ (rep s t a) := by rw [rep]

theorem rep_iter (s t c a : Tm n) (h : Tm (n + 1)) :
    rep s t (Tm.iter c a h) = if Tm.iter c a h = s then t
      else Tm.iter (rep s t c) (rep s t a) (rep (Syn.shift s) (Syn.shift t) h) := by rw [rep]

theorem rep_self (s t : Tm n) : rep s t s = t := by
  cases s with
  | var i => rw [rep_var, if_pos rfl]
  | zero => rw [rep_zero, if_pos rfl]
  | succ a => rw [rep_succ, if_pos rfl]
  | iter c a h => rw [rep_iter, if_pos rfl]

/-- A term smaller than the source is unchanged. -/
theorem rep_small (u : Tm n) : ∀ (s t : Tm n), sz u < sz s → rep s t u = u := by
  induction u with
  | var i => intro s t h; rw [rep_var, if_neg (ne_of_sz_lt h)]
  | zero => intro s t h; rw [rep_zero, if_neg (ne_of_sz_lt h)]
  | succ a ih =>
    intro s t h
    rw [rep_succ, if_neg (ne_of_sz_lt h), ih s t (by simp only [sz] at h; omega)]
  | iter c a b ihc iha ihb =>
    intro s t h
    simp only [sz] at h
    rw [rep_iter, if_neg (ne_of_sz_lt (by simp only [sz]; exact h)), ihc s t (by omega),
      iha s t (by omega), ihb _ _ (by rw [sz_shift]; omega)]

/-- The substitutions `σm` and `σs` agree on variables, except where `σm` is
the marker `M` and `σs` is `S`. -/
def Marks (M S : Tm n) (σm σs : Fin k → Tm n) : Prop :=
  ∀ i, (σm i = M ∧ σs i = S) ∨ ∃ j, σm i = Tm.var j ∧ σs i = Tm.var j

theorem Marks.up {M S : Tm n} {σm σs : Fin k → Tm n} (h : Marks M S σm σs) :
    Marks (Syn.shift M) (Syn.shift S) (Syn.up σm) (Syn.up σs) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .inr ⟨0, rfl, rfl⟩
  · rcases h j with ⟨e₁, e₂⟩ | ⟨j', e₁, e₂⟩
    · exact .inl ⟨by rw [Syn.up_succ, e₁], by rw [Syn.up_succ, e₂]⟩
    · exact .inr ⟨j'.succ, by rw [Syn.up_succ, e₁]; rfl, by rw [Syn.up_succ, e₂]; rfl⟩

/-- A substitution instance either has the size of the term or is at least as
large as the marker. -/
theorem sz_subst_marks (h : Tm k) : ∀ {n : ℕ} {M S : Tm n} {σm σs : Fin k → Tm n},
    Marks M S σm σs → sz (Syn.subst σm h) = sz h ∨ sz M ≤ sz (Syn.subst σm h) := by
  induction h with
  | var i =>
    intro n M S σm σs hσ
    rcases hσ i with ⟨e, _⟩ | ⟨j, e, _⟩
    · right; show sz M ≤ sz (σm i); rw [e]
    · left; show sz (σm i) = 1; rw [e]; rfl
  | zero => intro n M S σm σs _; exact .inl rfl
  | succ a ih =>
    intro n M S σm σs hσ
    rcases ih hσ with e | e
    · left; show sz (Syn.subst σm a) + 1 = sz a + 1; rw [e]
    · right; show sz M ≤ sz (Syn.subst σm a) + 1; omega
  | iter c a b ihc iha ihb =>
    intro n M S σm σs hσ
    rw [Tm.subst_iter]
    have hb := ihb hσ.up
    rw [sz_shift] at hb
    rcases ihc hσ with ec | ec <;> rcases iha hσ with ea | ea <;> rcases hb with eb | eb
    all_goals first | (left; simp only [sz]; omega) | (right; simp only [sz]; omega)

/-- The marker is an iterator whose step term is larger than `N`. -/
def Big (N : ℕ) (M : Tm n) : Prop := ∃ c a K, M = Tm.iter c a K ∧ N < sz K

theorem Big.shift {N : ℕ} {M : Tm n} (h : Big N M) : Big N (Syn.shift M) := by
  obtain ⟨c, a, K, rfl, hK⟩ := h
  refine ⟨ren Fin.succ c, ren Fin.succ a, ren (upRen Fin.succ) K, ?_, by rwa [sz_ren]⟩
  rw [shift_eq_ren]; rfl

theorem Big.mono {N N' : ℕ} {M : Tm n} (h : Big N M) (h' : N' ≤ N) : Big N' M := by
  obtain ⟨c, a, K, e, hK⟩ := h
  exact ⟨c, a, K, e, by omega⟩

/-- Replacing the marker in an instance of a term that is smaller than the
step term of the marker replaces exactly the marked variables. -/
theorem rep_subst (h : Tm k) : ∀ {n : ℕ} {M S : Tm n} {σm σs : Fin k → Tm n},
    Big (sz h) M → Marks M S σm σs → rep M S (Syn.subst σm h) = Syn.subst σs h := by
  induction h with
  | var i =>
    intro n M S σm σs hM hσ
    show rep M S (σm i) = σs i
    rcases hσ i with ⟨e₁, e₂⟩ | ⟨j, e₁, e₂⟩
    · rw [e₁, e₂, rep_self]
    · obtain ⟨c, a, K, rfl, _⟩ := hM
      rw [e₁, e₂, rep_var, if_neg (by intro e; cases e)]
  | zero =>
    intro n M S σm σs hM _
    obtain ⟨c, a, K, rfl, _⟩ := hM
    show rep _ S Tm.zero = Tm.zero
    rw [rep_zero, if_neg (by intro e; cases e)]
  | succ a ih =>
    intro n M S σm σs hM hσ
    have iha := ih (hM.mono (by simp only [sz]; omega)) hσ
    obtain ⟨c, a', K, rfl, _⟩ := hM
    show rep _ S (Tm.succ (Syn.subst σm a)) = Tm.succ (Syn.subst σs a)
    rw [rep_succ, if_neg (by intro e; cases e), iha]
  | iter c a b ihc iha ihb =>
    intro n M S σm σs hM hσ
    have hc := ihc (hM.mono (by simp only [sz]; omega)) hσ
    have ha := iha (hM.mono (by simp only [sz]; omega)) hσ
    have hb := ihb (hM.shift.mono (by simp only [sz]; omega)) hσ.up
    have hne : Tm.iter (Syn.subst σm c) (Syn.subst σm a) (Syn.subst (Syn.up σm) b) ≠ M := by
      obtain ⟨c₀, a₀, K, rfl, hK⟩ := hM
      intro e
      have eb := (Tm.iter.inj e).2.2
      simp only [sz] at hK
      rcases sz_subst_marks b hσ.up with e' | e'
      · rw [eb] at e'; omega
      · rw [eb, sz_shift] at e'; simp only [sz] at e'; omega
    rw [Tm.subst_iter, Tm.subst_iter, rep_iter, if_neg hne, hc, ha, hb]

end Rep

/-- A numeral of size `k + 1`. -/
def big : ℕ → Tm n
  | 0 => .zero
  | k + 1 => .succ (big k)

theorem sz_big (k : ℕ) : sz (big k : Tm n) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => show sz (big k : Tm n) + 1 = k + 1 + 1; rw [ih]

/-- The marker of a template: `I(0, s; u.K)` with `K` larger than the template. -/
def marker (h : Tm (n + 1)) (s : Tm n) : Tm n := .iter .zero s (big (sz h))

/-- Replacing the marker in `h(M)` gives `h(x)`: the marker occurs at the
template positions and nowhere else. -/
theorem rep_marker (h : Tm (n + 1)) (s x : Tm n) :
    rep (marker h s) x (Syn.subst (inst (marker h s)) h) = Syn.subst (inst x) h :=
  rep_subst h ⟨_, _, _, rfl, by rw [sz_big]; omega⟩ fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨j, by simp, by simp⟩

end Tm

/-! ### Soundness: the kernel proves `u = R(u)` -/

namespace NPrf

variable {Γ : List (NFm n)}

/-- Congruence of the iterator in its count and its seed. -/
theorem iterCongr {c c' a a' : Tm n} (b : Tm (n + 1)) (hc : NPrf Γ (.eq c c'))
    (ha : NPrf Γ (.eq a a')) : NPrf Γ (.eq (iter c a b) (iter c' a' b)) := by
  have h₁ := eqCongr
    (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b)) hc
  have h₂ := eqCongr
    (iter (Syn.shift c') (Syn.var 0) (Syn.subst (up fun i => Syn.var i.succ) b)) ha
  simp only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    Syn.subst_up_inst_up_shift] at h₁ h₂
  exact eqTrans h₁ h₂

/-- Congruence of the iterator in its step term, by equation induction on the
count. -/
theorem iterBody (c a : Tm n) {b b' : Tm (n + 1)} (hb : NPrf (Γ.map NFm.shift) (.eq b b')) :
    NPrf Γ (.eq (iter c a b) (iter c a b')) := by
  have e₁ : ∀ (X x : Tm (n + 1)),
      Syn.subst (inst X) (Syn.subst (up fun i => Syn.var i.succ) x) = Syn.subst (repl X) x := by
    intro X x
    rw [Syn.subst_subst]
    exact congrArg (fun ρ => Syn.subst ρ x) (funext fun i => by
      refine Fin.cases ?_ (fun j => ?_) i <;> simp)
  have e₂ : ∀ x : Tm (n + 1), Syn.subst (up (repl (succ (Syn.var 0))))
      (Syn.subst (up fun i => (Syn.var i.succ : Tm (n + 1))) x)
      = Syn.subst (up fun i => Syn.var i.succ) x := by
    intro x
    rw [Syn.subst_subst, Syn.up_comp]
    exact congrArg (fun ρ => Syn.subst (up ρ) x) (funext fun i => by simp)
  have h0 : NPrf Γ ((NFm.eq
      (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b))
      (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b'))).subst
        (inst zero)) := by
    simp only [NFm.subst_eq, Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      Syn.subst_up_inst_up_shift]
    exact eqTrans (.iterZero a b) (eqSymm (.iterZero a b'))
  have hS : NPrf (NFm.eq
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b))
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b'))
        :: Γ.map NFm.shift)
      ((NFm.eq
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b))
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b'))).subst
          (repl (succ (Syn.var 0)))) := by
    simp only [NFm.subst_eq, Tm.subst_iter, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift,
      e₂]
    -- both sides compute one step; the bodies agree at the common previous value
    have s₁ := NPrf.iterSucc (Γ := NFm.eq
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b))
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b'))
        :: Γ.map NFm.shift)
      (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b)
    have s₂ := NPrf.iterSucc (Γ := NFm.eq
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b))
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b'))
        :: Γ.map NFm.shift)
      (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b')
    have mid := (hb.subst (repl (iter (Syn.var 0) (Syn.shift a)
      (Syn.subst (up fun i => Syn.var i.succ) b')))).wk
      (B := NFm.eq
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b))
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b')))
    rw [NFm.map_shift_subst_repl, NFm.subst_eq] at mid
    rw [e₁] at s₁ s₂
    have cg := eqCongr (Syn.subst (up fun i => Syn.var i.succ) b)
      (hyp0 (Γ := Γ.map NFm.shift) (A := NFm.eq
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b))
        (iter (Syn.var 0) (Syn.shift a) (Syn.subst (up fun i => Syn.var i.succ) b'))))
    rw [e₁, e₁] at cg
    exact eqTrans s₁ (eqTrans cg (eqTrans mid (eqSymm s₂)))
  have key := NPrf.eqInd _ _ c h0 hS
  simpa only [NFm.subst_eq, Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    Syn.subst_up_inst_up_shift] using key

/-- From `s = t` the kernel proves `u = R(u)`. -/
theorem repEq (u : Tm n) : ∀ {s t : Tm n} {Γ : List (NFm n)},
    NPrf Γ (.eq s t) → NPrf Γ (.eq u (Tm.rep s t u)) := by
  induction u with
  | var i =>
    intro s t Γ h
    rw [Tm.rep_var]
    split
    · next e => rw [e]; exact h
    · exact eqRefl _
  | zero =>
    intro s t Γ h
    rw [Tm.rep_zero]
    split
    · next e => rw [e]; exact h
    · exact eqRefl _
  | succ a ih =>
    intro s t Γ h
    rw [Tm.rep_succ]
    split
    · next e => rw [e]; exact h
    · exact eqCongr (succ (Syn.var 0)) (ih h)
  | iter c a b ihc iha ihb =>
    intro s t Γ h
    rw [Tm.rep_iter]
    split
    · next e => rw [e]; exact h
    · exact eqTrans (iterCongr b (ihc h) (iha h)) (iterBody _ _ (ihb h.shift))

end NPrf

/-- Derivability in the kernel with the template-free replacement rule in place
of transport. -/
inductive TPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : TPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      TPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      TPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- Replacement: from `s = t` and `u = v` infer `v = R(u)`. -/
  | tf {n : ℕ} {Γ : List (NFm n)} {s t u v : Tm n}
      (h₁ : TPrf Γ (.eq s t)) (h₂ : TPrf Γ (.eq u v)) : TPrf Γ (.eq v (Tm.rep s t u))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : TPrf Γ (.Q B)) (h₂ : TPrf Γ (B.subst (inst zero))) : TPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : TPrf Γ (.D B)) (h₂ : TPrf (.Q B :: Γ.map NFm.shift) A.shift) : TPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : TPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      TPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : TPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      TPrf Γ (.Q (.eq s₁ s₂))

namespace TPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem eqRefl (a : Tm n) : TPrf Γ (.eq a a) := by
  have h := TPrf.tf (Γ := Γ) (.iterZero a (Syn.var 0)) (.iterZero a (Syn.var 0))
  rwa [Tm.rep_self] at h

/-- Symmetry: replace the marker `I(0, p; u.0)`, which is larger than `p`. -/
theorem eqSymm {p q : Tm n} (h : TPrf Γ (.eq p q)) : TPrf Γ (.eq q p) := by
  have k := TPrf.tf (.iterZero p zero) h
  rwa [Tm.rep_small p _ p (by simp only [Tm.sz]; omega)] at k

theorem eqTrans {p q r : Tm n} (h₁ : TPrf Γ (.eq p q)) (h₂ : TPrf Γ (.eq q r)) :
    TPrf Γ (.eq p r) := by
  have k := TPrf.tf h₂ (eqSymm h₁)
  rwa [Tm.rep_self] at k

/-- Congruence in a chosen template along an equation whose source is the
marker of the template. -/
theorem markerCongr (h : Tm (n + 1)) (s : Tm n) {x : Tm n}
    (e : TPrf Γ (.eq (Tm.marker h s) x)) :
    TPrf Γ (.eq (Syn.subst (inst (Tm.marker h s)) h) (Syn.subst (inst x) h)) := by
  have k := TPrf.tf e (eqRefl (Syn.subst (inst (Tm.marker h s)) h))
  rwa [Tm.rep_marker] at k

/-- Transport in one term, in a chosen template. -/
theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (h₁ : TPrf Γ (.eq s t))
    (h₂ : TPrf Γ (.eq (Syn.subst (inst s) h) u)) : TPrf Γ (.eq u (Syn.subst (inst t) h)) := by
  have e₁ : TPrf Γ (.eq (Tm.marker h s) s) := .iterZero s _
  exact eqTrans (eqSymm h₂)
    (eqTrans (eqSymm (markerCongr h s e₁)) (markerCongr h s (eqTrans e₁ h₁)))

theorem toNPrf (h : TPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | tf _ _ ih₁ ih₂ => exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.repEq _ ih₁)
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

end TPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem NPrf.toTPrf (h : NPrf Γ A) : TPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact TPrf.trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

/-- **Equality without a template.**  The replacement rule derives the same
sequents as the kernel's transport. -/
theorem tprf_iff_nprf : TPrf Γ A ↔ NPrf Γ A := ⟨TPrf.toNPrf, NPrf.toTPrf⟩

end LeanProofs.ConciseIPRA
