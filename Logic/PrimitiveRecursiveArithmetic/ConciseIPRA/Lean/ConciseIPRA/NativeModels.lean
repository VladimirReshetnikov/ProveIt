import ConciseIPRA.NativeBiInterpretation

/-!
# Readings of the native language, consistency, and independence of the rules

A *reading* (`Sem`) of the native language over the natural numbers fixes the
value of the iterator, the meaning of an equation, and the meanings of the two
binders `Q` and `D`.  Terms are evaluated by `Tm.val` and formulas by
`NFm.sat`.

`FPrf r` is the kernel with each of its eight rules switched on or off by the
flags `r`; with all of them on it is the kernel (`fprf_all_iff_nprf`).  The
one soundness theorem `FPrf.sound` asks, of a reading, one condition for each
rule that is switched on (`Sem.Sound`).

* **Consistency.**  The standard reading satisfies every condition, so the
  kernel does not derive `0 = 1` (`native_consistent`).  Through the
  bi-interpretation this is the consistency of `T_eq` and of iPRA
  (`teq_consistent`, `pra_consistent`): a proof that evaluates iterator terms
  only.
* **Independence.**  Seven of the eight rules cannot be dropped.  For each of
  the two computation equations, transport, `QE`, `DE` and the introduction of
  `D`, a reading satisfies the conditions of the other rules and refutes a
  sequent that the kernel derives (`indep_iterZero`, `indep_iterSucc`,
  `indep_trOne`, `indep_qE`, `indep_dE`, `indep_dICase`).  Without the
  hypothesis rule a derivation does not depend on its context
  (`FPrf.ctx`), which gives `indep_hyp`.

The independence of the progress rule `qIInd` is not obtained in this way: in
a reading over the natural numbers the conditions for the introduction and the
elimination of `D` already imply the condition for `qIInd` (`Sem.Sound.qIInd_of`).
It needs a structure with nonstandard numbers.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m k : ℕ}

/-- A reading of the native language over the natural numbers. -/
structure Sem where
  /-- The value of the iterator, from the values of its count and seed and the
  function of its step term. -/
  it : ℕ → ℕ → (ℕ → ℕ) → ℕ
  /-- The meaning of an equation. -/
  eqv : ℕ → ℕ → Prop
  /-- The meaning of `Q`. -/
  q : (ℕ → Prop) → Prop
  /-- The meaning of `D`. -/
  d : (ℕ → ℕ → Prop) → Prop

/-- The standard reading. -/
def Sem.std : Sem where
  it c a f := Nat.rec a (fun _ u => f u) c
  eqv := Eq
  q P := P 0 → ∀ y, P y
  d P := ∃ x, P x 0 → ∀ y, P x y

namespace Tm

/-- The value of a term. -/
def val (S : Sem) : {n : ℕ} → Tm n → (Fin n → ℕ) → ℕ
  | _, .var i, ρ => ρ i
  | _, .zero, _ => 0
  | _, .succ t, ρ => val S t ρ + 1
  | _, .iter c a h, ρ => S.it (val S c ρ) (val S a ρ) fun u => val S h (Fin.cases u ρ)

variable (S : Sem)

theorem val_ren (t : Tm n) : ∀ {m : ℕ} (ξ : Fin n → Fin m) (ρ : Fin m → ℕ),
    (ren ξ t).val S ρ = t.val S fun i => ρ (ξ i) := by
  induction t with
  | var i => intro m ξ ρ; rfl
  | zero => intro m ξ ρ; rfl
  | succ t ih => intro m ξ ρ; simp only [ren, val, ih]
  | iter c a h ihc iha ihh =>
    intro m ξ ρ
    simp only [ren, val, ihc, iha, ihh]
    congr 1
    funext u
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem val_sub (t : Tm n) : ∀ {m : ℕ} (σ : Fin n → Tm m) (ρ : Fin m → ℕ),
    (sub σ t).val S ρ = t.val S fun i => (σ i).val S ρ := by
  induction t with
  | var i => intro m σ ρ; rfl
  | zero => intro m σ ρ; rfl
  | succ t ih => intro m σ ρ; simp only [sub, val, ih]
  | iter c a h ihc iha ihh =>
    intro m σ ρ
    simp only [sub, val, ihc, iha, ihh]
    congr 1
    funext u
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [upS, val_ren]

theorem val_subst (σ : Fin n → Tm m) (t : Tm n) (ρ : Fin m → ℕ) :
    (Syn.subst σ t).val S ρ = t.val S fun i => (σ i).val S ρ := val_sub S t σ ρ

theorem val_shift (t : Tm n) (b : ℕ) (ρ : Fin n → ℕ) :
    (Syn.shift t).val S (Fin.cases b ρ) = t.val S ρ := by
  unfold Syn.shift
  rw [val_subst]
  rfl

theorem val_inst (t : Tm n) (ρ : Fin n → ℕ) :
    (fun i => (inst t i).val S ρ) = Fin.cases (t.val S ρ) ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Syn.inst_succ, Fin.cases_succ]
    rfl

theorem val_up (σ : Fin n → Tm m) (y : ℕ) (ρ : Fin m → ℕ) :
    (fun i => (up σ i).val S (Fin.cases y ρ)) = Fin.cases y fun i => (σ i).val S ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Syn.up_succ, Fin.cases_succ, val_shift]

theorem val_repl (s : Tm (n + 1)) (z : ℕ) (ρ : Fin n → ℕ) :
    (fun i => (repl s i).val S (Fin.cases z ρ)) = Fin.cases (s.val S (Fin.cases z ρ)) ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Syn.repl_succ, Fin.cases_succ]
    rfl

end Tm

namespace NFm

/-- The truth of a formula. -/
def sat (S : Sem) : {n : ℕ} → NFm n → (Fin n → ℕ) → Prop
  | _, .eq s t, ρ => S.eqv (s.val S ρ) (t.val S ρ)
  | _, .Q B, ρ => S.q fun y => sat S B (Fin.cases y ρ)
  | _, .D B, ρ => S.d fun x y => sat S B (Fin.cases y (Fin.cases x ρ))

variable (S : Sem)

theorem sat_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m) (ρ : Fin m → ℕ),
    (A.subst σ).sat S ρ = A.sat S fun i => (σ i).val S ρ := by
  induction A with
  | eq s t => intro m σ ρ; simp only [subst_eq, sat, Tm.val_subst]
  | Q B ih => intro m σ ρ; simp only [subst_Q, sat, ih, Tm.val_up]
  | D B ih => intro m σ ρ; simp only [subst_D, sat, ih, Tm.val_up]

theorem sat_shift (A : NFm n) (b : ℕ) (ρ : Fin n → ℕ) :
    A.shift.sat S (Fin.cases b ρ) = A.sat S ρ := by
  unfold NFm.shift
  rw [sat_subst]
  rfl

theorem sat_inst (B : NFm (n + 1)) (t : Tm n) (ρ : Fin n → ℕ) :
    (B.subst (inst t)).sat S ρ = B.sat S (Fin.cases (t.val S ρ) ρ) := by
  rw [sat_subst, Tm.val_inst]

theorem sat_repl (B : NFm (n + 1)) (s : Tm (n + 1)) (z : ℕ) (ρ : Fin n → ℕ) :
    (B.subst (repl s)).sat S (Fin.cases z ρ) = B.sat S (Fin.cases (s.val S (Fin.cases z ρ)) ρ) := by
  rw [sat_subst, Tm.val_repl]

theorem sat_up_inst (B : NFm (n + 2)) (t : Tm n) (y : ℕ) (ρ : Fin n → ℕ) :
    (B.subst (up (inst t))).sat S (Fin.cases y ρ)
      = B.sat S (Fin.cases y (Fin.cases (t.val S ρ) ρ)) := by
  rw [sat_subst, Tm.val_up, Tm.val_inst]

end NFm

/-- A choice of rules of the kernel. -/
structure Rules where
  hyp : Bool
  iterZero : Bool
  iterSucc : Bool
  trOne : Bool
  qE : Bool
  dE : Bool
  dICase : Bool
  qIInd : Bool

/-- All eight rules. -/
def Rules.all : Rules := ⟨true, true, true, true, true, true, true, true⟩

/-- The kernel with the rules chosen by `r`. -/
inductive FPrf (r : Rules) : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (e : r.hyp = true) (h : A ∈ Γ) : FPrf r Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (e : r.iterZero = true) (a : Tm n) (h : Tm (n + 1)) :
      FPrf r Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (e : r.iterSucc = true) (c a : Tm n) (h : Tm (n + 1)) :
      FPrf r Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (e : r.trOne = true) (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : FPrf r Γ (.eq s t)) (h₂ : FPrf r Γ (.eq (Syn.subst (inst s) h) u)) :
      FPrf r Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (e : r.qE = true) (t : Tm n)
      (h₁ : FPrf r Γ (.Q B)) (h₂ : FPrf r Γ (B.subst (inst zero))) :
      FPrf r Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n} (e : r.dE = true)
      (h₁ : FPrf r Γ (.D B)) (h₂ : FPrf r (.Q B :: Γ.map NFm.shift) A.shift) : FPrf r Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (e : r.dICase = true) (B : NFm (n + 2)) (t : Tm n)
      (h : FPrf r (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      FPrf r Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (e : r.qIInd = true) (s₁ s₂ : Tm (n + 1))
      (h : FPrf r (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      FPrf r Γ (.Q (.eq s₁ s₂))

/-- The conditions on a reading, one for each rule that is switched on. -/
structure Sem.Sound (S : Sem) (r : Rules) : Prop where
  iterZero : r.iterZero = true → ∀ a f, S.eqv (S.it 0 a f) a
  iterSucc : r.iterSucc = true → ∀ c a f, S.eqv (S.it (c + 1) a f) (f (S.it c a f))
  trOne : r.trOne = true → ∀ (g : ℕ → ℕ) s t u, S.eqv s t → S.eqv (g s) u → S.eqv u (g t)
  qE : r.qE = true → ∀ (P : ℕ → Prop) t, S.q P → P 0 → P t
  dE : r.dE = true → ∀ (P : ℕ → ℕ → Prop) (A : Prop), S.d P → (∀ b, S.q (P b) → A) → A
  dICase : r.dICase = true → ∀ (P : ℕ → ℕ → Prop) t, (∀ z, P t 0 → P t (z + 1)) → S.d P
  qIInd : r.qIInd = true → ∀ f g : ℕ → ℕ,
    (∀ z, S.eqv (f z) (g z) → S.eqv (f (z + 1)) (g (z + 1))) → S.q fun y => S.eqv (f y) (g y)

/-- Over the natural numbers the conditions for the two rules of `D` imply the
condition for the progress rule, whatever the reading of an equation. -/
theorem Sem.Sound.qIInd_of {S : Sem} {r : Rules} (hS : S.Sound r) (e₁ : r.dE = true)
    (e₂ : r.dICase = true) (f g : ℕ → ℕ)
    (h : ∀ z, S.eqv (f z) (g z) → S.eqv (f (z + 1)) (g (z + 1))) :
    S.q fun y => S.eqv (f y) (g y) := by
  refine hS.dE e₁ (fun _ y => S.eqv (f y) (g y)) _ (hS.dICase e₂ _ 0 fun z h0 => ?_)
    fun _ hq => hq
  induction z with
  | zero => exact h 0 h0
  | succ z ih => exact h _ ih

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Soundness** of the chosen rules for a reading that satisfies their
conditions. -/
theorem FPrf.sound {S : Sem} {r : Rules} (hS : S.Sound r) (h : FPrf r Γ A) :
    ∀ ρ : Fin n → ℕ, (∀ X ∈ Γ, X.sat S ρ) → A.sat S ρ := by
  induction h with
  | hyp _ h => intro ρ hΓ; exact hΓ _ h
  | iterZero e a h => intro ρ _; exact hS.iterZero e _ _
  | iterSucc e c a h =>
    intro ρ _
    show S.eqv _ ((Syn.subst (inst (iter c a h)) h).val S ρ)
    rw [Tm.val_subst, Tm.val_inst]
    exact hS.iterSucc e _ _ _
  | trOne e h _ _ ih₁ ih₂ =>
    intro ρ hΓ
    have e₂ := ih₂ ρ hΓ
    simp only [NFm.sat, Tm.val_subst, Tm.val_inst] at e₂ ⊢
    exact hS.trOne e (fun x => h.val S (Fin.cases x ρ)) _ _ _ (ih₁ ρ hΓ) e₂
  | @qE _ Γ B e t _ _ ih₁ ih₂ =>
    intro ρ hΓ
    have h₂ := ih₂ ρ hΓ
    rw [NFm.sat_inst] at h₂ ⊢
    have hq : S.q fun y => B.sat S (Fin.cases y ρ) := ih₁ ρ hΓ
    exact hS.qE e _ _ hq h₂
  | @dE _ Γ B A e _ _ ih₁ ih₂ =>
    intro ρ hΓ
    refine hS.dE e _ _ (ih₁ ρ hΓ) fun b hq => ?_
    rw [← NFm.sat_shift S A b ρ]
    refine ih₂ (Fin.cases b ρ) fun X hX => ?_
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hq
    · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      rw [NFm.sat_shift]
      exact hΓ Y hY
  | @dICase _ Γ e B t _ ih =>
    intro ρ hΓ
    refine hS.dICase e _ (t.val S ρ) fun z h0 => ?_
    have h := ih (Fin.cases z ρ) fun X hX => by
      rcases List.mem_cons.1 hX with rfl | hX
      · rw [NFm.sat_shift, NFm.sat_inst, NFm.sat_up_inst]
        exact h0
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        rw [NFm.sat_shift]
        exact hΓ Y hY
    rw [NFm.sat_repl, NFm.sat_up_inst] at h
    exact h
  | @qIInd _ Γ e s₁ s₂ _ ih =>
    intro ρ hΓ
    refine hS.qIInd e (fun y => s₁.val S (Fin.cases y ρ)) (fun y => s₂.val S (Fin.cases y ρ))
      fun z hz => ?_
    have h := ih (Fin.cases z ρ) fun X hX => by
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hz
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        rw [NFm.sat_shift]
        exact hΓ Y hY
    simp only [NFm.subst_eq, NFm.sat, Tm.val_subst, Tm.val_repl] at h
    exact h

theorem FPrf.toNPrf {r : Rules} (h : FPrf r Γ A) : NPrf Γ A := by
  induction h with
  | hyp _ h => exact .hyp h
  | iterZero _ a h => exact .iterZero a h
  | iterSucc _ c a h => exact .iterSucc c a h
  | trOne _ h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE _ t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase _ B t _ ih => exact .dICase B t ih
  | qIInd _ s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

theorem NPrf.toFPrf (h : NPrf Γ A) : FPrf .all Γ A := by
  induction h with
  | hyp h => exact .hyp rfl h
  | iterZero a h => exact .iterZero rfl a h
  | iterSucc c a h => exact .iterSucc rfl c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne rfl h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE rfl t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE rfl ih₁ ih₂
  | dICase B t _ ih => exact .dICase rfl B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd rfl s₁ s₂ ih

/-- With all rules switched on, `FPrf` is the kernel. -/
theorem fprf_all_iff_nprf : FPrf .all Γ A ↔ NPrf Γ A := ⟨FPrf.toNPrf, NPrf.toFPrf⟩

/-! ### The standard reading and consistency -/

theorem Sem.std_sound (r : Rules) : Sem.std.Sound r where
  iterZero _ _ _ := rfl
  iterSucc _ _ _ _ := rfl
  trOne _ g s t u e₁ e₂ := by subst e₁; exact e₂.symm
  qE _ _ t hq h0 := hq h0 t
  dE _ _ _ hd H := hd.elim fun b hb => H b hb
  dICase _ _ t H := ⟨t, fun h0 y => by cases y with | zero => exact h0 | succ z => exact H z h0⟩
  qIInd _ f g H h0 y := by
    induction y with
    | zero => exact h0
    | succ z ih => exact H z ih

/-- The kernel is sound for the standard reading. -/
theorem NPrf.sound_std (h : NPrf Γ A) (ρ : Fin n → ℕ) (hΓ : ∀ X ∈ Γ, X.sat .std ρ) :
    A.sat .std ρ :=
  h.toFPrf.sound (Sem.std_sound _) ρ hΓ

/-- **The native scalar core is consistent.** -/
theorem native_consistent : ¬ NPrf ([] : List (NFm 0)) NFm.bot := fun h =>
  Nat.succ_ne_zero 0 (h.sound_std (fun i => i.elim0) (fun _ hX => nomatch hX)).symm

/-- **iPRA is consistent**, by the standard reading of the native core and the
bi-interpretation. -/
theorem pra_consistent : ¬ ([] ⊢[PRAAx] (Fm.bot : Fm PTm 0)) := fun h =>
  native_consistent (native_inconsistent_iff.2 h)

/-- **`T_eq` is consistent.** -/
theorem teq_consistent : ¬ ([] ⊢[TeqAx] (Fm.bot : Fm Tm 0)) := fun h =>
  pra_consistent (teq_consistent_iff.1 h)

/-! ### Independence of seven rules -/

/-- From `Q_y (sel(y, 0, 1) = 0)` the kernel derives `0 = 1`. -/
theorem NPrf.selQBot (h : NPrf Γ (.Q (.eq (Tm.sel (Syn.var 0) zero (succ zero)) zero))) :
    NPrf Γ (.eq zero (succ zero)) := by
  have k := NPrf.qE (succ zero) h (by
    simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_zero,
      Tm.subst_succ]
    exact NPrf.selZero _ _)
  simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_zero,
    Tm.subst_succ] at k
  exact NPrf.eqTrans (NPrf.eqSymm k) (NPrf.selSucc zero zero (succ zero))

/-- The zero equation of the iterator is independent: read `I(c, a; u.h)` as
`h` applied `c + 1` times to `a`. -/
theorem indep_iterZero :
    NPrf ([] : List (NFm 0)) (.eq (iter zero zero (succ (Syn.var 0))) zero)
      ∧ ¬ FPrf { Rules.all with iterZero := false } ([] : List (NFm 0))
        (.eq (iter zero zero (succ (Syn.var 0))) zero) := by
  refine ⟨.iterZero _ _, fun h => ?_⟩
  have hS : Sem.Sound { Sem.std with it := fun c a f => Nat.rec (f a) (fun _ u => f u) c }
      { Rules.all with iterZero := false } :=
    { Sem.std_sound _ with
      iterZero := fun e => absurd e (by decide)
      iterSucc := fun _ _ _ _ => rfl }
  exact Nat.succ_ne_zero 0 (h.sound hS (fun i => i.elim0) (fun _ hX => nomatch hX))

/-- The successor equation of the iterator is independent: read
`I(c, a; u.h)` as `a`. -/
theorem indep_iterSucc :
    NPrf ([] : List (NFm 0)) (.eq (iter (succ zero) zero (succ (Syn.var 0)))
        (succ (iter zero zero (succ (Syn.var 0)))))
      ∧ ¬ FPrf { Rules.all with iterSucc := false } ([] : List (NFm 0))
        (.eq (iter (succ zero) zero (succ (Syn.var 0)))
          (succ (iter zero zero (succ (Syn.var 0))))) := by
  refine ⟨.iterSucc _ _ _, fun h => ?_⟩
  have hS : Sem.Sound { Sem.std with it := fun _ a _ => a }
      { Rules.all with iterSucc := false } :=
    { Sem.std_sound _ with
      iterZero := fun _ _ _ => rfl
      iterSucc := fun e => absurd e (by decide) }
  exact Nat.succ_ne_zero 0 (h.sound hS (fun i => i.elim0) (fun _ hX => nomatch hX)).symm

/-- Transport is independent: read an equation `s = t` as `s ≤ t`. -/
theorem indep_trOne :
    NPrf [NFm.eq (zero : Tm 0) (succ zero)] (.eq (succ zero) zero)
      ∧ ¬ FPrf { Rules.all with trOne := false } [NFm.eq (zero : Tm 0) (succ zero)]
        (.eq (succ zero) zero) := by
  refine ⟨NPrf.eqSymm NPrf.hyp0, fun h => ?_⟩
  have hS : Sem.Sound { Sem.std with eqv := fun a b => a ≤ b }
      { Rules.all with trOne := false } :=
    { Sem.std_sound _ with
      iterZero := fun _ _ _ => le_refl _
      iterSucc := fun _ _ _ _ => le_refl _
      trOne := fun e => absurd e (by decide)
      qIInd := fun _ f g H h0 y => by
        induction y with
        | zero => exact h0
        | succ z ih => exact H z ih }
  have k := h.sound hS (fun i => i.elim0) fun X hX => by
    rcases List.mem_singleton.1 hX with rfl
    exact Nat.zero_le _
  exact Nat.not_succ_le_zero 0 k

/-- `QE` is independent: read every `Q` and `D` formula as true. -/
theorem indep_qE :
    NPrf [NFm.Q (.eq (Tm.sel (Syn.var 0) zero (succ zero)) zero)]
        (.eq (zero : Tm 0) (succ zero))
      ∧ ¬ FPrf { Rules.all with qE := false }
        [NFm.Q (.eq (Tm.sel (Syn.var 0) zero (succ zero)) zero)]
        (.eq (zero : Tm 0) (succ zero)) := by
  refine ⟨NPrf.selQBot NPrf.hyp0, fun h => ?_⟩
  have hS : Sem.Sound { Sem.std with q := fun _ => True, d := fun _ => True }
      { Rules.all with qE := false } :=
    { Sem.std_sound _ with
      qE := fun e => absurd e (by decide)
      dE := fun _ _ _ _ H => H 0 trivial
      dICase := fun _ _ _ _ => trivial
      qIInd := fun _ _ _ _ => trivial }
  have k := h.sound hS (fun i => i.elim0) fun X hX => by
    rcases List.mem_singleton.1 hX with rfl
    trivial
  exact Nat.succ_ne_zero 0 k.symm

/-- `DE` is independent: read every `D` formula as true. -/
theorem indep_dE :
    NPrf [NFm.D (.eq (Tm.sel (Syn.var 0) zero (succ zero)) zero)]
        (.eq (zero : Tm 0) (succ zero))
      ∧ ¬ FPrf { Rules.all with dE := false }
        [NFm.D (.eq (Tm.sel (Syn.var 0) zero (succ zero)) zero)]
        (.eq (zero : Tm 0) (succ zero)) := by
  refine ⟨.dE NPrf.hyp0 (NPrf.selQBot NPrf.hyp0), fun h => ?_⟩
  have hS : Sem.Sound { Sem.std with d := fun _ => True } { Rules.all with dE := false } :=
    { Sem.std_sound _ with
      dE := fun e => absurd e (by decide)
      dICase := fun _ _ _ _ => trivial }
  have k := h.sound hS (fun i => i.elim0) fun X hX => by
    rcases List.mem_singleton.1 hX with rfl
    trivial
  exact Nat.succ_ne_zero 0 k.symm

/-- The introduction of `D` is independent: read every `D` formula as
false. -/
theorem indep_dICase :
    NPrf ([] : List (NFm 0)) (.D (.eq zero zero))
      ∧ ¬ FPrf { Rules.all with dICase := false } ([] : List (NFm 0)) (.D (.eq zero zero)) := by
  refine ⟨.dICase _ zero (NPrf.eqRefl zero), fun h => ?_⟩
  have hS : Sem.Sound { Sem.std with d := fun _ => False }
      { Rules.all with dICase := false } :=
    { Sem.std_sound _ with
      dE := fun _ _ _ hd _ => hd.elim
      dICase := fun e => absurd e (by decide) }
  exact h.sound hS (fun i => i.elim0) (fun _ hX => nomatch hX)

/-- Without the hypothesis rule a derivation does not depend on its
context. -/
theorem FPrf.ctx {r : Rules} (e : r.hyp = false) (h : FPrf r Γ A) :
    ∀ Δ : List (NFm n), FPrf r Δ A := by
  induction h with
  | hyp e' _ => rw [e] at e'; cases e'
  | iterZero e' a h => intro Δ; exact .iterZero e' a h
  | iterSucc e' c a h => intro Δ; exact .iterSucc e' c a h
  | trOne e' h _ _ ih₁ ih₂ => intro Δ; exact .trOne e' h (ih₁ Δ) (ih₂ Δ)
  | qE e' t _ _ ih₁ ih₂ => intro Δ; exact .qE e' t (ih₁ Δ) (ih₂ Δ)
  | dE e' _ _ ih₁ ih₂ => intro Δ; exact .dE e' (ih₁ Δ) (ih₂ _)
  | dICase e' B t _ ih => intro Δ; exact .dICase e' B t (ih _)
  | qIInd e' s₁ s₂ _ ih => intro Δ; exact .qIInd e' s₁ s₂ (ih _)

/-- The hypothesis rule is independent. -/
theorem indep_hyp :
    NPrf [(NFm.bot : NFm 0)] NFm.bot
      ∧ ¬ FPrf { Rules.all with hyp := false } [(NFm.bot : NFm 0)] NFm.bot :=
  ⟨NPrf.hyp0, fun h => native_consistent (h.ctx rfl []).toNPrf⟩

end LeanProofs.ConciseIPRA
