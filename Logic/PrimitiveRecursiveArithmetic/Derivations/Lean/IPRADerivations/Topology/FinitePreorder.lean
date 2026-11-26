import IPRADerivations.Core.Descent

/-!
# Finite topology through the specialization preorder

Packet: `topology/ipra_topology_framework_2026-11-15` (Section "Finite topology inside iPRA":
`thm:finite-preorder`, `thm:finite-continuity`). A finite space is presented by a relation
`x ≼ y`; the open sets are the upward-closed sets. Here the relation is an arbitrary formula
`R(x, y)` and a set is a formula `A(x, p)` with a parameter `p`; nothing is assumed to be bounded
or decidable, and the derivations are first-order logic in iPRA.

* `Up R A p`: `A(·, p)` is upward closed, `∀ x y, A(x, p) ∧ R(x, y) → A(y, p)`;
* `up_bot`, `up_univ`, `up_inter`, `up_union`: the upward-closed sets contain the empty set and
  the whole space and are closed under intersection and union, so they form a topology;
* `nbhd_up`, `nbhd_self`, `nbhd_least`: for a preorder, `U_x = {y : x ≼ y}` is open, contains `x`,
  and is contained in every open set containing `x`; it is the minimal neighbourhood, and
  `y ∈ U_x ↔ x ≼ y` recovers the relation;
* `t0_of_antisym`: if `≼` is antisymmetric, points with `y ∈ U_x` and `x ∈ U_y` are equal;
* `preimage_up`: for a monotone `f`, the preimage of an upward-closed set is upward closed;
* `mono_of_continuous`: if the preimage of every minimal neighbourhood `U_{f(x)}` is upward
  closed, then `f` is monotone.

The coded list of open sets of a given topology, the mutual-inverse statement and the homology
constructions are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.FinitePreorder

open_ipra

variable {m : ℕ} {Γ : List (Fm PTm m)}

/-! ## Substitution lemmas -/

theorem up_one {j k : ℕ} (σ : Fin (j + 1) → PTm k) : Syn.up σ 1 = Syn.shift (σ 0) := Syn.up_succ σ 0
theorem up_two {j k : ℕ} (σ : Fin (j + 2) → PTm k) : Syn.up σ 2 = Syn.shift (σ 1) := Syn.up_succ σ 1

theorem shift_var {k : ℕ} (i : Fin k) : Syn.shift (var i : PTm k) = var i.succ := by simp [Syn.shift]

theorem subst_up_shift {j k : ℕ} (σ : Fin j → PTm k) (t : PTm j) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

/-- `A(s, t)` for a formula `A` in two variables. -/
abbrev App {m : ℕ} (A : Fm PTm 2) (s t : PTm m) : Fm PTm m := A.subst ![s, t]

theorem subst_App (A : Fm PTm 2) {j k : ℕ} (σ : Fin j → PTm k) (s t : PTm j) :
    (App A s t).subst σ = App A (Syn.subst σ s) (Syn.subst σ t) := by
  simp only [App, Fm.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-! ## Properties of a relation -/

/-- `∀ x, R(x, x)`. -/
def Refl {m : ℕ} (R : Fm PTm 2) : Fm PTm m := Fm.all (App R (var 0) (var 0))

/-- `∀ x y z, R(x, y) ∧ R(y, z) → R(x, z)`. -/
def Trans {m : ℕ} (R : Fm PTm 2) : Fm PTm m :=
  Fm.all (Fm.all (Fm.all ((App R (var 2) (var 1) ⋏ App R (var 1) (var 0)) ⟶ App R (var 2) (var 0))))

/-- `∀ x y, R(x, y) ∧ R(y, x) → x = y`. -/
def Antisym {m : ℕ} (R : Fm PTm 2) : Fm PTm m :=
  Fm.all (Fm.all ((App R (var 1) (var 0) ⋏ App R (var 0) (var 1)) ⟶ (var 1 ≐ var 0)))

/-- `A(·, p)` is upward closed: `∀ x y, A(x, p) ∧ R(x, y) → A(y, p)`. -/
def Up {m : ℕ} (R A : Fm PTm 2) (p : PTm m) : Fm PTm m :=
  Fm.all (Fm.all ((App A (var 1) (Syn.shift (Syn.shift p)) ⋏ App R (var 1) (var 0)) ⟶
    App A (var 0) (Syn.shift (Syn.shift p))))

/-- `f` is monotone: `∀ x y, R(x, y) → S(f x, f y)`. -/
def Mono {m : ℕ} (R S : Fm PTm 2) (f : PTm 1) : Fm PTm m :=
  Fm.all (Fm.all (App R (var 1) (var 0) ⟶ App S (inst1 f (var 1)) (inst1 f (var 0))))

theorem subst_Refl (R : Fm PTm 2) {k : ℕ} (σ : Fin m → PTm k) : (Refl R : Fm PTm m).subst σ = Refl R := by
  simp only [Refl, Fm.subst_all, subst_App, Syn.subst_var, Syn.up_zero]

theorem subst_Trans (R : Fm PTm 2) {k : ℕ} (σ : Fin m → PTm k) : (Trans R : Fm PTm m).subst σ = Trans R := by
  simp only [Trans, Fm.subst_all, Fm.subst_imp, Fm.subst_and, subst_App, Syn.subst_var, Syn.up_zero, up_one,
    up_two, shift_var, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

theorem subst_Antisym (R : Fm PTm 2) {k : ℕ} (σ : Fin m → PTm k) :
    (Antisym R : Fm PTm m).subst σ = Antisym R := by
  simp only [Antisym, Fm.subst_all, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_App, Syn.subst_var,
    Syn.up_zero, up_one, shift_var, Fin.succ_zero_eq_one]

theorem subst_Up (R A : Fm PTm 2) {k : ℕ} (σ : Fin m → PTm k) (p : PTm m) :
    (Up R A p).subst σ = Up R A (Syn.subst σ p) := by
  simp only [Up, Fm.subst_all, Fm.subst_imp, Fm.subst_and, subst_App, Syn.subst_var, Syn.up_zero, up_one,
    shift_var, Fin.succ_zero_eq_one, subst_up_shift]

theorem subst_Mono (R S : Fm PTm 2) (f : PTm 1) {k : ℕ} (σ : Fin m → PTm k) :
    (Mono R S f : Fm PTm m).subst σ = Mono R S f := by
  simp only [Mono, Fm.subst_all, Fm.subst_imp, subst_App, subst_inst1, Syn.subst_var, Syn.up_zero, up_one,
    shift_var, Fin.succ_zero_eq_one]

/-! ## Eliminations -/

theorem refl_elim {R : Fm PTm 2} (h : Γ ⊢[PRAAx] Refl R) (s : PTm m) : Γ ⊢[PRAAx] App R s s := by
  have h₁ := Prf.allE s h
  simpa only [subst_App, Syn.subst_var, Syn.inst_zero] using h₁

theorem trans_elim {R : Fm PTm 2} (h : Γ ⊢[PRAAx] Trans R) {s t u : PTm m}
    (h₁ : Γ ⊢[PRAAx] App R s t) (h₂ : Γ ⊢[PRAAx] App R t u) : Γ ⊢[PRAAx] App R s u := by
  have h₃ := Prf.allE u (Prf.allE t (Prf.allE s h))
  simp only [Fm.subst_imp, Fm.subst_and, subst_App, Syn.subst_var, Syn.up_zero, up_one, up_two, shift_var,
    Fin.succ_zero_eq_one, subst_up_shift, Syn.subst_inst_shift, Syn.inst_zero] at h₃
  exact .impE h₃ (.andI h₁ h₂)

theorem antisym_elim {R : Fm PTm 2} (h : Γ ⊢[PRAAx] Antisym R) {s t : PTm m}
    (h₁ : Γ ⊢[PRAAx] App R s t) (h₂ : Γ ⊢[PRAAx] App R t s) : Γ ⊢[PRAAx] s ≐ t := by
  have h₃ := Prf.allE t (Prf.allE s h)
  simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_App, Syn.subst_var, Syn.up_zero, up_one,
    shift_var, Fin.succ_zero_eq_one, subst_up_shift, Syn.subst_inst_shift, Syn.inst_zero] at h₃
  exact .impE h₃ (.andI h₁ h₂)

theorem up_elim {R A : Fm PTm 2} {p : PTm m} (h : Γ ⊢[PRAAx] Up R A p) {s t : PTm m}
    (hs : Γ ⊢[PRAAx] App A s p) (hr : Γ ⊢[PRAAx] App R s t) : Γ ⊢[PRAAx] App A t p := by
  have h₂ := Prf.allE t (Prf.allE s h)
  simp only [Fm.subst_imp, Fm.subst_and, subst_App, Syn.subst_var, Syn.up_zero, up_one, shift_var,
    Fin.succ_zero_eq_one, subst_up_shift, Syn.subst_inst_shift, Syn.inst_zero] at h₂
  exact .impE h₂ (.andI hs hr)

theorem mono_elim {R S : Fm PTm 2} {f : PTm 1} (h : Γ ⊢[PRAAx] Mono R S f) {s t : PTm m}
    (hr : Γ ⊢[PRAAx] App R s t) : Γ ⊢[PRAAx] App S (inst1 f s) (inst1 f t) := by
  have h₂ := Prf.allE t (Prf.allE s h)
  simp only [Fm.subst_imp, subst_App, subst_inst1, Syn.subst_var, Syn.up_zero, up_one, shift_var,
    Fin.succ_zero_eq_one, subst_up_shift, Syn.subst_inst_shift, Syn.inst_zero] at h₂
  exact .impE h₂ hr

/-! ## Carrying hypotheses under binders -/

theorem lift {φ : Fm PTm m} {φ' : Fm PTm (m + 1)} (e : φ.shift = φ') (h : Γ ⊢[PRAAx] φ) :
    Γ.map Fm.shift ⊢[PRAAx] φ' := e ▸ h.shift

theorem shift_Up (R A : Fm PTm 2) (p : PTm m) : (Up R A p).shift = Up R A (Syn.shift p) :=
  subst_Up R A _ p

/-- Introduction of `Up`. -/
theorem up_intro {R A : Fm PTm 2} {p : PTm m}
    (h : ((App A (var 1) (Syn.shift (Syn.shift p)) ⋏ App R (var 1) (var 0)) ::
      (Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx] App A (var 0) (Syn.shift (Syn.shift p))) :
    Γ ⊢[PRAAx] Up R A p := .allI (.allI (.impI h))

/-! ## The upward-closed sets form a topology -/

/-- The empty set. -/
theorem up_bot (R : Fm PTm 2) (p : PTm m) : Γ ⊢[PRAAx] Up R Fm.bot p :=
  up_intro (Prf.andE₁ Prf.hyp0)

/-- The whole space, as `{x : x = x}`. -/
theorem up_univ (R : Fm PTm 2) (p : PTm m) : Γ ⊢[PRAAx] Up R (var 0 ≐ var 0) p :=
  up_intro (.eqRefl _)

theorem up_inter {R A B : Fm PTm 2} {p : PTm m} (hA : Γ ⊢[PRAAx] Up R A p) (hB : Γ ⊢[PRAAx] Up R B p) :
    Γ ⊢[PRAAx] Up R (A ⋏ B) p := by
  have hA' := lift (shift_Up R A _) (lift (shift_Up R A p) hA)
  have hB' := lift (shift_Up R B _) (lift (shift_Up R B p) hB)
  refine up_intro ?_
  have hyp : ((App (A ⋏ B) (var 1) (Syn.shift (Syn.shift p)) ⋏ App R (var 1) (var 0)) ::
      (Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx]
      (App A (var 1) (Syn.shift (Syn.shift p)) ⋏ App B (var 1) (Syn.shift (Syn.shift p))) ⋏
        App R (var 1) (var 0) := Prf.hyp0
  exact .andI (up_elim hA'.wk (Prf.andE₁ (Prf.andE₁ hyp)) (Prf.andE₂ hyp))
    (up_elim hB'.wk (Prf.andE₂ (Prf.andE₁ hyp)) (Prf.andE₂ hyp))

theorem up_union {R A B : Fm PTm 2} {p : PTm m} (hA : Γ ⊢[PRAAx] Up R A p) (hB : Γ ⊢[PRAAx] Up R B p) :
    Γ ⊢[PRAAx] Up R (A ⋎ B) p := by
  have hA' := lift (shift_Up R A _) (lift (shift_Up R A p) hA)
  have hB' := lift (shift_Up R B _) (lift (shift_Up R B p) hB)
  refine up_intro ?_
  have hyp : ((App (A ⋎ B) (var 1) (Syn.shift (Syn.shift p)) ⋏ App R (var 1) (var 0)) ::
      (Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx]
      (App A (var 1) (Syn.shift (Syn.shift p)) ⋎ App B (var 1) (Syn.shift (Syn.shift p))) ⋏
        App R (var 1) (var 0) := Prf.hyp0
  refine .orE (Prf.andE₁ hyp) ?_ ?_
  · exact .orI₁ (up_elim hA'.wk.wk Prf.hyp0 (Prf.andE₂ hyp).wk)
  · exact .orI₂ (up_elim hB'.wk.wk Prf.hyp0 (Prf.andE₂ hyp).wk)

/-! ## Minimal neighbourhoods -/

/-- `U_x = {y : R(x, y)}`, as a set with the parameter `x`. -/
abbrev nbhd (R : Fm PTm 2) : Fm PTm 2 := R.subst ![var 1, var 0]

theorem App_nbhd (R : Fm PTm 2) (t p : PTm m) : App (nbhd R) t p = App R p t := by
  simp only [App, nbhd, Fm.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-- For a transitive relation, `U_x` is upward closed. -/
theorem nbhd_up {R : Fm PTm 2} (htrans : Γ ⊢[PRAAx] Trans R) (x : PTm m) : Γ ⊢[PRAAx] Up R (nbhd R) x := by
  have ht := lift (subst_Trans R _) (lift (subst_Trans R _) htrans)
  refine up_intro ?_
  simp only [App_nbhd]
  exact trans_elim ht.wk (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)

/-- For a reflexive relation, `x ∈ U_x`. -/
theorem nbhd_self {R : Fm PTm 2} (hrefl : Γ ⊢[PRAAx] Refl R) (x : PTm m) :
    Γ ⊢[PRAAx] App (nbhd R) x x := by
  rw [App_nbhd]; exact refl_elim hrefl x

/-- `U_x` is the least open set containing `x`: an upward-closed `A` with `x ∈ A` contains every
`y ∈ U_x`. -/
theorem nbhd_least {R A : Fm PTm 2} {p x y : PTm m} (hA : Γ ⊢[PRAAx] Up R A p)
    (hx : Γ ⊢[PRAAx] App A x p) (hy : Γ ⊢[PRAAx] App (nbhd R) y x) : Γ ⊢[PRAAx] App A y p := by
  rw [App_nbhd] at hy; exact up_elim hA hx hy

/-- `T₀`: for an antisymmetric relation, `y ∈ U_x` and `x ∈ U_y` give `x = y`. -/
theorem t0_of_antisym {R : Fm PTm 2} (hanti : Γ ⊢[PRAAx] Antisym R) {x y : PTm m}
    (h₁ : Γ ⊢[PRAAx] App (nbhd R) y x) (h₂ : Γ ⊢[PRAAx] App (nbhd R) x y) : Γ ⊢[PRAAx] x ≐ y := by
  rw [App_nbhd] at h₁ h₂; exact antisym_elim hanti h₁ h₂

/-! ## Continuity -/

/-- The preimage `{x : V(f x, p)}`. -/
abbrev pre (f : PTm 1) (V : Fm PTm 2) : Fm PTm 2 := V.subst ![inst1 f (var 0), var 1]

theorem App_pre (f : PTm 1) (V : Fm PTm 2) (t p : PTm m) :
    App (pre f V) t p = App V (inst1 f t) p := by
  simp only [App, pre, Fm.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-- A monotone map is continuous: preimages of upward-closed sets are upward closed. -/
theorem preimage_up {R S V : Fm PTm 2} {f : PTm 1} {p : PTm m} (hmono : Γ ⊢[PRAAx] Mono R S f)
    (hV : Γ ⊢[PRAAx] Up S V p) : Γ ⊢[PRAAx] Up R (pre f V) p := by
  have hm := lift (subst_Mono R S f _) (lift (subst_Mono R S f _) hmono)
  have hV' := lift (shift_Up S V _) (lift (shift_Up S V p) hV)
  refine up_intro ?_
  simp only [App_pre]
  exact up_elim hV'.wk (Prf.andE₁ Prf.hyp0) (mono_elim hm.wk (Prf.andE₂ Prf.hyp0))

/-- Continuity at the minimal neighbourhoods: the preimage of every `U_{f(x)}` is upward closed. -/
def Cont {m : ℕ} (R S : Fm PTm 2) (f : PTm 1) : Fm PTm m :=
  Fm.all (Up R (pre f (nbhd S)) (inst1 f (var 0)))

theorem subst_Cont (R S : Fm PTm 2) (f : PTm 1) {k : ℕ} (σ : Fin m → PTm k) :
    (Cont R S f : Fm PTm m).subst σ = Cont R S f := by
  simp only [Cont, Fm.subst_all, subst_Up, subst_inst1, Syn.subst_var, Syn.up_zero]

theorem cont_elim {R S : Fm PTm 2} {f : PTm 1} (h : Γ ⊢[PRAAx] Cont R S f) (s : PTm m) :
    Γ ⊢[PRAAx] Up R (pre f (nbhd S)) (inst1 f s) := by
  have h₁ := Prf.allE s h
  simpa only [subst_Up, subst_inst1, Syn.subst_var, Syn.inst_zero] using h₁

/-- A continuous map between preordered spaces is monotone. -/
theorem mono_of_continuous {R S : Fm PTm 2} {f : PTm 1} (hrefl : Γ ⊢[PRAAx] Refl S)
    (hcont : Γ ⊢[PRAAx] Cont R S f) : Γ ⊢[PRAAx] Mono R S f := by
  have hr := lift (subst_Refl S _) (lift (subst_Refl S _) hrefl)
  have hc := lift (subst_Cont R S f _) (lift (subst_Cont R S f _) hcont)
  refine .allI (.allI (.impI ?_))
  have hu := cont_elim hc (var 1)
  have hs := refl_elim hr (inst1 f (var 1))
  have hs' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] App (pre f (nbhd S)) (var 1) (inst1 f (var 1)) := by
    rw [App_pre, App_nbhd]; exact hs
  have key : (App R (var 1) (var 0) :: (Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx]
      App (pre f (nbhd S)) (var 0) (inst1 f (var 1)) := up_elim hu.wk hs'.wk Prf.hyp0
  rw [App_pre, App_nbhd] at key
  exact key

end LeanProofs.IPRA.Topology.FinitePreorder
