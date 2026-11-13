import ConciseIPRA.NativeReplacementCalculi

/-!
# Backward replacement at sources other than the literal `0`

`BRep⁻` is backward replacement with the side condition `s ≢ 0` on the source,
the term it inserts: from `s = t` and `Rep_t^s(u) = r` infer `r = u`.  Three
calculi of the article use it in place of `BRep`:

* `BmPrf` (`B⁻`): the kernel with transport replaced by `BRep⁻`;
* `Bm7Prf` (`B⁻₇`): the single introduction with `BRep⁻`;
* `AmPrf`: `A₇` (elimination by abstraction) with `BRep⁻`, the open question
  `kern:q:aqeminus`.

All three are equivalent to the kernel (`bmprf_iff_nprf`, `bm7prf_iff_nprf`,
`amprf_iff_nprf`).  The equality rules and transport are derived once,
generically over the class `BMKernel` (`kern:lem:bmeq`, `kern:lem:bzero`),
whose only elimination of a closure is elimination by abstraction (`aqE`).
`QE` gives it at once (`NFm.aqE_of_qE`), and the bootstrap needs it only at
two instances whose abstraction is the matrix itself:

* `I(p, p; v.p) = p` is `aqE` at the term `p`: the abstraction of `p` is
  `I(y, y; v.y) = y`, whose closure is a computation step, and its instance at
  `0` is a computation (`BMKernel.iterSelf`);
* in the name for zero, `D_{x,y} (I(y, 0; v.x) = I(y, 0; v.0))`, the instance
  at `y = S 0` is `aqE` at the term `S 0` (`BMKernel.congZero`).

The introductions are needed only at the witness `0` with the assumption
unused (`BMKernel.dI0`, which gives `QI` with the assumption unused).  For
`AmPrf` the recovery of `QE` and of the kernel's introductions is the generic
one of `AKernel`; for `Bm7Prf` it is that of `WKernel`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m k : ℕ}

/-! ### Replacement of the literal `0` -/

namespace Tm

theorem iter_ne_zero (c a : Tm n) (h : Tm (n + 1)) : iter c a h ≠ zero := by
  intro e; cases e

theorem var_ne_zero (i : Fin n) : (Syn.var i : Tm n) ≠ zero := by
  intro e; cases e

theorem shift_ne_zero {t : Tm n} (ht : t ≠ zero) : Syn.shift t ≠ zero := by
  cases t with
  | zero => exact absurd rfl ht
  | _ => intro e; cases e

open Classical in
theorem rpl_var' (t : Tm n) (v : Tm m) (σ : Fin n → Tm m) (i : Fin n) :
    rpl t v σ (Syn.var i) = if Tm.var i = t then v else σ i := by
  show rpl t v σ (Tm.var i) = _
  simp only [rpl]

theorem rpl_zero_var (v : Tm m) (σ : Fin n → Tm m) (i : Fin n) :
    rpl zero v σ (Syn.var i) = σ i := by
  show rpl zero v σ (Tm.var i) = σ i
  simp [rpl]

/-- Replacement of `0` commutes with weakening. -/
theorem rpl_zero_shift (x : Tm m) (v : Tm k) (ρ : Fin m → Tm k) :
    rpl zero (Syn.shift v) (Syn.up ρ) (Syn.shift x) = Syn.shift (rpl zero v ρ x) := by
  have e₁ : Syn.shift (rpl zero v ρ x) = rpl zero (Syn.shift v) (fun i => Syn.shift (ρ i)) x :=
    rpl_comp x zero v ρ _
  have e₂ : rpl zero (Syn.shift v) (Syn.up ρ) (Syn.shift x)
      = rpl zero (Syn.shift v) (fun i => Syn.up ρ i.succ) x := by
    rw [shift_eq_ren x]; exact rpl_ren x (Fin.succ_injective _) zero _ _
  rw [e₂, e₁]; simp only [Syn.up_succ]

/-- Two instances of a term whose substituted terms agree after the
replacement of `0` agree after the replacement of `0`: every leaf `0` is a
leaf of the term or of a substituted term. -/
theorem rpl_zero_subst (h : Tm k) : ∀ {n m : ℕ} (v : Tm m) (ρ : Fin n → Tm m)
    (σ₁ σ₂ : Fin k → Tm n), (∀ j, rpl zero v ρ (σ₁ j) = rpl zero v ρ (σ₂ j)) →
    rpl zero v ρ (Syn.subst σ₁ h) = rpl zero v ρ (Syn.subst σ₂ h) := by
  induction h with
  | var i => intro n m v ρ σ₁ σ₂ hσ; simpa using hσ i
  | zero => intro n m v ρ σ₁ σ₂ _; rfl
  | succ a ih =>
    intro n m v ρ σ₁ σ₂ hσ
    simp only [Tm.subst_succ, rpl, reduceCtorEq, if_false, ih v ρ σ₁ σ₂ hσ]
  | iter c a b ihc iha ihb =>
    intro n m v ρ σ₁ σ₂ hσ
    have hb := ihb (Syn.shift v) (Syn.up ρ) (Syn.up σ₁) (Syn.up σ₂) fun j => by
      refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · simp only [Syn.up_succ, rpl_zero_shift, hσ i]
    simp only [Tm.subst_iter, rpl, reduceCtorEq, if_false, ihc v ρ σ₁ σ₂ hσ,
      iha v ρ σ₁ σ₂ hσ, Tm.shift_zero, hb]

/-- The instance at a weakened term of the weakened template. -/
theorem subst_inst_shift_up (h : Tm (n + 1)) (t : Tm n) :
    Syn.subst (inst (Syn.shift t)) (Syn.subst (up fun i => Syn.var i.succ) h)
      = Syn.shift (Syn.subst (inst t) h) := by
  rw [Syn.subst_subst, Syn.shift_subst]
  congr 1; funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

end Tm

/-! ### The bootstrap of backward replacement at nonzero sources -/

/-- The rules used by the bootstrap of `BRep⁻` (`kern:lem:bmeq`,
`kern:lem:bzero`): computation, `BRep⁻`, elimination by abstraction, `DE`,
introduction at the witness `0` with the assumption unused, and the structural
rules. -/
class BMKernel (P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop) : Prop where
  hyp : ∀ {n : ℕ} {Γ : List (NFm n)} {A : NFm n}, A ∈ Γ → P Γ A
  iterZero : ∀ {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter zero a h) a)
  iterSucc : ∀ {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  bRep : ∀ {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n}, s ≠ zero → P Γ (.eq s t) →
    P Γ (.eq (Tm.rpl t s Syn.var u) r) → P Γ (.eq r u)
  aqE : ∀ {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (t : Tm n), P Γ (.Q (NFm.abs t A)) →
    P Γ (NFm.rep t zero A) → P Γ A
  dE : ∀ {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}, P Γ (.D B) →
    P (.Q B :: Γ.map NFm.shift) A.shift → P Γ A
  dI0 : ∀ {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)),
    P (Γ.map NFm.shift) ((B.subst (up (inst zero))).subst (repl (succ (Syn.var 0)))) →
    P Γ (.D B)
  weaken : ∀ {n : ℕ} {Γ Δ : List (NFm n)} {A : NFm n}, P Γ A → Γ ⊆ Δ → P Δ A
  shift : ∀ {n : ℕ} {Γ : List (NFm n)} {A : NFm n}, P Γ A → P (Γ.map NFm.shift) A.shift

namespace BMKernel

variable {P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop} [BMKernel @P] {Γ : List (NFm n)}

theorem hyp0 {A : NFm n} : P (A :: Γ) A := hyp List.mem_cons_self

theorem wk {A B : NFm n} (h : P Γ A) : P (B :: Γ) A := weaken h (List.subset_cons_self _ _)

/-- `QI` with the assumption unused, by the introduction at the witness `0` of
the closure with a dummy first variable. -/
theorem qI (B : NFm (n + 1)) (h : P (Γ.map NFm.shift) (B.subst (repl (succ (Syn.var 0))))) :
    P Γ (.Q B) := by
  have hD : P Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine dI0 _ ?_
    rw [NFm.subst_dummy_inst]
    exact h
  exact dE hD hyp0

/-- (i) Joining at a source other than `0`. -/
theorem jn {s t r : Tm n} (hs : s ≠ zero) (h₁ : P Γ (.eq s t)) (h₂ : P Γ (.eq s r)) :
    P Γ (.eq r t) :=
  bRep hs h₁ (by rwa [Tm.rpl_root])

/-- (i) Reflexivity, at the source `J(a) = I(0, a; u.0)`. -/
theorem eqRefl (a : Tm n) : P Γ (.eq a a) :=
  jn (Tm.iter_ne_zero _ _ _) (iterZero a zero) (iterZero a zero)

/-- (ii) Symmetry, at the source `J(M)` of a numeral `M` larger than the
equation's left side, which therefore is unchanged by the replacement. -/
theorem eqSymm {u r : Tm n} (h : P Γ (.eq u r)) : P Γ (.eq r u) := by
  refine bRep (s := iter zero (Tm.big (Tm.sz u)) zero) (t := Tm.big (Tm.sz u))
    (Tm.iter_ne_zero _ _ _) (iterZero _ zero) ?_
  rwa [Tm.rpl_var_eq_rep, Tm.rep_small u _ _ (by rw [Tm.sz_big]; omega)]

/-- (iii) `I(p, p; v.p) = p`, by elimination by abstraction at the term `p`:
the abstraction is `I(y, y; v.y) = y`, whose step is a computation. -/
theorem iterSelf (p : Tm n) : P Γ (.eq (iter p p (Syn.shift p)) p) := by
  have hne : iter p p (Syn.shift p) ≠ p :=
    (Tm.ne_of_sz_lt (by simp only [Tm.sz]; omega)).symm
  have hab : NFm.abs p (.eq (iter p p (Syn.shift p)) p)
      = .eq (iter (Syn.var 0) (Syn.var 0) (Syn.shift (Syn.var 0))) (Syn.var 0) := by
    simp only [NFm.abs, NFm.rpl, Tm.rpl, if_neg hne, Tm.rpl_root]
  refine aqE p ?_ ?_
  · rw [hab]; refine qI _ ?_
    simpa [Syn.subst_shift] using iterSucc (P := @P) (Γ := Γ.map NFm.shift) (Syn.var 0)
      (succ (Syn.var 0)) (Syn.shift (succ (Syn.var 0)))
  · rw [← NFm.abs_inst, hab]
    simpa [Syn.subst_shift] using iterZero (P := @P) (Γ := Γ) zero zero

/-- (iv) From `p = 0` the equation `c = p`, with `c = I(0, 0; u.0)`. -/
theorem cOfZero {p : Tm n} (h : P Γ (.eq p zero)) : P Γ (.eq (iter zero zero zero) p) := by
  by_cases hp : p = zero
  · subst hp; exact iterZero zero zero
  · refine eqSymm (bRep hp h ?_)
    have e : Tm.rpl zero p Syn.var (iter zero zero zero) = iter p p (Syn.shift p) := by
      simp [Tm.rpl]
    rw [e]; exact iterSelf p

/-- (v) Joining without restriction. -/
theorem join {s t r : Tm n} (h₁ : P Γ (.eq s t)) (h₂ : P Γ (.eq s r)) : P Γ (.eq r t) := by
  by_cases hs : s = zero
  · subst hs
    exact jn (Tm.iter_ne_zero _ _ _) (cOfZero (eqSymm h₁)) (cOfZero (eqSymm h₂))
  · exact jn hs h₁ h₂

theorem eqTrans {a b e : Tm n} (h₁ : P Γ (.eq a b)) (h₂ : P Γ (.eq b e)) : P Γ (.eq a e) :=
  join h₂ (eqSymm h₁)

/-- (vi) Congruence by the marker, when neither side is `0`. -/
theorem congNZ (h : Tm (n + 1)) {s t : Tm n} (hs : s ≠ zero) (ht : t ≠ zero)
    (e : P Γ (.eq s t)) : P Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) := by
  have hK : P Γ (.eq (Tm.marker h s) s) := iterZero s _
  have k₁ : P Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst (Tm.marker h s)) h)) :=
    bRep hs (eqSymm hK) (by rw [Tm.rpl_marker]; exact eqRefl _)
  have k₂ : P Γ (.eq (Syn.subst (inst t) h) (Syn.subst (inst (Tm.marker h s)) h)) :=
    bRep ht (eqSymm (eqTrans hK e)) (by rw [Tm.rpl_marker]; exact eqRefl _)
  exact eqTrans k₁ (eqSymm k₂)

/-- A variable equal to `0`: both instances become `L = Rep_0^b(h(0))`. -/
theorem varZero (h : Tm (n + 1)) (i : Fin n) (e : P Γ (.eq (Syn.var i) zero)) :
    P Γ (.eq (Syn.subst (inst zero) h) (Syn.subst (inst (Syn.var i)) h)) := by
  have hL : Tm.rpl zero (Syn.var i) Syn.var (Syn.subst (inst (Syn.var i)) h)
      = Tm.rpl zero (Syn.var i) Syn.var (Syn.subst (inst zero) h) :=
    Tm.rpl_zero_subst h _ _ _ _ fun j => by
      refine Fin.cases ?_ (fun l => ?_) j <;> simp [Tm.rpl, Tm.rpl_zero_var]
  have k₁ : P Γ (.eq (Tm.rpl zero (Syn.var i) Syn.var (Syn.subst (inst zero) h))
      (Syn.subst (inst zero) h)) := bRep (Tm.var_ne_zero i) e (eqRefl _)
  have k₂ : P Γ (.eq (Tm.rpl zero (Syn.var i) Syn.var (Syn.subst (inst zero) h))
      (Syn.subst (inst (Syn.var i)) h)) :=
    bRep (Tm.var_ne_zero i) e (by rw [hL]; exact eqRefl _)
  exact eqTrans (eqSymm k₁) k₂

/-- The name for zero, `E(x, y) := I(y, 0; v.x) = I(y, 0; v.0)`. -/
def zname : NFm (n + 2) :=
  .eq (iter (Syn.var 0) zero (Syn.var (Fin.succ (Fin.succ 0)))) (iter (Syn.var 0) zero zero)

/-- Congruence at a zero endpoint (`kern:lem:bzero`). -/
theorem congZero (h : Tm (n + 1)) {t : Tm n} (e : P Γ (.eq zero t)) :
    P Γ (.eq (Syn.subst (inst zero) h) (Syn.subst (inst t) h)) := by
  by_cases ht : t = zero
  · subst ht; exact eqRefl _
  have hD : P Γ (.D (zname (n := n))) :=
    dI0 _ (eqRefl (P := @P) (Γ := Γ.map NFm.shift) (iter (succ (Syn.var 0)) zero zero))
  refine dE hD ?_
  -- over `Δ = Q_y E(b, y), Γ` with the eigenvariable `b = 0`
  have hQ : P (.Q zname :: Γ.map NFm.shift) (.Q zname) := hyp0
  have hE0 : P (.Q zname :: Γ.map NFm.shift) ((zname (n := n)).subst (inst zero)) := by
    have k := eqTrans (iterZero (P := @P) (Γ := .Q zname :: Γ.map NFm.shift) zero
      (Syn.var (Fin.succ 0))) (eqSymm (iterZero zero zero))
    exact k
  have habs : NFm.abs (succ zero) ((zname (n := n)).subst (inst (succ zero))) = zname := by
    have u2 : ∀ σ : Fin (n + 2) → Tm (n + 1), Syn.up σ 2 = Syn.shift (σ 1) := fun σ => by
      rw [← Fin.succ_one_eq_two]; exact Syn.up_succ σ 1
    simp [zname, NFm.abs, NFm.rpl, Tm.rpl, u2, Tm.rpl_var']
  have hE1 : P (.Q zname :: Γ.map NFm.shift) ((zname (n := n)).subst (inst (succ zero))) :=
    aqE (succ zero) (by rw [habs]; exact hQ) (by rw [← NFm.abs_inst, habs]; exact hE0)
  have hb : P (.Q zname :: Γ.map NFm.shift) (.eq (Syn.var 0) zero) := by
    have k₁ := iterSucc (P := @P) (Γ := .Q zname :: Γ.map NFm.shift) zero zero
      (Syn.var (Fin.succ 0))
    have k₂ := iterSucc (P := @P) (Γ := .Q zname :: Γ.map NFm.shift) zero zero zero
    simp only [Syn.subst_var, Syn.inst_succ, Tm.subst_zero] at k₁ k₂
    exact eqTrans (eqSymm k₁) (eqTrans (hE1 : P _ (.eq (iter (succ zero) zero (Syn.var (Fin.succ 0))) (iter (succ zero) zero zero))) k₂)
  have e' : P (.Q zname :: Γ.map NFm.shift) (.eq zero (Syn.shift t)) := wk (shift e)
  have k₁ := varZero (Syn.subst (up fun i => Syn.var i.succ) h) 0 hb
  have k₂ := congNZ (Syn.subst (up fun i => Syn.var i.succ) h) (Tm.var_ne_zero 0)
    (Tm.shift_ne_zero ht) (eqTrans hb e')
  have k := eqTrans k₁ k₂
  have z := Tm.subst_inst_shift_up h zero
  rw [Tm.shift_zero] at z
  rw [Tm.subst_inst_shift_up, z] at k
  exact k

/-- Congruence from `s = t` in every case. -/
theorem cong (h : Tm (n + 1)) {s t : Tm n} (e : P Γ (.eq s t)) :
    P Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) := by
  by_cases hs : s = zero
  · subst hs; exact congZero h e
  by_cases ht : t = zero
  · subst ht; exact eqSymm (congZero h (eqSymm e))
  exact congNZ h hs ht e

/-- Transport in an equation template. -/
theorem trEq (a b : Tm (n + 1)) {s t : Tm n} (e : P Γ (.eq s t))
    (h : P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    P Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  eqTrans (eqSymm (cong a e)) (eqTrans h (cong b e))

end BMKernel

/-- `A₇` with backward replacement at sources other than the literal `0`. -/
inductive AmPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : AmPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      AmPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      AmPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- `BRep⁻`: from `s = t`, `s ≢ 0`, and `Rep_t^s(u) = r` infer `r = u`. -/
  | bRep {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n} (hs : s ≠ zero)
      (h₁ : AmPrf Γ (.eq s t)) (h₂ : AmPrf Γ (.eq (Tm.rpl t s Syn.var u) r)) :
      AmPrf Γ (.eq r u)
  | aqE {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (t : Tm n) (h₁ : AmPrf Γ (.Q (NFm.abs t A)))
      (h₂ : AmPrf Γ (NFm.rep t zero A)) : AmPrf Γ A
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : AmPrf Γ (.D B)) (h₂ : AmPrf (.Q B :: Γ.map NFm.shift) A.shift) : AmPrf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : AmPrf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      AmPrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

/-! ### Soundness -/

theorem AmPrf.toAPrf (h : AmPrf Γ A) : APrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | bRep _ _ _ ih₁ ih₂ => exact .bRep ih₁ ih₂
  | aqE t _ _ ih₁ ih₂ => exact .aqE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

/-! ### Weakening and injective renaming -/

theorem Tm.subst_rn_ne_zero {s : Tm n} (hs : s ≠ zero) (ξ : Fin n → Fin m) :
    Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) s ≠ zero := by
  cases s <;> simp_all [Tm.subst_iter, Tm.subst_succ]

namespace AmPrf

theorem hyp0 : AmPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : AmPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → AmPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | bRep hs _ _ ih₁ ih₂ => intro Δ s; exact .bRep hs (ih₁ s) (ih₂ s)
  | aqE t _ _ ih₁ ih₂ => intro Δ s; exact .aqE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dI B t _ ih =>
    intro Δ s
    exact .dI B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : AmPrf Γ A) : AmPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

theorem ren (h : AmPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    AmPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ _; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ _; exact .iterZero _ _
  | iterSucc c a h =>
    intro m ξ _
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | bRep hs _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_eq, Tm.rpl_rn _ _ _ hξ] at h₂
    exact .bRep (Tm.subst_rn_ne_zero hs ξ) (ih₁ ξ hξ) h₂
  | aqE t _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₁ := ih₁ ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_Q, NFm.abs_rn _ _ hξ] at h₁
    rw [NFm.rep_rn _ _ _ hξ] at h₂
    exact .aqE _ h₁ h₂
  | dE _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h := ih₂ (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ hξ) h
  | @dI _ Γ B t _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ,
      NFm.subst_repl_up _ (NFm.start B t), NFm.subst_up_inst, ← NFm.start_rn] at h
    exact .dI _ _ h

theorem shift (h : AmPrf Γ A) : AmPrf (Γ.map NFm.shift) A.shift :=
  h.ren Fin.succ (Fin.succ_injective _)

end AmPrf

instance : BMKernel @AmPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun hs h₁ h₂ => .bRep hs h₁ h₂, fun t h₁ h₂ => .aqE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂,
    fun B h => .dI B zero h.wk, fun h s => h.weaken s, fun h => h.shift⟩

instance : AKernel @AmPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun a b => BMKernel.trEq a b, fun t h₁ h₂ => .aqE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂,
    fun B t h => .dI B t h, fun h s => h.weaken s, fun h => h.shift⟩

/-- **Elimination by abstraction with backward replacement at nonzero
sources**: `A₇` with `BRep⁻` and the kernel derive the same sequents. -/
theorem amprf_iff_nprf : AmPrf Γ A ↔ NPrf Γ A :=
  ⟨fun h => h.toAPrf.toNPrf, AKernel.ofNPrf⟩

/-! ### `B⁻` and `B⁻₇` -/

/-- `B⁻`: the kernel with transport replaced by `BRep⁻`. -/
inductive BmPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : BmPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      BmPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      BmPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | bRep {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n} (hs : s ≠ zero)
      (h₁ : BmPrf Γ (.eq s t)) (h₂ : BmPrf Γ (.eq (Tm.rpl t s Syn.var u) r)) :
      BmPrf Γ (.eq r u)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : BmPrf Γ (.Q B)) (h₂ : BmPrf Γ (B.subst (inst zero))) : BmPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : BmPrf Γ (.D B)) (h₂ : BmPrf (.Q B :: Γ.map NFm.shift) A.shift) : BmPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : BmPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      BmPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : BmPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      BmPrf Γ (.Q (.eq s₁ s₂))

/-- `B⁻₇`: the single introduction with `BRep⁻`. -/
inductive Bm7Prf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : Bm7Prf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      Bm7Prf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      Bm7Prf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | bRep {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n} (hs : s ≠ zero)
      (h₁ : Bm7Prf Γ (.eq s t)) (h₂ : Bm7Prf Γ (.eq (Tm.rpl t s Syn.var u) r)) :
      Bm7Prf Γ (.eq r u)
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : Bm7Prf Γ (.Q B)) (h₂ : Bm7Prf Γ (B.subst (inst zero))) :
      Bm7Prf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : Bm7Prf Γ (.D B)) (h₂ : Bm7Prf (.Q B :: Γ.map NFm.shift) A.shift) : Bm7Prf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : Bm7Prf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      Bm7Prf Γ (.D B)

/-- Elimination by abstraction from `QE`. -/
theorem NFm.aqE_of_qE {P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop}
    (qE : ∀ {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n), P Γ (.Q B) →
      P Γ (B.subst (inst zero)) → P Γ (B.subst (inst t)))
    {Γ : List (NFm n)} {A : NFm n} (t : Tm n) (h₁ : P Γ (.Q (NFm.abs t A)))
    (h₂ : P Γ (NFm.rep t zero A)) : P Γ A := by
  have h := qE t h₁ (by rwa [NFm.abs_inst])
  rwa [NFm.abs_inst_self] at h

namespace BmPrf

theorem weaken (h : BmPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → BmPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | bRep hs _ _ ih₁ ih₂ => intro Δ s; exact .bRep hs (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dICase B t _ ih =>
    intro Δ s; exact .dICase B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | qIInd s₁ s₂ _ ih =>
    intro Δ s; exact .qIInd s₁ s₂ (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem ren (h : BmPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    BmPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ _; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ _; exact .iterZero _ _
  | iterSucc c a h =>
    intro m ξ _
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | bRep hs _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_eq, Tm.rpl_rn _ _ _ hξ] at h₂
    exact .bRep (Tm.subst_rn_ne_zero hs ξ) (ih₁ ξ hξ) h₂
  | qE t _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ ξ hξ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h := ih₂ (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ hξ) h
  | dICase B t _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up, NFm.subst_inst,
      NFm.subst_repl_succ, NFm.subst_up_inst] at h
    exact .dICase _ _ h
  | qIInd s₁ s₂ _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ] at h
    exact .qIInd _ _ h

end BmPrf

namespace Bm7Prf

theorem weaken (h : Bm7Prf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → Bm7Prf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | bRep hs _ _ ih₁ ih₂ => intro Δ s; exact .bRep hs (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dI B t _ ih =>
    intro Δ s
    exact .dI B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem ren (h : Bm7Prf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    Bm7Prf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ _; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ _; exact .iterZero _ _
  | iterSucc c a h =>
    intro m ξ _
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | bRep hs _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_eq, Tm.rpl_rn _ _ _ hξ] at h₂
    exact .bRep (Tm.subst_rn_ne_zero hs ξ) (ih₁ ξ hξ) h₂
  | qE t _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ ξ hξ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h := ih₂ (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ hξ) h
  | @dI _ Γ B t _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ,
      NFm.subst_repl_up _ (NFm.start B t), NFm.subst_up_inst, ← NFm.start_rn] at h
    exact .dI _ _ h

end Bm7Prf

instance : BMKernel @BmPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun hs h₁ h₂ => .bRep hs h₁ h₂, NFm.aqE_of_qE fun t h₁ h₂ => .qE t h₁ h₂,
    fun h₁ h₂ => .dE h₁ h₂,
    fun B h => .dICase B zero (h.weaken (List.subset_cons_self _ _)),
    fun h s => h.weaken s, fun h => h.ren Fin.succ (Fin.succ_injective _)⟩

instance : BMKernel @Bm7Prf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun hs h₁ h₂ => .bRep hs h₁ h₂, NFm.aqE_of_qE fun t h₁ h₂ => .qE t h₁ h₂,
    fun h₁ h₂ => .dE h₁ h₂,
    fun B h => .dI B zero (h.weaken (List.subset_cons_self _ _)),
    fun h s => h.weaken s, fun h => h.ren Fin.succ (Fin.succ_injective _)⟩

instance : WKernel @Bm7Prf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun a b => BMKernel.trEq a b,
    fun t h₁ h₂ => .qE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂, fun B t h => .dI B t h⟩

/-- **`B⁻` and the kernel derive the same sequents** (`kern:thm:bminus`). -/
theorem bmprf_iff_nprf : BmPrf Γ A ↔ NPrf Γ A := by
  constructor
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | bRep _ _ _ ih₁ ih₂ => exact NPrf.bRep ih₁ ih₂
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dICase B t _ ih => exact .dICase B t ih
    | qIInd s t _ ih => exact .qIInd s t ih
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | trOne h _ _ ih₁ ih₂ => exact BMKernel.join (BMKernel.cong h ih₁) ih₂
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dICase B t _ ih => exact .dICase B t ih
    | qIInd s t _ ih => exact .qIInd s t ih

/-- **`B⁻₇` and the kernel derive the same sequents** (`kern:thm:bminus`). -/
theorem bm7prf_iff_nprf : Bm7Prf Γ A ↔ NPrf Γ A := by
  constructor
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | bRep _ _ _ ih₁ ih₂ => exact NPrf.bRep ih₁ ih₂
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dI B t _ ih => exact .ofDI B t ih
  · intro h
    induction h with
    | hyp h => exact .hyp h
    | iterZero a h => exact .iterZero a h
    | iterSucc c a h => exact .iterSucc c a h
    | trOne h _ _ ih₁ ih₂ => exact BMKernel.join (BMKernel.cong h ih₁) ih₂
    | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
    | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
    | dICase B t _ ih => exact WKernel.dICase B t ih
    | qIInd s t _ ih => exact WKernel.qInd s t ih

end LeanProofs.ConciseIPRA
