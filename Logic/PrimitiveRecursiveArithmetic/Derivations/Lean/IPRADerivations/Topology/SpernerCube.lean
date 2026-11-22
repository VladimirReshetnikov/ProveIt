import IPRADerivations.Topology.KuhnSimplices
import IPRADerivations.Core.ParityArith

/-!
# The cubical Sperner parity lemma in every dimension (`dimension_invariance_ipra`)

Packet: `topology/dimension_invariance_ipra`, `thm:sperner`: "For every admissible labeling, the
number of full Kuhn `d`-simplices is odd." With the grid `G_d(N) = {0, …, N}^d` as the packed lists
over the base `B = ⟨N, p⟩` (`Foundations/GridSums`; entry `q` from the top is coordinate `d − 1 − q`,
0-indexed as in the packet's executable convention) and a labelling term `L` in the point (it may
read `N` and the parameter `p` from the base), admissibility is the list of hypotheses

* `hRange`: `λ(v) ≤ d`;
* `hLow j`: coordinate `d − 1 − j` of `v` is `0` ⟹ `λ(v) ≤ d − 1 − j` (`eq:lower`);
* `hUp j`: coordinate `d − 1 − j` of `v` is `N` ⟹ `λ(v) ≠ d − 1 − j` (`eq:upper`),

each a single universal formula over the codes `v` of grid points: `v` equal to its canonical
repacking over `B` (`canon`) with entries `≤ N` (`bsum`), so junk codes are excluded and the
hypotheses say exactly that `λ` is admissible on `G_d(N)`. The full count is
`count d L B = Σ_{a ∈ [0, N)^d} Σ_π [the simplex (a, π) is full]`, the inner sum over the `d!`
permutations as a Lean-indexed sum (`Foundations/TermSums`).

* `sperner_parity`: for every `d` and `L`, the hypotheses derive `par (count d L B) = 1`, by
  induction on `d` in the metatheory. The step is the double count of the packet: the door count of
  each simplex (`KuhnSimplices.simplex_identity`); interior doors cancel in pairs (`vbit_swap`,
  `sum_even_of_invol`); the first and last facets telescope along `π_1`
  (`GridSums.grid_telescope`, `vbit_rot`); the faces vanish by `eq:upper` and `eq:lower`
  (`GridSumsContext.faceN_gen`, `face0_gen`), except the lower face of the last coordinate, which is
  the full count one dimension down for the restricted labelling `λ(·, 0)` (`vbit_rot_lift0_*`,
  `face_full`), whose admissibility follows (`hyps_face`);
* `sperner_cube`: the closed sentence `∀ N p. hyps ⟶ par (count) = 1` for every `d` and `L`.

The induction is on `d` in the metatheory, as in the packet ("the induction is genuinely
quantifier-free"): for each fixed `d` the theorem is one iPRA derivation.
-/


set_option autoImplicit false

namespace LeanProofs.IPRA.Topology.SpernerCube

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.GridSumsContext
open LeanProofs.IPRA.Foundations.TermSums
open LeanProofs.IPRA.Topology.KuhnSimplices
open Equiv

variable {n : ℕ}

/-! ## Shifting derivations into a summation level -/

theorem subst_up_shift' {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

theorem eq_lift {Γ : List (Fm PTm n)} {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) (ψ : Fm PTm (n + 1)) :
    (ψ :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift s ≐ Syn.shift t := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq] at e
  exact e.wk

theorem le_lift {Γ : List (Fm PTm n)} {s t : PTm n} (h : Γ ⊢[PRAAx] le s t) (ψ : Fm PTm (n + 1)) :
    (ψ :: Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift s) (Syn.shift t) := by
  have e := h.shift
  simp only [Fm.shift, subst_le] at e
  exact e.wk

theorem lt_lift {Γ : List (Fm PTm n)} {s t : PTm n} (h : Γ ⊢[PRAAx] lt s t) (ψ : Fm PTm (n + 1)) :
    (ψ :: Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift s) (Syn.shift t) := by
  have e := h.shift
  simp only [Fm.shift, subst_lt] at e
  exact e.wk

/-- Rewrite one side of a derived equation or inequality by an equation of terms, leaving the
context alone. -/
theorem eqL {Γ : List (Fm PTm n)} {s s' t : PTm n} (e : s = s') (h : Γ ⊢[PRAAx] s ≐ t) :
    Γ ⊢[PRAAx] s' ≐ t := by subst e; exact h

theorem eqR {Γ : List (Fm PTm n)} {s t t' : PTm n} (e : t = t') (h : Γ ⊢[PRAAx] s ≐ t) :
    Γ ⊢[PRAAx] s ≐ t' := by subst e; exact h

theorem leR {Γ : List (Fm PTm n)} {s t t' : PTm n} (e : t = t') (h : Γ ⊢[PRAAx] le s t) :
    Γ ⊢[PRAAx] le s t' := by subst e; exact h

theorem ltR {Γ : List (Fm PTm n)} {s t t' : PTm n} (e : t = t') (h : Γ ⊢[PRAAx] lt s t) :
    Γ ⊢[PRAAx] lt s t' := by subst e; exact h

theorem shift_fstT (t : PTm n) : Syn.shift (fstT t) = fstT (Syn.shift t) := by
  simp [Syn.shift]

theorem shift_tl (e : ℕ) (t : PTm n) : Syn.shift (tl e t) = tl e (Syn.shift t) := by
  simp [Syn.shift]

theorem shift_proj (q : ℕ) (t : PTm n) : Syn.shift (proj q t) = proj q (Syn.shift t) := by
  simp [Syn.shift]

/-- `eqb` is a congruence. -/
theorem congrEqb {Γ : List (Fm PTm n)} {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a')
    (h₂ : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx] eqb a b ≐ eqb a' b' :=
  congrMonus (.eqRefl _) (congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁))

/-- `eqb 0 1 = 0`. -/
theorem eqb_zero_one {Γ : List (Fm PTm n)} : Γ ⊢[PRAAx] eqb (zero : PTm n) one ≐ zero :=
  (congrMonus (.eqRefl _) ((congrAdd (zero_monus _) (monus_zero _)).eqTrans (zero_add _))).eqTrans
    (monus_self _)

/-! ## Colours and the Kuhn simplices -/

/-- The colour of the point `v`. -/
def col (L : PTm 1) (v : PTm n) : PTm n := Syn.subst ![v] L

@[simp] theorem subst_col {m : ℕ} (σ : Fin n → PTm m) (L : PTm 1) (v : PTm n) :
    Syn.subst σ (col L v) = col L (Syn.subst σ v) := by
  simp only [col, Syn.subst_subst]; congr 1; funext i; fin_cases i; rfl

theorem congrCol {Γ : List (Fm PTm n)} (L : PTm 1) {v v' : PTm n} (h : Γ ⊢[PRAAx] v ≐ v') :
    Γ ⊢[PRAAx] col L v ≐ col L v' := Foundations.GridSums.congr1 L h

/-- The labelling restricted to the lower face of the top entry: `λ'(y) = λ(⟨0, y⟩)`. -/
def restrict (L : PTm 1) : PTm 1 := Syn.subst ![pairT zero (Syn.var 0)] L

theorem col_restrict (L : PTm 1) (v : PTm n) : col (restrict L) v = col L (pairT zero v) := by
  simp only [col, restrict, Syn.subst_subst]; congr 1; funext i; fin_cases i; simp

variable (d : ℕ) (L : PTm 1)

/-- The colours of the vertices `v_0, …, v_d` of the simplex `(x, π)`. -/
def cols (π : Perm (Fin d)) (x : PTm n) : Fin (d + 1) → PTm n := fun t => col L (vert d π t.val x)

/-- `[the facet without v_t is a door]`. -/
def doorT (π : Perm (Fin d)) (t : Fin (d + 1)) (x : PTm n) : PTm n :=
  Syn.subst (fun s => cols d L π x (t.succAbove s)) (exactPat d)

/-- `[the simplex is full]`. -/
def fullT (π : Perm (Fin d)) (x : PTm n) : PTm n := Syn.subst (cols d L π x) (exactPat (d + 1))

@[simp] theorem subst_doorT {m : ℕ} (σ : Fin n → PTm m) (π : Perm (Fin d)) (t : Fin (d + 1))
    (x : PTm n) : Syn.subst σ (doorT d L π t x) = doorT d L π t (Syn.subst σ x) := by
  simp only [doorT, Syn.subst_subst]; congr 1; funext s; simp [cols]

@[simp] theorem subst_fullT {m : ℕ} (σ : Fin n → PTm m) (π : Perm (Fin d)) (x : PTm n) :
    Syn.subst σ (fullT d L π x) = fullT d L π (Syn.subst σ x) := by
  simp only [fullT, Syn.subst_subst]; congr 1; funext s; simp [cols]

theorem cell_eq (π : Perm (Fin d)) (x : PTm n) :
    Syn.subst (cols d L π x) (cellPat d) = fsum (d + 1) (fun t => doorT d L π t x) + fullT d L π x := by
  simp only [cellPat, PTm.subst_add, subst_fsum, subst_doorPat]; rfl

theorem even_eq (π : Perm (Fin d)) (x : PTm n) :
    Syn.subst (cols d L π x) (evenPat d) = two * Signum.sg (fsum (d + 1) (fun t => doorT d L π t x)) := by
  simp only [evenPat, PTm.subst_mul, PTm.subst_monus, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, subst_fsum, subst_doorPat]; rfl

/-- The full count: `Σ_{a ∈ [0, N)^d} Σ_π [(a, π) is full]` at the base `b = ⟨N, p⟩`. -/
noncomputable def fullS : PTm 1 := ftsum (fun π : Perm (Fin d) => fullT d L π (Syn.var 0))

noncomputable def count (b : PTm n) : PTm n := Syn.subst ![b] (gs 0 d (fullS d L))

/-! ## The admissibility hypotheses -/

/-- `v` is the code of a grid point over the base `b`: `v ≐ canon(v) ⟶ Σ (v_q ∸ N) = 0 ⟶ φ`. -/
def gridImp (v b : PTm n) (φ : Fm PTm n) : Fm PTm n :=
  (v ≐ canon d b v) ⟶ ((bsum d v b ≐ zero) ⟶ φ)

@[simp] theorem subst_gridImp {m : ℕ} (σ : Fin n → PTm m) (v b : PTm n) (φ : Fm PTm n) :
    (gridImp d v b φ).subst σ = gridImp d (Syn.subst σ v) (Syn.subst σ b) (φ.subst σ) := by
  simp [gridImp]

/-- `λ(v) ≤ d` at every grid point. -/
def hRange (b : PTm n) : Fm PTm n :=
  Fm.all (gridImp d (Syn.var 0) (Syn.shift b) (le (col L (Syn.var 0)) (num d)))

/-- `eq:lower` for coordinate `d − 1 − j`. -/
def hLow (j : ℕ) (b : PTm n) : Fm PTm n :=
  Fm.all (gridImp d (Syn.var 0) (Syn.shift b)
    ((proj j (Syn.var 0) ≐ zero) ⟶ le (col L (Syn.var 0)) (num (d - 1 - j))))

/-- `eq:upper` for coordinate `d − 1 − j`, as `[λ(v) = d − 1 − j] = 0`. -/
def hUp (j : ℕ) (b : PTm n) : Fm PTm n :=
  Fm.all (gridImp d (Syn.var 0) (Syn.shift b)
    ((proj j (Syn.var 0) ≐ fstT (Syn.shift b)) ⟶ (eqb (col L (Syn.var 0)) (num (d - 1 - j)) ≐ zero)))

@[simp] theorem subst_hRange {m : ℕ} (σ : Fin n → PTm m) (b : PTm n) :
    (hRange d L b).subst σ = hRange d L (Syn.subst σ b) := by
  simp [hRange, subst_up_shift', Syn.up]

@[simp] theorem subst_hLow {m : ℕ} (σ : Fin n → PTm m) (j : ℕ) (b : PTm n) :
    (hLow d L j b).subst σ = hLow d L j (Syn.subst σ b) := by
  simp [hLow, subst_up_shift', Syn.up]

@[simp] theorem subst_hUp {m : ℕ} (σ : Fin n → PTm m) (j : ℕ) (b : PTm n) :
    (hUp d L j b).subst σ = hUp d L j (Syn.subst σ b) := by
  simp [hUp, subst_up_shift', Syn.up]

/-- The hypotheses, in a context. -/
def Hyps {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m) : Prop :=
  (Δ ⊢[PRAAx] hRange d L b) ∧ (∀ j, j < d → (Δ ⊢[PRAAx] hLow d L j b)) ∧
    (∀ j, j < d → (Δ ⊢[PRAAx] hUp d L j b))

variable {d L}

theorem Hyps.lift {m : ℕ} {Δ : List (Fm PTm m)} {b : PTm m} (h : Hyps d L Δ b) (ψ : Fm PTm (m + 1)) :
    Hyps d L (ψ :: Δ.map Fm.shift) (Syn.shift b) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_⟩
  · have e := h₁.shift; simp only [Fm.shift, subst_hRange] at e; exact e.wk
  · have e := (h₂ j hj).shift; simp only [Fm.shift, subst_hLow] at e; exact e.wk
  · have e := (h₃ j hj).shift; simp only [Fm.shift, subst_hUp] at e; exact e.wk

section Elim

variable {Γ : List (Fm PTm n)} {b v : PTm n}

theorem range_at (h : Γ ⊢[PRAAx] hRange d L b) (h₁ : Γ ⊢[PRAAx] v ≐ canon d b v)
    (h₂ : Γ ⊢[PRAAx] bsum d v b ≐ zero) : Γ ⊢[PRAAx] le (col L v) (num d) := by
  have a := Prf.allE v h
  simp only [subst_gridImp, subst_le, subst_col, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    PTm.subst_num] at a
  exact .impE (.impE a h₁) h₂

theorem low_at {j : ℕ} (h : Γ ⊢[PRAAx] hLow d L j b) (h₁ : Γ ⊢[PRAAx] v ≐ canon d b v)
    (h₂ : Γ ⊢[PRAAx] bsum d v b ≐ zero) (h₃ : Γ ⊢[PRAAx] proj j v ≐ zero) :
    Γ ⊢[PRAAx] le (col L v) (num (d - 1 - j)) := by
  have a := Prf.allE v h
  simp only [subst_gridImp, Fm.subst_imp, Fm.subst_eq, subst_le, subst_col, subst_proj, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, PTm.subst_num, ConciseIPRA.PTm.subst_zero] at a
  exact .impE (.impE (.impE a h₁) h₂) h₃

theorem up_at {j : ℕ} (h : Γ ⊢[PRAAx] hUp d L j b) (h₁ : Γ ⊢[PRAAx] v ≐ canon d b v)
    (h₂ : Γ ⊢[PRAAx] bsum d v b ≐ zero) (h₃ : Γ ⊢[PRAAx] proj j v ≐ fstT b) :
    Γ ⊢[PRAAx] eqb (col L v) (num (d - 1 - j)) ≐ zero := by
  have a := Prf.allE v h
  simp only [subst_gridImp, Fm.subst_imp, Fm.subst_eq, subst_eqb, subst_col, subst_proj, subst_fstT,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, PTm.subst_num, ConciseIPRA.PTm.subst_zero] at a
  exact .impE (.impE (.impE a h₁) h₂) h₃

end Elim

/-! ## Facts carried into the grid sums -/

/-- The face value: `N` on an upper face, `0` on a lower face. -/
def fv {m : ℕ} : Bool → PTm m → PTm m
  | true, N => N
  | false, _ => zero

@[simp] theorem subst_fv {m k : ℕ} (σ : Fin m → PTm k) (top : Bool) (N : PTm m) :
    Syn.subst σ (fv top N) = fv top (Syn.subst σ N) := by
  cases top <;> simp [fv]

theorem shift_fv {m : ℕ} (top : Bool) (N : PTm m) : Syn.shift (fv top N) = fv top (Syn.shift N) := by
  cases top <;> simp [fv, Syn.shift]

/-- Entry information: on the full grid every summed entry is `< N`; on a face, the entry at
bottom depth `j` is fixed to the face value. -/
def EntryOK {m : ℕ} : Option (ℕ × Bool) → ℕ → List (Fm PTm m) → PTm m → PTm m → Prop
  | none, _, Δ, u, b => Δ ⊢[PRAAx] lt u (fstT b)
  | some (j, top), r, Δ, u, b =>
      if r = j then (Δ ⊢[PRAAx] u ≐ fv top (fstT b)) else (Δ ⊢[PRAAx] lt u (fstT b))

theorem EntryOK.lt' {m : ℕ} {z : Option (ℕ × Bool)} {r : ℕ} {Δ : List (Fm PTm m)} {u b : PTm m}
    (h : EntryOK z r Δ u b) (hz : ∀ top, z ≠ some (r, top)) : Δ ⊢[PRAAx] lt u (fstT b) := by
  match z, h with
  | none, h => exact h
  | some (j, top), h =>
    have hr : r ≠ j := fun e => hz top (by rw [e])
    simpa [EntryOK, hr] using h

theorem EntryOK.eq' {m : ℕ} {r : ℕ} {top : Bool} {Δ : List (Fm PTm m)} {u b : PTm m}
    (h : EntryOK (some (r, top)) r Δ u b) : Δ ⊢[PRAAx] u ≐ fv top (fstT b) := by
  simpa [EntryOK] using h

theorem EntryOK.lift {m : ℕ} {z : Option (ℕ × Bool)} {r : ℕ} {Δ : List (Fm PTm m)} {u b : PTm m}
    (h : EntryOK z r Δ u b) (ψ : Fm PTm (m + 1)) {u' : PTm (m + 1)}
    (hu : (ψ :: Δ.map Fm.shift) ⊢[PRAAx] u' ≐ Syn.shift u) :
    EntryOK z r (ψ :: Δ.map Fm.shift) u' (Syn.shift b) := by
  have hlt : (Δ ⊢[PRAAx] lt u (fstT b)) → ((ψ :: Δ.map Fm.shift) ⊢[PRAAx] lt u' (fstT (Syn.shift b))) :=
    fun h' => lt_congr hu.eqSymm (.eqRefl _) (ltR (shift_fstT b) (lt_lift h' ψ))
  match z, h with
  | none, h => exact hlt h
  | some (j, top), h =>
    by_cases hr : r = j
    · subst hr
      have e := eqR (by rw [shift_fv, shift_fstT]) (eq_lift (EntryOK.eq' h) ψ)
      simp only [EntryOK]
      exact hu.eqTrans e
    · simp only [EntryOK, if_neg hr] at h ⊢
      exact hlt h

variable (d L)

/-- The facts about a list `x` of depth `e`: the hypotheses at its base `b`, and its entries. -/
def Facts (z : Option (ℕ × Bool)) : ListFacts := fun e m Δ x =>
  ∃ b : PTm m, Hyps d L Δ b ∧ (Δ ⊢[PRAAx] tl e x ≐ b) ∧ ∀ q, q < e →
    (Δ ⊢[PRAAx] le (proj q x) (fstT b)) ∧ EntryOK z (e - 1 - q) Δ (proj q x) b

variable {d L}

/-- The facts are preserved by the summation levels outside the face. -/
theorem facts_steps (z : Option (ℕ × Bool)) (lo hi : ℕ)
    (hz : ∀ e, lo ≤ e → e < hi → ∀ top, z ≠ some (e, top)) : Steps (Facts d L z) lo hi := by
  intro e hlo hhi m Δ x ⟨b, hH, htl, hq⟩
  have htl' := eqL (shift_tl e x) (eq_lift htl (lt (Syn.var 0) (Syn.shift (fstT (tl e x)))))
  refine ⟨Syn.shift b, hH.lift _, (tl_pair_succ e _ _).eqTrans htl', fun q hq' => ?_⟩
  have hN : (lt (Syn.var 0) (Syn.shift (fstT (tl e x))) :: Δ.map Fm.shift) ⊢[PRAAx]
      Syn.shift (fstT (tl e x)) ≐ fstT (Syn.shift b) :=
    eqL (by rw [shift_fstT, shift_tl]) (congrFst htl')
  cases q with
  | zero =>
    have hlt : (lt (Syn.var 0) (Syn.shift (fstT (tl e x))) :: Δ.map Fm.shift) ⊢[PRAAx]
        lt (proj 0 (pairT (Syn.var 0) (Syn.shift x))) (fstT (Syn.shift b)) :=
      lt_congr (fst_pair _ _).eqSymm hN Prf.hyp0
    refine ⟨le_of_lt hlt, ?_⟩
    rw [show e + 1 - 1 - 0 = e by omega]
    match z, hz with
    | none, _ => exact hlt
    | some (j, top), hz =>
      have : e ≠ j := fun h => hz e hlo hhi top (by rw [h])
      simpa [EntryOK, this] using hlt
  | succ q =>
    obtain ⟨hle, hok⟩ := hq q (by omega)
    have hp : (lt (Syn.var 0) (Syn.shift (fstT (tl e x))) :: Δ.map Fm.shift) ⊢[PRAAx]
        proj (q + 1) (pairT (Syn.var 0) (Syn.shift x)) ≐ Syn.shift (proj q x) := by
      exact eqR (shift_proj q x).symm (proj_pair_succ q (Syn.var 0) (Syn.shift x))
    have hle' := leR (shift_fstT b) (le_lift hle (lt (Syn.var 0) (Syn.shift (fstT (tl e x)))))
    refine ⟨le_congr hp.eqSymm (.eqRefl _) hle', ?_⟩
    rw [show e + 1 - 1 - (q + 1) = e - 1 - q by omega]
    exact hok.lift _ hp

/-- The facts hold at the base of the grid. -/
theorem facts_base {m : ℕ} {Δ : List (Fm PTm m)} {b : PTm m} (z : Option (ℕ × Bool))
    (h : Hyps d L Δ b) : Facts d L z 0 m Δ b :=
  ⟨b, h, .eqRefl _, fun _ hq => absurd hq (Nat.not_lt_zero _)⟩

/-- The face step: the entry at depth `j` set to the face value. -/
theorem facts_face {m : ℕ} {Δ : List (Fm PTm m)} {x : PTm m} (j : ℕ) (top : Bool)
    (h : Facts d L (some (j, top)) j m Δ x) :
    Facts d L (some (j, top)) (j + 1) m Δ (pairT (fv top (fstT (tl j x))) x) := by
  obtain ⟨b, hH, htl, hq⟩ := h
  have hv : Δ ⊢[PRAAx] fv top (fstT (tl j x)) ≐ fv top (fstT b) := by
    cases top
    · exact .eqRefl _
    · exact congrFst htl
  refine ⟨b, hH, (tl_pair_succ j _ _).eqTrans htl, fun q hq' => ?_⟩
  cases q with
  | zero =>
    have e₀ := (fst_pair (Γ := Δ) (fv top (fstT (tl j x))) x).eqTrans hv
    have hle : Δ ⊢[PRAAx] le (proj 0 (pairT (fv top (fstT (tl j x))) x)) (fstT b) := by
      cases top
      · exact le_congr e₀.eqSymm (.eqRefl _) (zero_le _)
      · exact le_congr e₀.eqSymm (.eqRefl _) (le_refl _)
    refine ⟨hle, ?_⟩
    simp only [EntryOK, show j + 1 - 1 - 0 = j by omega]
    exact e₀
  | succ q =>
    obtain ⟨hle, hok⟩ := hq q (by omega)
    have hp := proj_pair_succ (Γ := Δ) q (fv top (fstT (tl j x))) x
    refine ⟨le_congr hp.eqSymm (.eqRefl _) hle, ?_⟩
    rw [show j + 1 - 1 - (q + 1) = j - 1 - q by omega]
    simp only [EntryOK] at hok ⊢
    split_ifs at hok ⊢ with h₁
    · exact hp.eqTrans hok
    · exact lt_congr hp.eqSymm (.eqRefl _) hok

/-! ## Vertices at full depth -/

/-- A vertex that increments only entries `< N` is a grid point. -/
theorem vertex_grid {z : Option (ℕ × Bool)} {m : ℕ} {Δ : List (Fm PTm m)} {y : PTm m}
    (h : Facts d L z d m Δ y) (bits : ℕ → Bool)
    (hb : ∀ q, q < d → bits q = true → ∀ top, z ≠ some (d - 1 - q, top)) :
    ∃ b, Hyps d L Δ b ∧ (Δ ⊢[PRAAx] incr d bits y ≐ canon d b (incr d bits y)) ∧
      (Δ ⊢[PRAAx] bsum d (incr d bits y) b ≐ zero) ∧
      (∀ q, q < d → EntryOK z (d - 1 - q) Δ (proj q y) b) := by
  obtain ⟨b, hH, htl, hq⟩ := h
  obtain ⟨h₁, h₂⟩ := incr_grid d bits y b htl (fun q h => (hq q h).1)
    (fun q h hbq => (hq q h).2.lt' (hb q h hbq))
  exact ⟨b, hH, h₁, h₂, fun q h => (hq q h).2⟩

/-! ## The door count of the simplices of the full grid -/

theorem cell_at {m : ℕ} {Δ : List (Fm PTm m)} {y : PTm m} (h : Facts d L none d m Δ y)
    (π : Perm (Fin d)) :
    Δ ⊢[PRAAx] fsum (d + 1) (fun t => doorT d L π t y) + fullT d L π y ≐
      two * Signum.sg (fsum (d + 1) (fun t => doorT d L π t y)) := by
  rw [← cell_eq, ← even_eq]
  refine simplex_identity d _ (fun s => ?_)
  obtain ⟨b, hH, h₁, h₂, _⟩ := vertex_grid h (vbit d π s.val) (fun _ _ _ _ h => nomatch h)
  exact range_at hH.1 h₁ h₂

/-! ## Colour facts on the faces -/

/-- `eqb a (num j₀) = 0` when `a ≤ i < j₀`. -/
theorem eqb_zero_of_le {Γ : List (Fm PTm n)} {a : PTm n} {i j₀ : ℕ} (h : Γ ⊢[PRAAx] le a (num i))
    (hij : i < j₀) : Γ ⊢[PRAAx] eqb a (num j₀) ≐ zero := by
  have e := Foundations.BoundedDecision.bounded_decide i (eqb (Syn.var 0 : PTm 1) (num j₀)) zero
    (fun ρ hρ => by have := hρ 0; simp; omega) ![a] (fun s => by fin_cases s; exact h)
  simpa using e

/-- A facet missing the colour `j₀` is not a door. -/
theorem exact_zero_of_missing {Γ : List (Fm PTm n)} {k : ℕ} (κ : Fin k → PTm n) (j₀ : Fin k)
    (h : ∀ s, Γ ⊢[PRAAx] eqb (κ s) (num j₀.val) ≐ zero) :
    Γ ⊢[PRAAx] Syn.subst κ (exactPat k) ≐ zero := by
  simp only [exactPat, subst_fprod, subst_eqb, subst_fsum, Syn.subst_var, PTm.subst_num,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  refine fprod_eq_zero j₀ ?_
  exact (congrEqb (fsum_eq_zero h) (.eqRefl _)).eqTrans eqb_zero_one

/-! ## The first facets: rule (2) -/

section Endpoint

variable {d' : ℕ}

theorem first_last {Γ : List (Fm PTm n)} (π : Perm (Fin (d' + 1))) (x : PTm n) :
    Γ ⊢[PRAAx] doorT (d' + 1) L π 0 x ≐
      doorT (d' + 1) L (rot π) (Fin.last (d' + 1)) (upd (π 0) x) := by
  refine Prf.eqCongr (exactPat (d' + 1)) (fun s => ?_)
  simp only [cols, Fin.succAbove_zero, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc, vert]
  refine congrCol L ?_
  have hs : s.val ≤ d' := by have := s.isLt; omega
  rw [vbit_rot π s.val]
  exact (incr_upd (d' + 1) _ (π 0) x (π 0).isLt (vbit_rot_self π s.val hs)).eqSymm

/-- The first facet of `(x, π)` is the last facet of `(x + e_{π_1}, rot π)`, inside the grid sum. -/
theorem first_last_gs {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m) (π : Perm (Fin (d' + 1))) :
    Δ ⊢[PRAAx] Syn.subst ![b] (gs 0 (d' + 1) (doorT (d' + 1) L π 0 (Syn.var 0))) ≐
      Syn.subst ![b] (gs 0 (d' + 1)
        (doorT (d' + 1) L (rot π) (Fin.last (d' + 1)) (upd (π 0) (Syn.var 0)))) := by
  refine gs_congr (fun m' Δ' y => ?_) 0 (d' + 1) m Δ b
  simp only [subst_doorT, subst_upd, Syn.subst_var, Matrix.cons_val_zero]
  exact first_last π y

end Endpoint

/-! ## The restricted labelling inherits admissibility -/

section Face

/-- The grid-point premises one dimension up, at `⟨0, v⟩`. -/
theorem grid_up {Δ : List (Fm PTm n)} {v b : PTm n} (h₁ : Δ ⊢[PRAAx] v ≐ canon d b v)
    (h₂ : Δ ⊢[PRAAx] bsum d v b ≐ zero) :
    (Δ ⊢[PRAAx] pairT zero v ≐ canon (d + 1) b (pairT zero v)) ∧
      (Δ ⊢[PRAAx] bsum (d + 1) (pairT zero v) b ≐ zero) := by
  refine ⟨?_, ?_⟩
  · simp only [canon]
    exact congrPairT (fst_pair _ _).eqSymm (h₁.eqTrans (congrCanon d b (snd_pair _ _).eqSymm))
  · apply of_mk
    have e₂ := Q.sound h₂
    simp only [bsum, mk_fsum, Q.mk_zero] at e₂ ⊢
    rw [Fin.sum_univ_succ]
    have e₀ : Q.mk Δ (monus (proj (0 : Fin (d + 1)).val (pairT zero v)) (fstT b)) = 0 := by
      rw [← Q.mk_zero]
      exact Q.sound ((congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans (zero_monus _))
    rw [e₀, _root_.zero_add, ← e₂]
    exact Finset.sum_congr rfl (fun q _ => Q.sound (congrMonus (proj_pair_succ q.val zero v) (.eqRefl _)))

theorem hyps_face {m : ℕ} {Δ : List (Fm PTm m)} {b : PTm m} (h : Hyps (d + 1) L Δ b) :
    Hyps d (restrict L) Δ b := by
  obtain ⟨_, hlow, hup⟩ := h
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_⟩
  · refine .allI (.impI (.impI ?_))
    have e := (hlow 0 (by omega)).shift
    simp only [Fm.shift, subst_hLow] at e
    have g := grid_up (d := d) (Δ := (bsum d (Syn.var 0) (Syn.shift b) ≐ zero) ::
      (Syn.var 0 ≐ canon d (Syn.shift b) (Syn.var 0)) :: Δ.map Fm.shift) Prf.hyp1 Prf.hyp0
    have r := low_at e.wk.wk g.1 g.2 (fst_pair _ _)
    rw [show d + 1 - 1 - 0 = d by omega] at r
    rw [col_restrict]
    exact r
  · refine .allI (.impI (.impI (.impI ?_)))
    have e := (hlow (j + 1) (by omega)).shift
    simp only [Fm.shift, subst_hLow] at e
    have g := grid_up (d := d) (Δ := (proj j (Syn.var 0) ≐ zero) ::
      (bsum d (Syn.var 0) (Syn.shift b) ≐ zero) ::
      (Syn.var 0 ≐ canon d (Syn.shift b) (Syn.var 0)) :: Δ.map Fm.shift) (.hyp (by simp)) Prf.hyp1
    have r := low_at e.wk.wk.wk g.1 g.2 ((proj_pair_succ j zero (Syn.var 0)).eqTrans Prf.hyp0)
    rw [show d + 1 - 1 - (j + 1) = d - 1 - j by omega] at r
    rw [col_restrict]
    exact r
  · refine .allI (.impI (.impI (.impI ?_)))
    have e := (hup (j + 1) (by omega)).shift
    simp only [Fm.shift, subst_hUp] at e
    have g := grid_up (d := d) (Δ := (proj j (Syn.var 0) ≐ fstT (Syn.shift b)) ::
      (bsum d (Syn.var 0) (Syn.shift b) ≐ zero) ::
      (Syn.var 0 ≐ canon d (Syn.shift b) (Syn.var 0)) :: Δ.map Fm.shift) (.hyp (by simp)) Prf.hyp1
    have r := up_at e.wk.wk.wk g.1 g.2 ((proj_pair_succ j zero (Syn.var 0)).eqTrans Prf.hyp0)
    rw [show d + 1 - 1 - (j + 1) = d - 1 - j by omega] at r
    rw [col_restrict]
    exact r

/-- On the lower face of the top entry the last facets of `rot (lift0 τ)` are the full simplices of
the restricted labelling one dimension down. -/
theorem face_full {Δ : List (Fm PTm n)} (τ : Perm (Fin d)) (x : PTm n) :
    Δ ⊢[PRAAx] doorT (d + 1) L (rot (lift0 τ)) (Fin.last (d + 1)) (pairT zero x) ≐
      fullT d (restrict L) τ x := by
  refine Prf.eqCongr (exactPat (d + 1)) (fun s => ?_)
  simp only [cols, Fin.succAbove_last, Fin.val_castSucc, vert, col_restrict]
  refine congrCol L ?_
  have hs : s.val ≤ d := by have := s.isLt; omega
  refine (incr_pair_zero d _ x (vbit_rot_lift0_zero τ s.val hs)).eqTrans ?_
  rw [vbit_rot_lift0_succ]
  all_goals exact .eqRefl _

end Face

/-! ## The induction step -/

/-- The summands of the telescoping along entry `c`: the last facets of `rot π` for `π_1 = c`. -/
noncomputable def Hc (d' : ℕ) (c : Fin (d' + 1)) : PTm 1 :=
  ftsum (fun π : Perm (Fin (d' + 1)) =>
    if π 0 = c then doorT (d' + 1) L (rot π) (Fin.last (d' + 1)) (Syn.var 0) else zero)

theorem subst_Hc {m : ℕ} (d' : ℕ) (c : Fin (d' + 1)) (y : PTm m) :
    Syn.subst ![y] (Hc (L := L) d' c) = ftsum (fun π : Perm (Fin (d' + 1)) =>
      if π 0 = c then doorT (d' + 1) L (rot π) (Fin.last (d' + 1)) y else zero) := by
  simp only [Hc, subst_ftsum]
  congr 1; funext π
  split_ifs <;> simp

/-- The value of a grid sum in the quotient semiring. -/
abbrev S {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m) (D : ℕ) (F : PTm 1) : Q Δ :=
  Q.mk Δ (Syn.subst ![b] (gs 0 D F))

theorem S_ite {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m) (D : ℕ) (p : Prop) [Decidable p] (F : PTm 1) :
    S Δ b D (if p then F else zero) = if p then S Δ b D F else 0 := by
  split_ifs
  · rfl
  · show Q.mk Δ (Syn.subst ![b] (gs 0 D zero)) = 0
    rw [Q.sound (gs_zero_term 0 D Δ b), Q.mk_zero]

/-- On a face of entry `c`, the last facets of `rot π` with `π_1 = c` are not doors, when every
grid point with entry `c` at the face value misses the colour `j₀`. -/
theorem face_door_zero {m : ℕ} {Δ : List (Fm PTm m)} {y b : PTm m} (c : Fin (d + 1)) (top : Bool)
    (htl : Δ ⊢[PRAAx] tl (d + 1) y ≐ b)
    (hq : ∀ q, q < d + 1 → (Δ ⊢[PRAAx] le (proj q y) (fstT b)) ∧
      EntryOK (some (d - c.val, top)) (d + 1 - 1 - q) Δ (proj q y) b)
    (j₀ : Fin (d + 1))
    (hcol : ∀ v : PTm m, (Δ ⊢[PRAAx] v ≐ canon (d + 1) b v) → (Δ ⊢[PRAAx] bsum (d + 1) v b ≐ zero) →
      (Δ ⊢[PRAAx] proj c.val v ≐ fv top (fstT b)) → (Δ ⊢[PRAAx] eqb (col L v) (num j₀.val) ≐ zero)) :
    Δ ⊢[PRAAx] Syn.subst ![y] (Hc (L := L) d c) ≐ zero := by
  rw [subst_Hc]
  refine (ftsum_congr (g := fun _ => zero) (fun π => ?_)).eqTrans (of_mk (by rw [mk_ftsum]; simp))
  split_ifs with hπ
  · refine exact_zero_of_missing _ j₀ (fun s => ?_)
    have hs : ((Fin.last (d + 1)).succAbove s).val ≤ d := by
      rw [Fin.succAbove_last]; simp only [Fin.val_castSucc]; have := s.isLt; omega
    have hbit : vbit (d + 1) (rot π) ((Fin.last (d + 1)).succAbove s).val c.val = false := by
      rw [← hπ]; exact vbit_rot_self π _ hs
    obtain ⟨h₁, h₂⟩ := incr_grid (d + 1) (vbit (d + 1) (rot π) ((Fin.last (d + 1)).succAbove s).val) y b
      htl (fun q hq' => (hq q hq').1)
      (fun q hq' hbq => (hq q hq').2.lt' (fun top' htop => by
        simp only [Option.some.injEq, Prod.mk.injEq] at htop
        obtain ⟨h1, -⟩ := htop
        have hqc : q = c.val := by omega
        rw [hqc, hbit] at hbq; exact Bool.false_ne_true hbq))
    have hc := (hq c.val c.isLt).2
    rw [show d + 1 - 1 - c.val = d - c.val by omega] at hc
    exact hcol _ h₁ h₂ ((proj_incr (d + 1) _ c.val y c.isLt).eqTrans (by rw [hbit]; exact hc.eq'))
  · exact .eqRefl _

/-- Rule (1): `π` and `π ∘ (t − 1, t)` share the facet without `v_t`. -/
theorem door_swap {m : ℕ} (π : Perm (Fin d)) (a a' : Fin d) (hab : a'.val = a.val + 1)
    (t : Fin (d + 1)) (ht : t.val = a'.val) (x : PTm m) :
    doorT d L (π * swap a a') t x = doorT d L π t x := by
  simp only [doorT, cols, vert]
  congr 1; funext s
  rw [vbit_swap π a a' hab _ (fun h => Fin.succAbove_ne t s (Fin.ext (by omega)))]

variable (d L) in
/-- The door occurrences opposite the vertex `t`, over the whole grid. -/
noncomputable def Dt {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m) (t : Fin (d + 1 + 1)) : Q Δ :=
  ∑ π : Perm (Fin (d + 1)), S Δ b (d + 1) (doorT (d + 1) L π t (Syn.var 0))

variable (d L) in
/-- The full simplices, over the whole grid. -/
noncomputable def Fu {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m) : Q Δ :=
  ∑ π : Perm (Fin (d + 1)), S Δ b (d + 1) (fullT (d + 1) L π (Syn.var 0))

variable (d L) in
/-- `Σ sg(doors)`, over the whole grid. -/
noncomputable def Ev {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m) : Q Δ :=
  ∑ π : Perm (Fin (d + 1)),
    S Δ b (d + 1) (Signum.sg (fsum (d + 1 + 1) (fun t => doorT (d + 1) L π t (Syn.var 0))))

variable (d L) in
/-- The double count: `par (count (d + 1)) = par (count d)` of the restricted labelling. -/
theorem step {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m) (h : Hyps (d + 1) L Δ b) :
    Δ ⊢[PRAAx] par (count (d + 1) L b) ≐ par (count d (restrict L) b) := by
  classical
  -- the door count of every simplex of the full grid
  have hcell : (∑ t, Dt d L Δ b t) + Fu d L Δ b = 2 * Ev d L Δ b := by
    have h₁ := gs_congr_gen (facts_steps (d := d + 1) (L := L) none 0 (d + 1) (fun _ _ _ _ h => nomatch h))
      (F := ftsum (fun π : Perm (Fin (d + 1)) =>
        fsum (d + 1 + 1) (fun t => doorT (d + 1) L π t (Syn.var 0)) + fullT (d + 1) L π (Syn.var 0)))
      (G := ftsum (fun π : Perm (Fin (d + 1)) =>
        two * Signum.sg (fsum (d + 1 + 1) (fun t => doorT (d + 1) L π t (Syn.var 0)))))
      (fun m' Δ' y hy => by
        simp only [subst_ftsum, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, ConciseIPRA.PTm.subst_succ,
          ConciseIPRA.PTm.subst_zero, subst_fsum, subst_doorT, subst_fullT, Syn.subst_var,
          Matrix.cons_val_zero]
        exact ftsum_congr (fun π => cell_at hy π))
      (d + 1) 0 (by omega) le_rfl m Δ b (facts_base none h)
    have e := Q.sound h₁
    rw [mk_gs_ftsum, mk_gs_ftsum] at e
    have e₁ : ∀ π : Perm (Fin (d + 1)), Q.mk Δ (Syn.subst ![b] (gs 0 (d + 1)
        (fsum (d + 1 + 1) (fun t => doorT (d + 1) L π t (Syn.var 0)) + fullT (d + 1) L π (Syn.var 0)))) =
        (∑ t, S Δ b (d + 1) (doorT (d + 1) L π t (Syn.var 0))) + S Δ b (d + 1) (fullT (d + 1) L π (Syn.var 0)) := by
      intro π; rw [Q.sound (gs_add _ _ 0 (d + 1) m Δ b), Q.mk_add, mk_gs_fsum]
    have e₂ : ∀ π : Perm (Fin (d + 1)), Q.mk Δ (Syn.subst ![b] (gs 0 (d + 1)
        (two * Signum.sg (fsum (d + 1 + 1) (fun t => doorT (d + 1) L π t (Syn.var 0)))))) =
        2 * S Δ b (d + 1) (Signum.sg (fsum (d + 1 + 1) (fun t => doorT (d + 1) L π t (Syn.var 0)))) :=
      fun π => mk_gs_two _ _ _ _ _
    rw [Finset.sum_congr rfl (fun π _ => e₁ π), Finset.sum_congr rfl (fun π _ => e₂ π),
      Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum] at e
    exact e
  -- interior facets cancel in pairs
  have hint : ∀ i : Fin d, ∃ X, Dt d L Δ b (Fin.castSucc i).succ = X + X := by
    intro i
    have ha : i.val < d + 1 := by omega
    have ha' : i.val + 1 < d + 1 := by omega
    refine sum_even_of_invol (fun π => S Δ b (d + 1) (doorT (d + 1) L π (Fin.castSucc i).succ (Syn.var 0)))
      (fun π => π * swap ⟨i.val, ha⟩ ⟨i.val + 1, ha'⟩) (fun π => by simp) ?_ ?_
    · intro π hπ
      have h' := congrArg (fun σ : Perm (Fin (d + 1)) => σ ⟨i.val, ha⟩) hπ
      simp only [Perm.mul_apply, swap_apply_left, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at h'
      omega
    · intro π
      exact congrArg (S Δ b (d + 1)) (door_swap π ⟨i.val, ha⟩ ⟨i.val + 1, ha'⟩ rfl (Fin.castSucc i).succ
        (by simp) (Syn.var 0))
  -- the first facets telescope along `π_1`
  have hfirst : Dt d L Δ b 0 =
      ∑ c : Fin (d + 1), S Δ b (d + 1) (comp (Hc (L := L) d c) (upd c.val (Syn.var 0))) := by
    have hHc : ∀ c : Fin (d + 1), comp (Hc (L := L) d c) (upd c.val (Syn.var 0)) =
        ftsum (fun π : Perm (Fin (d + 1)) =>
          if π 0 = c then doorT (d + 1) L (rot π) (Fin.last (d + 1)) (upd c.val (Syn.var 0)) else zero) :=
      fun c => subst_Hc d c _
    calc Dt d L Δ b 0 = ∑ π : Perm (Fin (d + 1)),
          S Δ b (d + 1) (doorT (d + 1) L (rot π) (Fin.last (d + 1)) (upd (π 0).val (Syn.var 0))) :=
          Finset.sum_congr rfl (fun π _ => Q.sound (first_last_gs Δ b π))
      _ = ∑ π : Perm (Fin (d + 1)), ∑ c : Fin (d + 1), if π 0 = c then
          S Δ b (d + 1) (doorT (d + 1) L (rot π) (Fin.last (d + 1)) (upd c.val (Syn.var 0))) else 0 := by
          refine Finset.sum_congr rfl (fun π _ => ?_); rw [Finset.sum_ite_eq]; simp
      _ = ∑ c : Fin (d + 1), ∑ π : Perm (Fin (d + 1)), if π 0 = c then
          S Δ b (d + 1) (doorT (d + 1) L (rot π) (Fin.last (d + 1)) (upd c.val (Syn.var 0))) else 0 :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun c _ => by
          show _ = Q.mk Δ (Syn.subst ![b] (gs 0 (d + 1) (comp (Hc (L := L) d c) (upd c.val (Syn.var 0)))))
          rw [hHc, mk_gs_ftsum]
          exact Finset.sum_congr rfl (fun π _ => (S_ite Δ b (d + 1) _ _).symm))
  -- the last facets
  have hlast : ∑ c : Fin (d + 1), S Δ b (d + 1) (Hc (L := L) d c) = Dt d L Δ b (Fin.last (d + 1)) := by
    have e : ∀ c : Fin (d + 1), S Δ b (d + 1) (Hc (L := L) d c) = ∑ π : Perm (Fin (d + 1)),
        if π 0 = c then S Δ b (d + 1) (doorT (d + 1) L (rot π) (Fin.last (d + 1)) (Syn.var 0)) else 0 := by
      intro c
      show Q.mk Δ (Syn.subst ![b] (gs 0 (d + 1) (ftsum _))) = _
      rw [mk_gs_ftsum]
      exact Finset.sum_congr rfl (fun π _ => S_ite Δ b (d + 1) _ _)
    rw [Finset.sum_congr rfl (fun c _ => e c), Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    show _ = ∑ π : Perm (Fin (d + 1)), S Δ b (d + 1) (doorT (d + 1) L π (Fin.last (d + 1)) (Syn.var 0))
    exact Fintype.sum_equiv (Equiv.mulRight (finRotate (d + 1))) _ _ (fun π => rfl)
  -- telescoping along each entry
  have htel : ∀ c : Fin (d + 1), S Δ b (d + 1) (comp (Hc (L := L) d c) (upd c.val (Syn.var 0))) +
      Q.mk Δ (Syn.subst ![b] (gs 0 (d - c.val) (face0 (Hc (L := L) d c) (d - c.val) c.val))) =
      Q.mk Δ (Syn.subst ![b] (gs 0 (d - c.val) (faceN (Hc (L := L) d c) (d - c.val) c.val))) +
        S Δ b (d + 1) (Hc (L := L) d c) := by
    intro c
    have e := grid_telescope (Hc (L := L) d c) (d - c.val) c.val Δ b
    rw [show d - c.val + (c.val + 1) = d + 1 by omega] at e
    simpa only [Q.mk_add] using Q.sound e
  -- the upper faces vanish (`eq:upper`)
  have hN : ∀ c : Fin (d + 1),
      Q.mk Δ (Syn.subst ![b] (gs 0 (d - c.val) (faceN (Hc (L := L) d c) (d - c.val) c.val))) = 0 := by
    intro c
    rw [← Q.mk_zero]
    refine Q.sound (faceN_gen (P := Facts (d + 1) L (some (d - c.val, true))) (d - c.val) c.val
      (facts_steps _ 0 (d - c.val) (fun e _ he top h => by cases h; omega))
      (facts_steps _ (d - c.val + 1) (d - c.val + 1 + c.val) (fun e he _ top h => by cases h; omega))
      (fun m' Δ' x' hx => facts_face (d - c.val) true hx)
      (fun m' Δ' y hy => ?_) Δ b (facts_base _ h))
    rw [show d - c.val + 1 + c.val = d + 1 by omega] at hy
    obtain ⟨b', hH, htl, hq⟩ := hy
    exact face_door_zero c true htl hq ⟨d - c.val, by omega⟩ (fun v h₁ h₂ hp => by
      have r := up_at (hH.2.2 c.val c.isLt) h₁ h₂ hp
      rwa [show d + 1 - 1 - c.val = d - c.val by omega] at r)
  -- the lower faces vanish except the one of the top entry (`eq:lower`)
  have h0 : ∀ c : Fin (d + 1), c ≠ 0 →
      Q.mk Δ (Syn.subst ![b] (gs 0 (d - c.val) (face0 (Hc (L := L) d c) (d - c.val) c.val))) = 0 := by
    intro c hc0
    have hc1 : 0 < c.val := Nat.pos_of_ne_zero (fun h => hc0 (Fin.ext h))
    rw [← Q.mk_zero]
    refine Q.sound (face0_gen (P := Facts (d + 1) L (some (d - c.val, false))) (d - c.val) c.val
      (facts_steps _ 0 (d - c.val) (fun e _ he top h => by cases h; omega))
      (facts_steps _ (d - c.val + 1) (d - c.val + 1 + c.val) (fun e he _ top h => by cases h; omega))
      (fun m' Δ' x' hx => facts_face (d - c.val) false hx)
      (fun m' Δ' y hy => ?_) Δ b (facts_base _ h))
    rw [show d - c.val + 1 + c.val = d + 1 by omega] at hy
    obtain ⟨b', hH, htl, hq⟩ := hy
    exact face_door_zero c false htl hq ⟨d, by omega⟩ (fun v h₁ h₂ hp =>
      eqb_zero_of_le (low_at (hH.2.1 c.val c.isLt) h₁ h₂ hp) (show d + 1 - 1 - c.val < d by omega))
  -- the lower face of the top entry is the full count one dimension down
  have hY : Q.mk Δ (Syn.subst ![b] (gs 0 (d - (0 : Fin (d + 1)).val)
      (face0 (Hc (L := L) d 0) (d - (0 : Fin (d + 1)).val) (0 : Fin (d + 1)).val))) =
      Q.mk Δ (count d (restrict L) b) := by
    simp only [Fin.val_zero, Nat.sub_zero]
    refine Q.sound (face0_congr_gen (P := fun _ _ _ _ => True) d (fun _ _ _ _ _ _ _ => trivial)
      (fun m' Δ' x' _ => ?_) Δ b trivial)
    rw [subst_Hc]
    simp only [fullS, subst_ftsum, subst_fullT, Syn.subst_var, Matrix.cons_val_zero]
    apply of_mk
    rw [mk_ftsum, mk_ftsum, ← (Perm.decomposeFin (n := d)).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Perm.decomposeFin_symm_apply_zero]
    rw [Finset.sum_eq_single (0 : Fin (d + 1))
      (fun p _ hp => Finset.sum_eq_zero (fun τ _ => by rw [if_neg hp, Q.mk_zero])) (by simp)]
    exact Finset.sum_congr rfl (fun τ _ => by rw [if_pos rfl]; exact Q.sound (face_full τ x'))
  -- assembling the double count
  have hends : Dt d L Δ b 0 + Q.mk Δ (count d (restrict L) b) = Dt d L Δ b (Fin.last (d + 1)) := by
    rw [hfirst, ← hlast, ← hY]
    have e := Finset.sum_congr rfl (fun c (_ : c ∈ (Finset.univ : Finset (Fin (d + 1)))) => htel c)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_eq_single (0 : Fin (d + 1)) (fun c _ hc => h0 c hc) (by simp),
      Finset.sum_eq_zero (fun c _ => hN c), _root_.zero_add] at e
    exact e
  choose X hX using hint
  have hsplit : ∑ t, Dt d L Δ b t = Dt d L Δ b 0 + Dt d L Δ b (Fin.last (d + 1)) + ∑ i : Fin d, (X i + X i) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.succ_last, hX]
    ring
  have hFu : Q.mk Δ (count (d + 1) L b) = Fu d L Δ b := by
    show Q.mk Δ (Syn.subst ![b] (gs 0 (d + 1) (ftsum _))) = _
    rw [mk_gs_ftsum]; rfl
  have key : Q.mk Δ (count (d + 1) L b) + 2 * (Dt d L Δ b (Fin.last (d + 1)) + ∑ i : Fin d, X i) =
      Q.mk Δ (count d (restrict L) b) + 2 * Ev d L Δ b := by
    rw [hFu, ← hcell, hsplit, ← hends, Finset.sum_add_distrib]; ring
  -- back to iPRA
  obtain ⟨tW, hW⟩ : ∃ t, Q.mk Δ t = Dt d L Δ b (Fin.last (d + 1)) + ∑ i : Fin d, X i :=
    Q.ind (motive := fun q => ∃ t, Q.mk Δ t = q) (fun t => ⟨t, rfl⟩) _
  obtain ⟨tE, hE⟩ : ∃ t, Q.mk Δ t = Ev d L Δ b :=
    Q.ind (motive := fun q => ∃ t, Q.mk Δ t = q) (fun t => ⟨t, rfl⟩) _
  have eq : Δ ⊢[PRAAx] count (d + 1) L b + two * tW ≐ count d (restrict L) b + two * tE := by
    apply of_mk
    rw [Q.mk_add, Q.mk_add, Q.mk_mul, Q.mk_mul, mk_two, hW, hE]
    exact key
  exact par_replacement eq (par_double tW)

/-! ## The theorem -/

/-- `par 1 = 1`. -/
theorem par_one' {Γ : List (Fm PTm n)} : Γ ⊢[PRAAx] par (one : PTm n) ≐ one :=
  (par_succ zero).eqTrans ((congrMonus (.eqRefl _) par_zero).eqTrans (monus_zero _))

/-- Dimension zero: the single vertex is full. -/
theorem base {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m) (h : Hyps 0 L Δ b) :
    Δ ⊢[PRAAx] par (count 0 L b) ≐ one := by
  have hr : Δ ⊢[PRAAx] le (col L b) (num 0) :=
    range_at h.1 (.eqRefl _) (fsum_eq_zero (fun q => q.elim0))
  have hf : ∀ π : Perm (Fin 0), Δ ⊢[PRAAx] fullT 0 L π b ≐ one := by
    intro π
    have e := Foundations.BoundedDecision.bounded_decide 0 (exactPat 1) one
      (fun ρ hρ => by
        have h0 : ρ 0 = 0 := by have := hρ 0; omega
        rw [ev_exactPat]
        simp only [exactV, cntV, Fin.prod_univ_one, Fin.sum_univ_one, Fin.val_zero, h0]
        simp)
      (cols 0 L π b) (fun s => by fin_cases s; exact hr)
    simpa [fullT] using e
  have hc : Δ ⊢[PRAAx] count 0 L b ≐ one := by
    apply of_mk
    show Q.mk Δ (Syn.subst ![b] (ftsum (fun π : Perm (Fin 0) => fullT 0 L π (Syn.var 0)))) = _
    rw [subst_ftsum, mk_ftsum, Fintype.sum_unique]
    simp only [subst_fullT, Syn.subst_var, Matrix.cons_val_zero]
    exact Q.sound (hf _)
  exact (congrAp1 parF hc).eqTrans par_one'

/-- `thm:sperner`: an admissible labelling has an odd number of full Kuhn simplices. -/
theorem sperner_parity : ∀ (d : ℕ) (L : PTm 1) {m : ℕ} (Δ : List (Fm PTm m)) (b : PTm m),
    Hyps d L Δ b → (Δ ⊢[PRAAx] par (count d L b) ≐ one)
  | 0, _, _, Δ, b, h => base Δ b h
  | d + 1, L, _, Δ, b, h =>
    (step d L Δ b h).eqTrans (sperner_parity d (restrict L) Δ b (hyps_face h))

/-! ## The closed sentence -/

/-- `ψ₁ ⟶ ⋯ ⟶ ψ_k ⟶ φ`. -/
def impAll {m : ℕ} : List (Fm PTm m) → Fm PTm m → Fm PTm m
  | [], φ => φ
  | ψ :: l, φ => ψ ⟶ impAll l φ

theorem impAll_intro {m : ℕ} :
    ∀ (l : List (Fm PTm m)) (Γ : List (Fm PTm m)) (φ : Fm PTm m), ((l.reverse ++ Γ) ⊢[PRAAx] φ) →
      (Γ ⊢[PRAAx] impAll l φ)
  | [], _, _, h => by simpa [impAll] using h
  | ψ :: l, Γ, φ, h => .impI (impAll_intro l (ψ :: Γ) φ (by simpa using h))

variable (d L)

/-- The base `⟨N, p⟩` with `N = var 0`, `p = var 1`. -/
abbrev base2 : PTm 2 := pairT (Syn.var 0) (Syn.var 1)

/-- The admissibility hypotheses at the base `⟨N, p⟩`. -/
def hyps2 : List (Fm PTm 2) :=
  hRange d L base2 :: (List.ofFn (fun j : Fin d => hLow d L j.val base2) ++
    List.ofFn (fun j : Fin d => hUp d L j.val base2))

/-- `∀ N p. admissible ⟶ par (#full Kuhn simplices) = 1`. -/
noncomputable def spernerFormula : Fm PTm 2 := impAll (hyps2 d L) (par (count d L base2) ≐ one)

theorem hyps2_hyps : Hyps d L ((hyps2 d L).reverse ++ []) base2 := by
  refine ⟨.hyp (by simp [hyps2]), fun j hj => .hyp ?_, fun j hj => .hyp ?_⟩
  · simp only [hyps2, List.append_nil, List.mem_reverse, List.mem_cons, List.mem_append, List.mem_ofFn]
    exact Or.inr (Or.inl ⟨⟨j, hj⟩, rfl⟩)
  · simp only [hyps2, List.append_nil, List.mem_reverse, List.mem_cons, List.mem_append, List.mem_ofFn]
    exact Or.inr (Or.inr ⟨⟨j, hj⟩, rfl⟩)

/-- `thm:sperner` as a closed sentence of iPRA, for every dimension `d` and labelling `L`. -/
theorem sperner_cube : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (spernerFormula d L) :=
  closeUniv 2 (impAll_intro _ _ _ (sperner_parity d L _ _ (hyps2_hyps d L)))

end LeanProofs.IPRA.Topology.SpernerCube
