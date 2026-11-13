import ConciseIPRA.NativeOneIntro
import ConciseIPRA.NativeTemplateFree
import ConciseIPRA.NativeMirror

/-!
# Elimination by abstraction

`APrf` is the calculus `A₇` of the article (`kern:def:A7`, from the package
`abstraction_and_refinements`): the kernel with transport replaced by
backward replacement and `QE` replaced by elimination by abstraction, and with
the single introduction of `WPrf`.  Its seven rules are hypothesis, the two
computation equations, and

* `bRep`: from `s = t` and `Rep_t^s(u) = r` infer `r = u`, where `Rep_t^s`
  replaces every occurrence of `t` by `s`, root first and in one pass;
* `aqE`: from `Q_y Rep_t^y(A)` and `Rep_t^0(A)` infer `A`: the matrix is the
  abstraction of every occurrence of `t` in the conclusion;
* `dE` and the single introduction `dI` of `WPrf`.

No rule is given a template or a matrix.  `aprf_iff_nprf` proves that `APrf`
derives the same sequents as the kernel.

* Replacement and abstraction are one operation, `Tm.rpl t v σ`, which puts
  `v` at the occurrences of `t` and applies `σ` to the other variables.  Its
  tests look at the source term only, so it commutes with substitution into
  `v` and `σ` (`Tm.rpl_comp`), which gives the two identities of the
  abstraction, and an injective renaming of the source can be moved into `σ`
  (`Tm.rpl_ren`), which gives renaming of derivations.
* Soundness: `bRep` is transport (`NPrf.repEq`), `aqE` is `QE` at the
  abstracted matrix, and `dI` is `NPrf.ofDI`.
* Completeness follows the article: equality and transport in a term template
  from the first computation equation and `bRep` with a marker; closure by
  cases at a witness that is not the literal `0`; then transport in a formula
  template and the ordinary `QE`, together by induction on the number of
  binders: `QE` is `aqE` at the marker of the matrix followed by transport
  along the computation `marker = t`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m k : ℕ}

namespace Tm

open Classical

/-- Replacement with a renaming: every occurrence of `t`, root first and in
one pass, becomes `v`; every other variable `i` becomes `σ i`. -/
noncomputable def rpl : {n m : ℕ} → Tm n → Tm m → (Fin n → Tm m) → Tm n → Tm m
  | _, _, t, v, σ, .var i => if Tm.var i = t then v else σ i
  | _, _, t, v, _, .zero => if Tm.zero = t then v else .zero
  | _, _, t, v, σ, .succ a => if Tm.succ a = t then v else .succ (rpl t v σ a)
  | _, _, t, v, σ, .iter c a h =>
    if Tm.iter c a h = t then v
    else .iter (rpl t v σ c) (rpl t v σ a) (rpl (Syn.shift t) (Syn.shift v) (Syn.up σ) h)

/-- Substitution into the inserted term and the renaming commutes with the
replacement. -/
theorem rpl_comp (a : Tm n) : ∀ {m k : ℕ} (t : Tm n) (v : Tm m) (σ : Fin n → Tm m)
    (τ : Fin m → Tm k),
    Syn.subst τ (rpl t v σ a) = rpl t (Syn.subst τ v) (fun i => Syn.subst τ (σ i)) a := by
  induction a with intro m k t v σ τ
  | var i => simp only [rpl]; split <;> rfl
  | zero => simp only [rpl]; split <;> rfl
  | succ a ih => simp only [rpl]; split; · rfl
                 · rw [Tm.subst_succ, ih]
  | iter c a h ihc iha ihh =>
    simp only [rpl]; split
    · rfl
    · rw [Tm.subst_iter, ihc, iha, ihh, Syn.subst_up_shift, Syn.up_comp]

/-- Replacing `t` by itself changes nothing. -/
theorem rpl_self (a : Tm n) : ∀ (t : Tm n), rpl t t Syn.var a = a := by
  induction a with intro t
  | var i => simp only [rpl]; split <;> simp_all
  | zero => simp only [rpl]; split <;> simp_all
  | succ a ih => simp only [rpl]; split; · simp_all
                 · rw [ih]
  | iter c a h ihc iha ihh =>
    simp only [rpl]; split
    · simp_all
    · rw [ihc, iha, Syn.up_var, ihh]

/-- An injective renaming of the source moves into the renaming. -/
theorem rpl_ren (a : Tm n) : ∀ {m k : ℕ} {ξ : Fin n → Fin m}, Function.Injective ξ →
    ∀ (t : Tm n) (v : Tm k) (σ : Fin m → Tm k),
    rpl (ren ξ t) v σ (ren ξ a) = rpl t v (fun i => σ (ξ i)) a := by
  induction a with intro m k ξ hξ t v σ
  | var i =>
    show rpl _ v σ (Tm.var (ξ i)) = _
    simp only [rpl]
    by_cases e : Tm.var i = t
    · rw [if_pos (by rw [← e]; rfl), if_pos e]
    · rw [if_neg (fun e' => e (ren_inj _ hξ t (by rw [← e']; rfl))), if_neg e]
  | zero =>
    show rpl _ v σ Tm.zero = _
    simp only [rpl]
    by_cases e : Tm.zero = t
    · rw [if_pos (by rw [← e]; rfl), if_pos e]
    · rw [if_neg (fun e' => e (ren_inj _ hξ t (by rw [← e']; rfl))), if_neg e]
  | succ a ih =>
    show rpl _ v σ (Tm.succ (ren ξ a)) = _
    simp only [rpl]
    by_cases e : Tm.succ a = t
    · rw [if_pos (by rw [← e]; rfl), if_pos e]
    · rw [if_neg (fun e' => e (ren_inj _ hξ t (by rw [← e']; rfl))), if_neg e, ih hξ]
  | iter c a h ihc iha ihh =>
    show rpl _ v σ (Tm.iter (ren ξ c) (ren ξ a) (ren (upRen ξ) h)) = _
    simp only [rpl]
    by_cases e : Tm.iter c a h = t
    · rw [if_pos (by rw [← e]; rfl), if_pos e]
    · rw [if_neg (fun e' => e (ren_inj _ hξ t (by rw [← e']; rfl))), if_neg e, ihc hξ,
        iha hξ]
      have hs : Syn.shift (ren ξ t) = ren (upRen ξ) (Syn.shift t) := by
        rw [shift_eq_ren, shift_eq_ren, ren_ren, ren_ren]; rfl
      rw [hs, ihh (upRen_inj hξ)]
      congr 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The substitution `σm` puts the marker `M` or a variable at every index. -/
def Marked (M : Tm n) (σm : Fin k → Tm n) : Prop := ∀ i, σm i = M ∨ ∃ j, σm i = Tm.var j

theorem Marked.up {M : Tm n} {σm : Fin k → Tm n} (h : Marked M σm) :
    Marked (Syn.shift M) (Syn.up σm) := by
  refine Fin.cases (.inr ⟨0, rfl⟩) fun j => ?_
  rcases h j with e | ⟨j', e⟩
  · exact .inl (by rw [Syn.up_succ, e])
  · exact .inr ⟨j'.succ, by rw [Syn.up_succ, e]; rfl⟩

theorem sz_subst_marked (h : Tm k) : ∀ {n : ℕ} {M : Tm n} {σm : Fin k → Tm n},
    Marked M σm → sz (Syn.subst σm h) = sz h ∨ sz M ≤ sz (Syn.subst σm h) := by
  induction h with
  | var i =>
    intro n M σm hσ
    rcases hσ i with e | ⟨j, e⟩
    · right; show sz M ≤ sz (σm i); rw [e]
    · left; show sz (σm i) = 1; rw [e]; rfl
  | zero => intro n M σm _; exact .inl rfl
  | succ a ih =>
    intro n M σm hσ
    rcases ih hσ with e | e
    · left; show sz (Syn.subst σm a) + 1 = sz a + 1; rw [e]
    · right; show sz M ≤ sz (Syn.subst σm a) + 1; omega
  | iter c a b ihc iha ihb =>
    intro n M σm hσ
    rw [Tm.subst_iter]
    have hb := ihb hσ.up
    rw [sz_shift] at hb
    rcases ihc hσ with ec | ec <;> rcases iha hσ with ea | ea <;> rcases hb with eb | eb
    all_goals first | (left; simp only [sz]; omega) | (right; simp only [sz]; omega)

/-- `σs` is `σm` with the marker replaced by `S` and the variables renamed by `ρ`. -/
def Marks' (M : Tm n) (S : Tm m) (ρ : Fin n → Tm m) (σm : Fin k → Tm n)
    (σs : Fin k → Tm m) : Prop :=
  ∀ i, (σm i = M ∧ σs i = S) ∨ ∃ j, σm i = Tm.var j ∧ σs i = ρ j

theorem Marks'.marked {M : Tm n} {S : Tm m} {ρ : Fin n → Tm m} {σm : Fin k → Tm n}
    {σs : Fin k → Tm m} (h : Marks' M S ρ σm σs) : Marked M σm := fun i =>
  (h i).imp (fun e => e.1) (fun ⟨j, e, _⟩ => ⟨j, e⟩)

theorem Marks'.up {M : Tm n} {S : Tm m} {ρ : Fin n → Tm m} {σm : Fin k → Tm n}
    {σs : Fin k → Tm m} (h : Marks' M S ρ σm σs) :
    Marks' (Syn.shift M) (Syn.shift S) (Syn.up ρ) (Syn.up σm) (Syn.up σs) := by
  refine Fin.cases (.inr ⟨0, rfl, rfl⟩) fun j => ?_
  rcases h j with ⟨e₁, e₂⟩ | ⟨j', e₁, e₂⟩
  · exact .inl ⟨by rw [Syn.up_succ, e₁], by rw [Syn.up_succ, e₂]⟩
  · exact .inr ⟨j'.succ, by rw [Syn.up_succ, e₁]; rfl, by rw [Syn.up_succ, e₂, Syn.up_succ]⟩

/-- Replacing a large marker in an instance of a term replaces exactly the
marked variables. -/
theorem rpl_subst (h : Tm k) : ∀ {n m : ℕ} {M : Tm n} {S : Tm m} {ρ : Fin n → Tm m}
    {σm : Fin k → Tm n} {σs : Fin k → Tm m},
    Big (sz h) M → Marks' M S ρ σm σs → rpl M S ρ (Syn.subst σm h) = Syn.subst σs h := by
  induction h with
  | var i =>
    intro n m M S ρ σm σs hM hσ
    show rpl M S ρ (σm i) = σs i
    rcases hσ i with ⟨e₁, e₂⟩ | ⟨j, e₁, e₂⟩
    · rw [e₁, e₂]
      obtain ⟨c, a, K, rfl, _⟩ := hM
      simp only [rpl, if_true]
    · obtain ⟨c, a, K, rfl, _⟩ := hM
      rw [e₁, e₂]; simp only [rpl]; rw [if_neg (by intro e; cases e)]
  | zero =>
    intro n m M S ρ σm σs hM _
    obtain ⟨c, a, K, rfl, _⟩ := hM
    show rpl _ S ρ Tm.zero = Tm.zero
    simp only [rpl]; rw [if_neg (by intro e; cases e)]
  | succ a ih =>
    intro n m M S ρ σm σs hM hσ
    have iha := ih (hM.mono (by simp only [sz]; omega)) hσ
    obtain ⟨c, a', K, rfl, _⟩ := hM
    show rpl _ S ρ (Tm.succ (Syn.subst σm a)) = Tm.succ (Syn.subst σs a)
    simp only [rpl]; rw [if_neg (by intro e; cases e), iha]
  | iter c a b ihc iha ihb =>
    intro n m M S ρ σm σs hM hσ
    have hc := ihc (hM.mono (by simp only [sz]; omega)) hσ
    have ha := iha (hM.mono (by simp only [sz]; omega)) hσ
    have hb := ihb (hM.shift.mono (by simp only [sz]; omega)) hσ.up
    have hne : Tm.iter (Syn.subst σm c) (Syn.subst σm a) (Syn.subst (Syn.up σm) b) ≠ M := by
      obtain ⟨c₀, a₀, K, rfl, hK⟩ := hM
      intro e
      have eb := (Tm.iter.inj e).2.2
      simp only [sz] at hK
      rcases sz_subst_marked b hσ.marked.up with e' | e'
      · rw [eb] at e'; omega
      · rw [eb, sz_shift] at e'; simp only [sz] at e'; omega
    rw [Tm.subst_iter, Tm.subst_iter]; simp only [rpl]; rw [if_neg hne, hc, ha, hb]

theorem subst_var_ren (ξ : Fin n → Fin m) (a : Tm n) :
    Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) a = ren ξ a := (ren_eq_sub a ξ).symm

end Tm

namespace NFm

/-- Replacement with a renaming in a native formula: in every term, below the
binders the replaced term, the inserted term and the renaming are weakened. -/
noncomputable def rpl : {n m : ℕ} → Tm n → Tm m → (Fin n → Tm m) → NFm n → NFm m
  | _, _, t, v, σ, .eq a b => .eq (Tm.rpl t v σ a) (Tm.rpl t v σ b)
  | _, _, t, v, σ, .Q B => .Q (rpl (Syn.shift t) (Syn.shift v) (Syn.up σ) B)
  | _, _, t, v, σ, .D B =>
    .D (rpl (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift v)) (Syn.up (Syn.up σ)) B)

theorem rpl_comp (A : NFm n) : ∀ {m k : ℕ} (t : Tm n) (v : Tm m) (σ : Fin n → Tm m)
    (τ : Fin m → Tm k),
    (rpl t v σ A).subst τ = rpl t (Syn.subst τ v) (fun i => Syn.subst τ (σ i)) A := by
  induction A with intro m k t v σ τ
  | eq a b => simp only [rpl, subst_eq, Tm.rpl_comp]
  | Q B ih => simp only [rpl, subst_Q, ih, Syn.subst_up_shift, Syn.up_comp]
  | D B ih => simp only [rpl, subst_D, ih, Syn.subst_up_shift, Syn.up_comp]

theorem rpl_self (A : NFm n) : ∀ (t : Tm n), rpl t t Syn.var A = A := by
  induction A with intro t
  | eq a b => simp only [rpl, Tm.rpl_self]
  | Q B ih => simp only [rpl, Syn.up_var, ih]
  | D B ih => simp only [rpl, Syn.up_var, ih]

/-- An injective renaming of the source moves into the renaming. -/
theorem rpl_ren (A : NFm n) : ∀ {m k : ℕ} {ξ : Fin n → Fin m}, Function.Injective ξ →
    ∀ (t : Tm n) (v : Tm k) (σ : Fin m → Tm k),
    rpl (Tm.ren ξ t) v σ (A.subst fun i => Syn.var (ξ i)) = rpl t v (fun i => σ (ξ i)) A := by
  induction A with intro m k ξ hξ t v σ
  | eq a b =>
    simp only [subst_eq, rpl, Tm.subst_var_ren, Tm.rpl_ren _ hξ]
  | Q B ih =>
    have hs : Syn.shift (Tm.ren ξ t) = Tm.ren (Tm.upRen ξ) (Syn.shift t) := by
      rw [Tm.shift_eq_ren, Tm.shift_eq_ren, Tm.ren_ren, Tm.ren_ren]; rfl
    have hu : (fun i => Syn.var (Tm.upRen ξ i) : Fin _ → Tm _) = Syn.up fun i => Syn.var (ξ i) :=
      (Tm.up_rn ξ).symm
    simp only [subst_Q, rpl, hs, ← hu, ih (Tm.upRen_inj hξ)]
    congr 2; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  | D B ih =>
    have hs : Syn.shift (Syn.shift (Tm.ren ξ t))
        = Tm.ren (Tm.upRen (Tm.upRen ξ)) (Syn.shift (Syn.shift t)) := by
      simp only [Tm.shift_eq_ren, Tm.ren_ren]; rfl
    have hu : (fun i => Syn.var (Tm.upRen (Tm.upRen ξ) i) : Fin _ → Tm _)
        = Syn.up (Syn.up fun i => Syn.var (ξ i)) := by rw [Tm.up_rn, Tm.up_rn]
    simp only [subst_D, rpl, hs, ← hu, ih (Tm.upRen_inj (Tm.upRen_inj hξ))]
    congr 2; funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;> rfl

/-- The number of term nodes of a formula. -/
def sz : {n : ℕ} → NFm n → ℕ
  | _, .eq a b => Tm.sz a + Tm.sz b
  | _, .Q B => sz B
  | _, .D B => sz B

/-- Replacing a large marker in an instance of a formula replaces exactly the
marked variables. -/
theorem rpl_subst (B : NFm k) : ∀ {n m : ℕ} {M : Tm n} {S : Tm m} {ρ : Fin n → Tm m}
    {σm : Fin k → Tm n} {σs : Fin k → Tm m},
    Tm.Big (sz B) M → Tm.Marks' M S ρ σm σs → rpl M S ρ (B.subst σm) = B.subst σs := by
  induction B with
  | eq a b =>
    intro n m M S ρ σm σs hM hσ
    simp only [subst_eq, rpl]
    rw [Tm.rpl_subst a (hM.mono (by simp only [sz]; omega)) hσ,
      Tm.rpl_subst b (hM.mono (by simp only [sz]; omega)) hσ]
  | Q B ih =>
    intro n m M S ρ σm σs hM hσ
    simp only [subst_Q, rpl]
    rw [ih hM.shift hσ.up]
  | D B ih =>
    intro n m M S ρ σm σs hM hσ
    simp only [subst_D, rpl]
    rw [ih hM.shift.shift hσ.up.up]

/-- `Rep_t^x(A)`: every occurrence of `t` in `A` replaced by `x`. -/
noncomputable def rep (t x : Tm n) (A : NFm n) : NFm n := rpl t x Syn.var A

/-- `Rep_t^y(A)`: the abstraction of every occurrence of `t` in `A` to the new
variable `y`. -/
noncomputable def abs (t : Tm n) (A : NFm n) : NFm (n + 1) :=
  rpl t (Syn.var 0) (fun i => Syn.var i.succ) A

/-- The abstraction instantiated is the replacement. -/
theorem abs_inst (t u : Tm n) (A : NFm n) : (abs t A).subst (inst u) = rep t u A := by
  rw [abs, rpl_comp, rep]
  congr 1

/-- The abstraction instantiated at the abstracted term is the formula. -/
theorem abs_inst_self (t : Tm n) (A : NFm n) : (abs t A).subst (inst t) = A := by
  rw [abs_inst, rep, rpl_self]

/-- The marker of a matrix with the seed `t`: `I(0, t; u.K)` with `K` larger
than the matrix. -/
def mark (B : NFm (n + 1)) (t : Tm n) : Tm n := .iter .zero t (Tm.big (sz B))

theorem big_mark (B : NFm (n + 1)) (t : Tm n) : Tm.Big (sz B) (mark B t) :=
  ⟨_, _, _, rfl, by rw [Tm.sz_big]; omega⟩

/-- Abstracting the marker in the marked instance gives the matrix back. -/
theorem abs_mark (B : NFm (n + 1)) (t : Tm n) : abs (mark B t) (B.subst (inst (mark B t))) = B := by
  rw [abs, rpl_subst B (big_mark B t) (σs := Syn.var), subst_id]
  refine Fin.cases (.inl ⟨rfl, rfl⟩) fun j => .inr ⟨j, by simp, rfl⟩

/-- Replacing the marker in the marked instance by `x` gives the instance at `x`. -/
theorem rep_mark (B : NFm (n + 1)) (t x : Tm n) :
    rep (mark B t) x (B.subst (inst (mark B t))) = B.subst (inst x) := by
  rw [rep, rpl_subst B (big_mark B t)]
  refine Fin.cases (.inl ⟨rfl, rfl⟩) fun j => .inr ⟨j, by simp, by simp⟩

end NFm

namespace Tm

theorem rpl_var_eq_rep (t s u : Tm n) : rpl t s Syn.var u = rep t s u := by
  induction u with
  | var i => simp only [rpl, rep_var]; rfl
  | zero => simp only [rpl, rep_zero]
  | succ a ih => simp only [rpl, rep_succ, ih]
  | iter c a h ihc iha ihh => simp only [rpl, rep_iter, ihc, iha, Syn.up_var, ihh]

theorem rpl_root (t : Tm n) (v : Tm m) (σ : Fin n → Tm m) : rpl t v σ t = v := by
  cases t <;> simp [rpl]

/-- Replacing the marker of a term template in its marked instance. -/
theorem rpl_marker (h : Tm (n + 1)) (s x : Tm n) :
    rpl (marker h s) x Syn.var (Syn.subst (inst (marker h s)) h) = Syn.subst (inst x) h :=
  rpl_subst h ⟨_, _, _, rfl, by rw [sz_big]; omega⟩ fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨j, by simp, by simp⟩

end Tm

/-- Derivability in the calculus `A₇`. -/
inductive APrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : APrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      APrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      APrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- BRep: from `s = t` and `Rep_t^s(u) = r` infer `r = u`. -/
  | bRep {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n} (h₁ : APrf Γ (.eq s t))
      (h₂ : APrf Γ (.eq (Tm.rpl t s Syn.var u) r)) : APrf Γ (.eq r u)
  /-- AQE: from `Q_y Rep_t^y(A)` and `Rep_t^0(A)` infer `A`. -/
  | aqE {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (t : Tm n) (h₁ : APrf Γ (.Q (NFm.abs t A)))
      (h₂ : APrf Γ (NFm.rep t zero A)) : APrf Γ A
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : APrf Γ (.D B)) (h₂ : APrf (.Q B :: Γ.map NFm.shift) A.shift) : APrf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : APrf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      APrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

/-! ### Soundness -/

theorem APrf.toNPrf (h : APrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | @bRep _ _ s t u r _ _ ih₁ ih₂ =>
    rw [Tm.rpl_var_eq_rep] at ih₂
    exact NPrf.eqSymm (NPrf.eqTrans (NPrf.repEq u (NPrf.eqSymm ih₁)) ih₂)
  | @aqE _ _ A t _ _ ih₁ ih₂ =>
    rw [← NFm.abs_inst] at ih₂
    have h := NPrf.qE t ih₁ ih₂
    rwa [NFm.abs_inst_self] at h
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDI B t ih

namespace APrf

/-! ### Equality from the first computation and backward replacement -/

/-- Joining: from `s = t` and `s = r` infer `r = t`. -/
theorem join {s t r : Tm n} (h₁ : APrf Γ (.eq s t)) (h₂ : APrf Γ (.eq s r)) :
    APrf Γ (.eq r t) :=
  .bRep h₁ (by rwa [Tm.rpl_root])

theorem eqRefl (a : Tm n) : APrf Γ (.eq a a) :=
  join (.iterZero a zero) (.iterZero a zero)

theorem eqSymm {s t : Tm n} (h : APrf Γ (.eq s t)) : APrf Γ (.eq t s) := join (eqRefl s) h

theorem eqTrans {s t u : Tm n} (h₁ : APrf Γ (.eq s t)) (h₂ : APrf Γ (.eq t u)) :
    APrf Γ (.eq s u) :=
  join h₂ (eqSymm h₁)

/-- Congruence in a chosen template, by the marker. -/
theorem eqCongr (h : Tm (n + 1)) {s t : Tm n} (e : APrf Γ (.eq s t)) :
    APrf Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) := by
  have hK : APrf Γ (.eq (Tm.marker h s) s) := .iterZero s _
  have h₁ : APrf Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst (Tm.marker h s)) h)) :=
    .bRep (eqSymm hK) (by rw [Tm.rpl_marker]; exact eqRefl _)
  have h₂ : APrf Γ (.eq (Syn.subst (inst t) h) (Syn.subst (inst (Tm.marker h s)) h)) :=
    .bRep (eqSymm (eqTrans hK e)) (by rw [Tm.rpl_marker]; exact eqRefl _)
  exact eqTrans h₁ (eqSymm h₂)

/-- The kernel's transport. -/
theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (h₁ : APrf Γ (.eq s t))
    (h₂ : APrf Γ (.eq (Syn.subst (inst s) h) u)) : APrf Γ (.eq u (Syn.subst (inst t) h)) :=
  join (eqCongr h h₁) h₂

/-- Transport in an equation template. -/
theorem trEq (a b : Tm (n + 1)) {s t : Tm n} (h₁ : APrf Γ (.eq s t))
    (h₂ : APrf Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    APrf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  trOne b h₁ (trOne a h₁ h₂)

end APrf

/-! ### Injective renaming and weakening -/

theorem Tm.rpl_rn (t s u : Tm n) {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) :
    Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) (Tm.rpl t s Syn.var u)
      = Tm.rpl (Syn.subst (fun i => Syn.var (ξ i)) t) (Syn.subst (fun i => Syn.var (ξ i)) s)
        Syn.var (Syn.subst (fun i => Syn.var (ξ i)) u) := by
  rw [Tm.rpl_comp, Tm.subst_var_ren ξ t, Tm.subst_var_ren ξ u, Tm.rpl_ren u hξ]
  rfl

theorem NFm.abs_rn (t : Tm n) (A : NFm n) {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) :
    (abs t A).subst (up fun i => (Syn.var (ξ i) : Tm m))
      = abs (Syn.subst (fun i => Syn.var (ξ i)) t) (A.subst fun i => Syn.var (ξ i)) := by
  rw [abs, abs, rpl_comp, Tm.subst_var_ren ξ t, rpl_ren A hξ]
  congr 1

theorem NFm.rep_rn (t x : Tm n) (A : NFm n) {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) :
    (rep t x A).subst (fun i => (Syn.var (ξ i) : Tm m))
      = rep (Syn.subst (fun i => Syn.var (ξ i)) t) (Syn.subst (fun i => Syn.var (ξ i)) x)
        (A.subst fun i => Syn.var (ξ i)) := by
  rw [rep, rep, rpl_comp, Tm.subst_var_ren ξ t, rpl_ren A hξ]
  rfl

namespace APrf

theorem hyp0 : APrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : APrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → APrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | bRep _ _ ih₁ ih₂ => intro Δ s; exact .bRep (ih₁ s) (ih₂ s)
  | aqE t _ _ ih₁ ih₂ => intro Δ s; exact .aqE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dI B t _ ih =>
    intro Δ s
    exact .dI B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : APrf Γ A) : APrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Injective renaming of the free variables of a derivation. -/
theorem ren (h : APrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    APrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ _; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ _; exact .iterZero _ _
  | iterSucc c a h =>
    intro m ξ _
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | bRep _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_eq, Tm.rpl_rn _ _ _ hξ] at h₂
    exact .bRep (ih₁ ξ hξ) h₂
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

theorem shift (h : APrf Γ A) : APrf (Γ.map NFm.shift) A.shift :=
  h.ren Fin.succ (Fin.succ_injective _)

/-! ### Closure by cases, at a witness that is not the literal `0` -/

/-- `Q` by cases: from `B(0) ⊢ B(S z)` infer `Q_y B(y)`, for every matrix. -/
theorem qCases (B : NFm (n + 1))
    (h : APrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : APrf Γ (.Q B) := by
  have hD : APrf Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine .dI _ (iter zero zero zero) ?_
    rw [NFm.start_iter, NFm.subst_dummy_inst, ← NFm.shift_subst_inst_zero]
    exact h
  exact .dE hD hyp0

end APrf

/-! ### Transport and elimination by the number of binders -/

namespace NFm

/-- The number of binders `Q` and `D` of a formula. -/
def rk : {n : ℕ} → NFm n → ℕ
  | _, .eq _ _ => 0
  | _, .Q B => rk B + 1
  | _, .D B => rk B + 1

theorem rk_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m), (A.subst σ).rk = A.rk := by
  induction A with intro m σ
  | eq a b => rfl
  | Q B ih => simp only [subst_Q, rk, ih]
  | D B ih => simp only [subst_D, rk, ih]

end NFm

namespace APrf

/-- Transport in formula templates with at most `r` binders. -/
def Tr (r : ℕ) : Prop :=
  ∀ {n : ℕ} {Γ : List (NFm n)} (F : NFm (n + 1)) {s t : Tm n}, F.rk ≤ r →
    APrf Γ (.eq s t) → APrf Γ (F.subst (inst s)) → APrf Γ (F.subst (inst t))

/-- Elimination of closures whose matrix has at most `r` binders. -/
def El (r : ℕ) : Prop :=
  ∀ {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 1)) (t : Tm n), B.rk ≤ r →
    APrf Γ (.Q B) → APrf Γ (B.subst (inst zero)) → APrf Γ (B.subst (inst t))

/-- Elimination is `aqE` at the marker of the matrix followed by transport
along the computation `marker = t`. -/
theorem el_of_tr {r : ℕ} (hT : Tr r) : El r := by
  intro n Γ B t hr hQ h0
  have hK : APrf Γ (B.subst (inst (NFm.mark B t))) := by
    refine .aqE (NFm.mark B t) ?_ ?_
    · rw [NFm.abs_mark]; exact hQ
    · rw [NFm.rep_mark]; exact h0
  exact hT B hr (.iterZero t _) hK

/-- The step of a closure transported along `s = t`: from `B(t, 0)` to
`B(t, S z)`, through `B(s, 0)` and the closure `Q_y B(s, y)`. -/
theorem qStep {r : ℕ} (hT : Tr r) (hE : El r) {Θ : List (NFm m)} (G : NFm (m + 2))
    (hG : G.rk ≤ r) {s t : Tm m} (e : APrf Θ (.eq s t))
    (hQ : APrf Θ (.Q (G.subst (up (inst s))))) :
    APrf (((G.subst (up (inst t))).subst (inst zero)).shift :: Θ.map NFm.shift)
      ((G.subst (up (inst t))).subst (repl (succ (Syn.var 0)))) := by
  have e' : APrf (((G.subst (up (inst t))).subst (inst zero)).shift :: Θ.map NFm.shift)
      (.eq (Syn.shift s) (Syn.shift t)) := (APrf.shift e).wk
  have hQ' := (APrf.shift hQ).wk (B := ((G.subst (up (inst t))).subst (inst zero)).shift)
  -- the template of the instances at zero
  have i0 : ∀ x : Tm m, (G.subst (Fin.cases zero (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))).subst (inst (Syn.shift x))
      = ((G.subst (up (inst x))).subst (inst zero)).shift := by
    intro x
    simp only [NFm.shift, NFm.subst_subst]
    refine G.subst_ext fun i => ?_
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;> first | rfl | simp [Syn.shift, Syn.subst_subst]
  -- the template of the instances at `S z`
  have i1 : ∀ x : Tm m, (G.subst (Fin.cases (succ (Syn.var 1)) (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))).subst (inst (Syn.shift x))
      = (G.subst (up (inst x))).subst (repl (succ (Syn.var 0))) := by
    intro x
    simp only [NFm.subst_subst]
    refine G.subst_ext fun i => ?_
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i <;> first | rfl | simp [Syn.shift, Syn.subst_subst]
  have h1 : APrf (((G.subst (up (inst t))).subst (inst zero)).shift :: Θ.map NFm.shift)
      (((G.subst (up (inst s))).subst (up fun i => Syn.var i.succ)).subst (inst zero)) := by
    rw [NFm.subst_dummy_up_inst, ← NFm.shift_subst_inst_zero, ← i0 s]
    exact hT (G.subst (Fin.cases zero (Fin.cases (Syn.var 0) fun j => Syn.var j.succ.succ)))
      (by rw [NFm.rk_subst]; exact hG) (eqSymm e') (by rw [i0]; exact hyp0)
  have h2 := hE ((G.subst (up (inst s))).subst (up fun i => Syn.var i.succ)) (succ (Syn.var 0))
    (by rw [NFm.rk_subst, NFm.rk_subst]; exact hG) hQ' h1
  rw [NFm.subst_dummy_up_inst, ← i1] at h2
  have h3 := hT (G.subst (Fin.cases (succ (Syn.var 1)) (Fin.cases (Syn.var 0)
      fun j => Syn.var j.succ.succ))) (by rw [NFm.rk_subst]; exact hG) e' h2
  rwa [i1] at h3

/-- **Transport and elimination**, by induction on the number of binders. -/
theorem trEl : ∀ r, Tr r ∧ El r
  | 0 => by
    have hT : Tr 0 := by
      intro n Γ F s t hr e h
      match F, hr with
      | .eq a b, _ => exact trEq a b e h
    exact ⟨hT, el_of_tr hT⟩
  | r + 1 => by
    obtain ⟨hT, hE⟩ := trEl r
    have hT' : Tr (r + 1) := by
      intro n Γ F s t hr e h
      match F, hr with
      | .eq a b, _ => exact trEq a b e h
      | .Q B, hr =>
        exact qCases _ (qStep hT hE B (by simp only [NFm.rk] at hr; omega) e h)
      | .D B, hr =>
        refine .dE h ?_
        show APrf _ (.D ((B.subst (up (up (inst t)))).subst (up (up fun i => Syn.var i.succ))))
        refine .dI _ (Syn.var 0) ?_
        rw [NFm.start_of_not (fun h' => by cases h'.2)]
        -- the instance at the eigenvariable of the reintroduced closure is the matrix itself
        have hτ : ((B.subst (up (up (inst t)))).subst (up (up fun i => Syn.var i.succ))).subst
            (up (inst (Syn.var 0))) = B.subst (up (up (inst t))) := by
          rw [NFm.subst_subst _ (up (up fun i => Syn.var i.succ))]
          refine NFm.subst_eq_self _ fun i => ?_
          refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun q => ?_) j) i <;> simp
        rw [hτ]
        -- the matrix with the eigenvariable in the place of the witness, and a hole for `v`
        have gx : ∀ x : Tm n, (B.subst (Fin.cases (Syn.var 0) (Fin.cases
            (Syn.var (Fin.succ (Fin.succ 0))) (Fin.cases (Syn.var (Fin.succ 0))
              fun j => Syn.var j.succ.succ.succ)))).subst (up (inst (Syn.shift x)))
            = B.subst (up (up (inst x))) := by
          intro x
          simp only [NFm.subst_subst]
          refine B.subst_ext fun i => ?_
          refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => Fin.cases ?_ (fun q => ?_) l) j)
            i <;> simp only [Fin.cases_succ, Fin.cases_zero, Syn.up_succ, Syn.up_zero,
              Syn.inst_zero, Syn.inst_succ, Syn.subst_var]
          all_goals simp
        have hq := qStep hT hE (Θ := .Q (B.subst (up (up (inst s)))) :: Γ.map NFm.shift)
          (B.subst (Fin.cases (Syn.var 0) (Fin.cases (Syn.var (Fin.succ (Fin.succ 0)))
            (Fin.cases (Syn.var (Fin.succ 0)) fun j => Syn.var j.succ.succ.succ))))
          (by rw [NFm.rk_subst]; simp only [NFm.rk] at hr; omega)
          (by exact (APrf.shift e).wk : APrf _ (.eq (Syn.shift s) (Syn.shift t)))
          (by rw [gx]; exact hyp0)
        rw [gx, NFm.shift_subst_inst_zero] at hq
        exact hq
    exact ⟨hT', el_of_tr hT'⟩

/-- `QE` is a derived rule of `A₇`. -/
theorem qE {B : NFm (n + 1)} (t : Tm n) (h₁ : APrf Γ (.Q B)) (h₂ : APrf Γ (B.subst (inst zero))) :
    APrf Γ (B.subst (inst t)) :=
  (trEl B.rk).2 B t le_rfl h₁ h₂

end APrf

instance : WKernel @APrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun a b => APrf.trEq a b,
    fun t h₁ h₂ => APrf.qE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂, fun B t h => .dI B t h⟩

/-- Every rule of the kernel is a derived rule of `A₇`. -/
theorem NPrf.toAPrf (h : NPrf Γ A) : APrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact APrf.trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact APrf.qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact WKernel.dICase B t ih
  | qIInd s t _ ih => exact WKernel.qInd s t ih

/-- **Elimination by abstraction**: `A₇` and the kernel derive the same
sequents. -/
theorem aprf_iff_nprf : APrf Γ A ↔ NPrf Γ A := ⟨APrf.toNPrf, NPrf.toAPrf⟩

end LeanProofs.ConciseIPRA
